/* SwitchRecomp - Copyright 2026 MZ Labs
   Licensed under the GNU Affero General Public License v3.0, see LICENSE.txt and NOTICE.txt.
   Forks and derived works have to keep the credit to SwitchRecomp by MZ Labs and the startup screen. */
/* Switch 2 graphics services. A Switch 2 game reaches the GPU through ISelfController 2000 (GetGraphicsSupervisor),
   not through nvdrv: the supervisor (TIPC) bootstraps, creates native memory and images, and opens sessions for the
   GPU (address spaces, devices, a worker that maps GPU memory), syncpoints, display ("vi2") and an nvdrv session of
   its own (1402). Underneath it all is our nvdrv: its nvmap handles, GPU page table and channels.
   Requests are TIPC: W(c,0) is the header word (16 + command), W(c,1) the size word, the arguments follow. Results go
   back as the first payload word (the dispatch return value) */
#include "rt.h"

extern SvcObj* nvdrv_obj_new(const char* name);
extern u32 nv_native_handle(u64 addr, u64 size);
extern void nv_gpu_map_raw(u64 gva, u64 cpu, u64 size), nv_gpu_unmap_raw(u64 gva, u64 size);
extern int nv_native_bind(u32 h, u64 addr), nv_native_alive(u32 h), nv_native_map(u64 gva, u32 h, u64 off, u64 size);
extern void nv_native_free(u32 h), nv_native_unmap(u64 gva, u64 size);
extern int nv_open_dev(const char* name), nv_fd_is_as(u32 fd);
extern u32 syncpt_read(u32 id); extern int syncpt_wait(u32 id, u32 thresh, i64 timeout);
extern u64 nvmap_addr(u32 h); extern u32 nvmap_size(u32 h);
extern void vi_show_addr(u64 a, u32 w, u32 h, u32 pitch, u32 layout, u32 bhl, u32 fmt);
extern int ipc_warn_once(const char* name, u32 cmd);

/* kernel results (module 1) */
#define K_INVSIZE   0xCA01
#define K_INVADDR   0xCC01
#define K_OUTOFRES  0xCE01
#define K_INVMEM    0xD401
#define K_NOTIMPL   0xF001
#define K_INVSTATE  0xFA01
#define K_NOTFOUND  0xF201
#define K_INVCOMB   0xE801
#define K_BUSY      0xFC01

static u32 W(IpcCtx* c, u32 i){ u32 v; memcpy(&v,c->msg+4*i,4); return v; }
static u64 W64(IpcCtx* c, u32 i){ return (u64)W(c,i)|((u64)W(c,i+1)<<32); }
static u32 ev_h(KEvent* e){ return h_new(&e->o); }
/* Switch 2 services fail soft: what this file doesn't know is logged and answered "ok" with zeros, so the game goes
   on and one log shows several missing pieces instead of stopping at the first one. SWR_NS2_STRICT=1 answers
   NotImplemented like the system */
static int ns2_strict(void){ static int v=-1; if(v<0) v=getenv("SWR_NS2_STRICT")!=NULL; return v; }
static int soft_worker_disp(SvcObj*,IpcCtx*); static int soft_sync_disp(SvcObj*,IpcCtx*); static int soft_vi2_disp(SvcObj*,IpcCtx*);
static int soft_gpusess_disp(SvcObj*,IpcCtx*); static int soft_gsv_disp(SvcObj*,IpcCtx*);
/* a command this file doesn't know */
static int ns2_unknown(SvcObj* o, IpcCtx* c){
  /* command 0 with a 64 bit word is a version handshake: the sdk sends its version and aborts unless the same value
     comes back (nn::syncpt::sdk::Initialize does it on the syncpoint session) */
  if(c->cmd==0 && (W(c,1)&0x3FF)>=2){ u64 v=W64(c,2);
    if(ipc_warn_once(o->name,0)) LOG("switch 2: %s handshake %llx\n",o->name,(unsigned long long)v);
    out64(c,v); return 0; }
  if(ipc_warn_once(o->name,c->cmd)){ u32 n=W(c,1)&0x3FF; if(n>12) n=12; char b[160]; int k=0; for(u32 i=0;i<n;i++) k+=snprintf(b+k,sizeof b-k," %x",W(c,2+i));
    WARN("  [switch 2] %s cmd %u not implemented (words%s)%s\n",o->name,c->cmd,k? b : " none",ns2_strict()? "" : ", answered ok with zeros"); }
  if(ns2_strict()) return K_NOTIMPL;
  for(int i=0;i<4;i++) out64(c,0);   /* the game reads its outputs as zeros instead of aborting on NotImplemented */
  return 0; }
/* a check this file doesn't know how to answer (NotImplemented) becomes success too, logged once per command */
static int ns2_soft(SvcObj* o, IpcCtx* c, int rc){
  if(rc!=K_NOTIMPL || ns2_strict()) return rc;
  if(ipc_warn_once("ns2-soft",((u32)(uintptr_t)o->name<<8)^c->cmd)) WARN("  [switch 2] %s cmd %u: case not handled, answered ok\n",o->name,c->cmd);
  return 0; }
/* a session handed back as a move handle; on failure the slot still goes out (the SDK reads it before the result) */
static int move_obj(IpcCtx* c, SvcObj* o, int rc){ out_move_h(c, rc? 0 : session_new(o)); if(rc && o) svcobj_unref(o); return rc; }

/* ============================================================ shared state (one process) */
static PMutex g_ns2; static int g_ns2_init;
static void ns2_lock(void){ if(!g_ns2_init){ pm_init(&g_ns2); g_ns2_init=1; } pm_lock(&g_ns2); }
static void ns2_unlock(void){ pm_unlock(&g_ns2); }

typedef struct { u32 id, mem; u32 pref[16]; u64 size; int window_pool; u64 off; } NsImage;   /* off: where in mem (image pools) */
static NsImage g_img[1024]; static u32 g_nimg, g_next_img=1;
static u32 g_native_mem[1024]; static u32 g_nnative;
static int g_phase;              /* 0 created, 1 initialized, 2 process bound, 3 ready */
static int g_gpu_ctx, g_gpu_ready, g_frame_ctx, g_img_ctx, g_img_formats, g_disp_ctx, g_sync_ctx;

static int native_mem_has(u32 id){ for(u32 i=0;i<g_nnative;i++) if(g_native_mem[i]==id) return 1; return 0; }
static NsImage* image_find(u32 id){ for(u32 i=0;i<g_nimg;i++) if(g_img[i].id==id) return &g_img[i]; return NULL; }

/* Ounce's NativeWindow::Present path is not an IPC call: the guest wrapper calls the
   native vi2 backend directly after OnPresentTexture.  Keep that path equivalent to
   vi2 command 229 by presenting the selected native image through the runtime's
   existing display bridge. */
void ns2_native_present(u32 slot){
  NsImage image; memset(&image,0,sizeof image);
  ns2_lock();
  u32 n=0, chosen=0;
  for(u32 i=0;i<g_nimg;i++) if(g_img[i].window_pool){
    if(n++ == (slot % 16u)) chosen=i;
  }
  if(n && chosen<g_nimg) image=g_img[chosen];
  ns2_unlock();
  if(!image.id) return;
  u64 a=nvmap_addr(image.mem); if(!a) return; a+=image.off;
  u32 w=(image.pref[2]&0xFFFF)+1, h=(image.pref[2]>>16)+1;
  u32 pitch=image.pref[5]*64;
  if(!w || !h || !pitch) return;
  vi_show_addr(a,w,h,pitch,3,image.pref[4]>=3? image.pref[4]-3 : 0,532120);
}

/* the size of a native image: four-byte color, row pitch in GOBs, block height 2^pref[4] pixels */
/* a layout image_size doesn't know: a size that's surely big enough (16 bytes a pixel unless the pitch says less, 128
   line blocks, every layer and twice that for mips), so the game gets memory instead of an abort */
static int image_size(const u32* p, u32 count, u64* size, u64* align);
static int image_size_any(const u32* p, u32 count, u64* size, u64* align){
  if(image_size(p,count,size,align)) return 1;
  { static int said; if(said<sw2_cap(16)){ said++; WARN("switch 2: image layout not handled (count %u):",count); for(int i=0;i<16;i++) WARN(" %x",p[i]); WARN("%s\n",ns2_strict()? "" : ", size estimated"); } }
  if(ns2_strict()) return 0;
  u64 w=(p[2]&0xFFFF)+1, h=(p[2]>>16)+1, pitch= p[5]>=(w*4+63)/64 && p[5]<=4096? (u64)p[5]*64 : w*16;
  u64 layers=(count? count : 1), one=pitch*((h+127)&~127ull);
  *size=((one*layers*(p[7]>1? 2 : 1))+0xFFFF)&~0xFFFFull; if(align) *align=0x10000; return 1; }

/* p[6] isn't always 1: Mario Kart World's window asks for its 3840x2160 textures with 4 there. It doesn't make the
   image bigger: the window places its textures one image size apart, and with 4x the size its memory pool came to
   382 MB, more than the game's 117 MB GraphicsSystem heap (HeapDef), so the pool got no memory and the window aborted.
   SWR_NS2_IMG_LAYERS=1 multiplies by it again */
static int image_size(const u32* p, u32 count, u64* size, u64* align){
  if(count!=1 || p[0]!=0 || (p[1]!=1 && p[1]!=2) || p[3]!=0 || !p[6] || p[6]>16 || p[7]!=1 || p[4]>8) return 0;
  for(int i=8;i<16;i++) if(p[i]) return 0;
  u64 w=(p[2]&0xFFFF)+1, h=(p[2]>>16)+1, gobs=p[5]; if(gobs<(w*4+63)/64 || gobs>4096) return 0;
  u64 bh=1ull<<p[4]; u64 one=gobs*64*((h+bh-1)&~(bh-1)); one=(one+0xFFF)&~0xFFFull;
  *size= getenv("SWR_NS2_IMG_LAYERS")? one*p[6] : one; if(align){ *align=64*bh; if(*align<0x1000) *align=0x1000; } return 1; }

/* ============================================================ syncpoint cache: 192 counters the GPU's syncpoints
   are copied into, in two transfer memories (requests in rw, values and acks in ro), refreshed every millisecond */
#define SC_N 192
static u64 g_sc_rw, g_sc_ro; static KEvent *g_sc_req, *g_sc_done; static u64 g_sc_prev[SC_N];
static void sc_refresh(void){
  if(!g_sc_rw) return;
  u64 req=gr64(g_sc_rw), ack=gr64(g_sc_ro+0x640), groups=(req^ack)&7; if(!groups) return;
  for(u32 g=0;g<3;g++){ if(!(groups>>g&1)) continue;
    u64 want=gr64(g_sc_rw+8+g*8), slots=want^gr64(g_sc_ro+0x648+g*8);
    for(u32 b=0;b<64;b++) if(slots>>b&1){ u32 id=g*64+b; u32 cur=syncpt_read(id); u64 prev=g_sc_prev[id];
      u64 v= prev==~0ull? cur : ((prev&0xFFFFFFFF00000000ull)+((u32)cur<(u32)prev? 1ull<<32 : 0))|cur; g_sc_prev[id]=v; gw64(g_sc_ro+0x40+id*8,v); }
    __atomic_thread_fence(__ATOMIC_RELEASE); gw64(g_sc_ro+0x648+g*8,want); }
  __atomic_thread_fence(__ATOMIC_RELEASE); gw64(g_sc_ro+0x640,req);
  kevent_clear(g_sc_req); kevent_signal(g_sc_done); }
/* syncpoint event slots (ISyncpointSupervisor 22/201/202): 201 asks for the slot's event once a syncpoint reaches a
   value, 202 cancels and always signals (nn::syncpt::sdk::CancelSyncPointEvent waits on it either way) */
static struct { KEvent* ev; u32 id, val; int armed; } g_sps[64];
static KEvent* sps_ev(u32 s){ s&=63; if(!g_sps[s].ev){ g_sps[s].ev=kevent_new("syncpoint slot",0); kobj_ref(&g_sps[s].ev->o); } return g_sps[s].ev; }
static void sps_poll(void){ for(int i=0;i<64;i++) if(g_sps[i].armed && (i32)(syncpt_read(g_sps[i].id)-g_sps[i].val)>=0){ g_sps[i].armed=0; kevent_signal(sps_ev(i)); } }
/* vi2 31/32 events: the display's vsync, every 16.7 ms (the main thread waits on 32 before its first frame) */
static KEvent* g_vsync[2];
static void sc_thread(void* a){ (void)a; u64 next=plat_ns()+16666667;
  for(;;){ plat_sleep_ns(1000000); ns2_lock(); sc_refresh(); sps_poll();
    if(plat_ns()>=next){ next+=16666667; if(plat_ns()>next) next=plat_ns()+16666667; for(int i=0;i<2;i++) if(g_vsync[i]) kevent_signal(g_vsync[i]); }
    ns2_unlock(); } }

static int sync_disp(SvcObj* o, IpcCtx* c){   /* ISyncpointSupervisor */
  switch(c->cmd){
    case 1: out32(c,63); return 0;                                      /* GetMaximumEventCount */
    case 21: return W(c,2)<=63? 0 : K_INVCOMB;                          /* SetEventCount */
    case 103: { u32 id=~W(c,2); out64(c,syncpt_read(id)); out32(c,0); return 0; }   /* QueryCounter */
    case 22: ns2_lock(); out_move_h(c,ev_h(sps_ev(W(c,2)))); ns2_unlock(); return 0;   /* the slot's event */
    case 201: { u32 s=W(c,2)&63; ns2_lock(); KEvent* e=sps_ev(s); kevent_clear(e); g_sps[s].id=~W(c,3); g_sps[s].val=W(c,4); g_sps[s].armed=1; sps_poll(); ns2_unlock(); return 0; }
    case 202: { u32 s=W(c,2)&63; ns2_lock(); g_sps[s].armed=0; kevent_signal(sps_ev(s)); ns2_unlock(); return 0; }
  }
  return ns2_unknown(o,c); }

/* ============================================================ GPU session, worker */
typedef struct { int as[8], as_reg[8]; u64 dev_name[256]; u8 dev_used[256]; KEvent* ev[64]; SvcObj* worker; } GpuDevs;
static GpuDevs g_dev;
typedef struct { u32 as; u64 gva, size; u32 mem; } GpuMap;
static GpuMap g_maps[32768]; static u32 g_nmaps;
typedef struct { u64 gva, size, cpu; } Sparse; static Sparse g_sparse[64]; static u32 g_nsparse;
/* memory behind sparse regions, at most 2 GB in all (SWR_SPARSE_MB): Windows commits all of it, and Mario Kart World's
   ~8 GB of regions on top of its 7.6 GB heap ran PCs out of commit, the next allocations failed and the runtime crashed.
   The renderer keeps render targets in host textures, a region left unbacked only loses CPU reads of them */
static u64 g_sparse_mb; static u64 sparse_budget_mb(void){ static u64 v; if(!v){ const char* e=getenv("SWR_SPARSE_MB"); v= e? strtoull(e,NULL,10) : 2048; if(!v) v=1; } return v; } static u32 g_wmem[16384]; static u32 g_nwmem;

static int as_owned(u32 id){ for(int i=0;i<8;i++) if(g_dev.as[i]==(int)id && g_dev.as_reg[i]) return 1; return 0; }
static void ev_sig(u32 i){ if(i<64 && g_dev.ev[i]) kevent_signal(g_dev.ev[i]); }
/* memory kinds: equal requested/fallback ones need no compression; compressible ones fall back */
static int kind_select(u8 req, u8 fb, u8* sel){
  if(req==fb && (req==0 || req==1 || req==3 || req==6)){ *sel=req; return 1; }
  if((req==8 && fb==6) || (req==0xB && fb==1) || (req==0xC && fb==3)){ *sel=fb; return 1; }
  return 0; }
/* guest memory the GPU may use carries attribute 0x20 (svc 0x80) */
static int gpu_accessible(u64 a, u64 end){
  for(u64 p=a;p<=end;){ MemBlock b; mem_query(p,&b); if(!b.size || !(b.attr&0x20)) return 0; u64 n=b.addr+b.size; if(n<=p) return 0; p=n; }
  return 1; }

static int worker_disp(SvcObj* o, IpcCtx* c){   /* IGpuWorker */
  switch(c->cmd){
    case 101: { /* CreateGpuAccessibleMemory {begin, end, flags u8, device u8} */
      u64 b=W64(c,2), e=W64(c,4); u32 fl=W(c,6)&0xFF, dv=W(c,7)&0xFF; u32 id=0; int rc;
      if(fl) rc=K_NOTIMPL; else if(!g_dev.dev_used[dv]) rc=K_NOTFOUND; else if(e<b || e==~0ull) rc=K_INVSIZE;
      else if((b|(e-b+1))&0xFFF) rc=(b&0xFFF)? K_INVADDR : K_INVSIZE; else if(g_nwmem>=16384) rc=K_OUTOFRES;
      else if(!gpu_accessible(b,e)) rc=K_INVMEM;
      else { id=nv_native_handle(b,e-b+1); rc= id? 0 : K_OUTOFRES; if(id) g_wmem[g_nwmem++]=id; }
      if(rc){ static int said; if(said<sw2_cap(8)){ said++; LOG("switch 2: GPU-accessible memory %llx-%llx refused (%x, %u registered)\n",(unsigned long long)b,(unsigned long long)e,rc,g_nwmem); } }
      out32(c,id); return rc; }
    case 102: { /* DestroyGpuAccessibleMemory {id, notification} */
      u32 id=W(c,2), n=W(c,3); for(u32 i=0;i<g_nwmem;i++) if(g_wmem[i]==id){ nv_native_free(id); g_wmem[i]=g_wmem[--g_nwmem]; ev_sig(n); return 0; }
      return K_NOTFOUND; }
    case 211: { /* NormalMapGpuMemory4K {as, begin, end, memory, offset, ..., kind, fallback, ..., device, ..., notification} */
      u32 as=W(c,2), mem=W(c,7), dv=W(c,15)&0xFF, note=W(c,17); u64 b=W64(c,3), e=W64(c,5), off=W64(c,8); u8 sel=0; int rc;
      if(!as_owned(as) || !nv_native_alive(mem) || !g_dev.dev_used[dv]) rc=K_NOTFOUND;
      else if(!kind_select((u8)W(c,12),(u8)W(c,13),&sel)) rc=K_NOTIMPL;
      else if(e<b || e==~0ull) rc=K_INVSIZE; else if(g_nmaps>=32768) rc=K_OUTOFRES;
      else { rc= nv_native_map(b,mem,off,e-b+1)? K_INVMEM : 0; if(!rc) g_maps[g_nmaps++]=(GpuMap){as,b,e-b+1,mem}; }
      ev_sig(note);
      { static int said; if(said<sw2_cap(6)){ said++; LOG("switch 2: GPU map %llx-%llx -> memory %u + %llx, kind %x (%x)\n",(unsigned long long)b,(unsigned long long)e,mem,(unsigned long long)off,sel,rc); } }
      out32(c,sel); return rc; }
    case 212: { /* NormalModifyGpuMemory4K: the kind only (our page table has none) */
      u64 b=W64(c,3), e=W64(c,5); u8 sel=0; int rc=K_NOTFOUND;
      if(kind_select((u8)W(c,7),(u8)W(c,8),&sel)) for(u32 i=0;i<g_nmaps;i++) if(g_maps[i].as==W(c,2) && b>=g_maps[i].gva && e<g_maps[i].gva+g_maps[i].size){ rc=0; break; }
      ev_sig(W(c,10)); out32(c,sel); return rc; }
    /* 214 CreateSparseRegion {as, first, last, ...}, done through the event in word 11; 215 destroys it. The graphics
       server backs these itself on the console (render targets live there, Mario Kart World makes several). Here
       each gets memory of its own up to 2 GB a region; a bigger one stays unbacked (logged), maps into it still work */
    case 214: { u64 b=W64(c,3), e=W64(c,5), sz= e>=b? e-b+1 : 0; int rc=0; u64 cpu=0;
      if(!sz || (b&0xFFF) || (sz&0xFFF)) rc=K_INVSIZE;
      else if(g_nsparse<64 && sz<=(2ull<<30) && g_sparse_mb+(sz>>20)<=sparse_budget_mb()){ cpu=mem_find_free(0xC00000000ull,0x1300000000ull,sz,0x10000);
        if(cpu && !mem_map(cpu,sz,MS_NORMAL,PERM_RW)){ nv_gpu_map_raw(b,cpu,sz); g_sparse[g_nsparse++]=(Sparse){b,sz,cpu}; g_sparse_mb+=sz>>20; } else cpu=0; }
      { static int said; if(said<sw2_cap(8)){ said++; LOG("switch 2: sparse GPU region %llx-%llx (%llu MB) %s\n",(unsigned long long)b,(unsigned long long)e,(unsigned long long)(sz>>20),cpu? "backed" : "left unbacked"); } }
      ev_sig(W(c,11)); return rc; }
    case 215: { u64 b=W64(c,3);
      for(u32 i=0;i<g_nsparse;i++) if(g_sparse[i].gva==b){ nv_gpu_unmap_raw(b,g_sparse[i].size); mem_unmap(g_sparse[i].cpu,g_sparse[i].size); g_sparse_mb-=g_sparse[i].size>>20; g_sparse[i]=g_sparse[--g_nsparse]; break; }
      ev_sig(W(c,11)); return 0; }
    case 213: { /* NormalUnmapGpuMemory4K */
      u64 b=W64(c,3), e=W64(c,5), n=0; int rc=K_NOTFOUND;
      for(u32 i=0;i<g_nmaps;i++) if(g_maps[i].as==W(c,2) && g_maps[i].gva==b && e-b+1==g_maps[i].size){ nv_native_unmap(b,g_maps[i].size); n=g_maps[i].size; g_maps[i]=g_maps[--g_nmaps]; rc=0; break; }
      ev_sig(W(c,8)); out64(c,n); return rc; }
  }
  return ns2_unknown(o,c); }

static int gpusess_disp(SvcObj* o, IpcCtx* c){   /* IGpuSession */
  ns2_lock(); int rc=0;
  switch(c->cmd){
    case 11: out32(c,0); out32(c,63); break;                            /* GetNotificationRange */
    case 12: { u32 i=W(c,2); if(i>=64){ rc=K_INVCOMB; out_move_h(c,0); break; }   /* GetNotificationEvent */
      if(!g_dev.ev[i]){ g_dev.ev[i]=kevent_new("gpu notification",0); kobj_ref(&g_dev.ev[i]->o); }
      out_move_h(c,ev_h(g_dev.ev[i])); break; }
    case 21: { u32 i=W(c,2); if(i>=64 || !g_dev.ev[i]){ rc=K_INVSTATE; break; }   /* RequestWorker */
      if(!g_dev.worker) g_dev.worker=svcobj_new("IGpuWorker",soft_worker_disp,0); kevent_signal(g_dev.ev[i]); break; }
    case 22: if(!g_dev.worker){ rc=K_INVSTATE; out_move_h(c,0); break; }   /* AcquireWorker */
      g_dev.worker->refs++; out_move_h(c,session_new(g_dev.worker)); break;
    case 33: { rc=K_OUTOFRES; for(int i=0;i<8;i++) if(!g_dev.as[i]){ int fd=nv_open_dev("/dev/nvhost-as-gpu");   /* CreateAddressSpace */
        if(fd>0){ g_dev.as[i]=fd; out32(c,(u32)fd); rc=0; } break; }
      if(rc) out32(c,0); break; }
    case 41: { u64 name=W64(c,2), flags=W64(c,4); u32 id=0; rc= flags? K_NOTIMPL : K_OUTOFRES;   /* CreateGraphicsDevice */
      if(!flags) for(u32 i=1;i<256;i++) if(!g_dev.dev_used[i]){ g_dev.dev_used[i]=1; g_dev.dev_name[i]=name; id=i; rc=0; break; }
      out32(c,id); break; }
    case 42: { u32 i=W(c,2)&0xFF; rc= g_dev.dev_used[i]? 0 : K_NOTFOUND; g_dev.dev_used[i]=0; break; }   /* DestroyGraphicsDevice */
    /* Eglantine's newer nx2:gsv path uses 201/202 for the user and GSV
       partitions respectively.  The old 203 VA-range query remains for
       SDKs that still use it.  These replies are ranges, not nvdrv handles;
       returning K_NOTIMPL here makes NVN close the device before submitting. */
    case 201: { u64 first=0x8000000ull, last=0xC000000000ull;
      LOG("switch 2: GPU user partition %llx-%llx\n",(unsigned long long)first,(unsigned long long)last);
      out64(c,first); out64(c,last-first); break; }
    case 202: { out64(c,~0ull); out64(c,0); break; }                  /* empty GSV partition */
    case 203: { u32 id=W(c,2); int ok=0; for(int i=0;i<8;i++) if(g_dev.as[i]==(int)id) ok=1;
      rc= ok? 0 : K_NOTFOUND;
      if(ok){ out64(c,1); out64(c,0x04000000); out64(c,0xFFFFFFFFFFull); for(int k=0;k<6;k++) out64(c,0); }
      else out64(c,0); break; }
    default: ns2_unlock(); return ns2_unknown(o,c);
  }
  ns2_unlock(); return rc; }

/* ============================================================ vi2: display sessions, presenting native images */
typedef struct { u64 token; u32 slots; int has_display, bound_default; u64 available; u32 retire_note, avail_note; u64 encoding; u32 queued; } Vi2Client;
typedef struct { Vi2Client cl[16]; u32 client_slots; int display_refs; u32 display_note; u32 notes[32]; KEvent* ev; int endpoint; u64 endpoint_token; } Vi2;
#define NAME_DEFAULT 0x00746C7561666564ull   /* "default" */
static Vi2Client* vi2_find(Vi2* v, u64 t){ if(!t) return NULL; for(int i=0;i<16;i++) if(v->cl[i].token==t) return &v->cl[i]; return NULL; }
static void vi2_note(Vi2* v, u32 n){ v->notes[(n/32)&31]|=1u<<(n%32); if(v->ev) kevent_signal(v->ev); }

static int vi2_present(Vi2* v, Vi2Client* s, IpcCtx* c){
  u32 slot=W(c,4)&0xFF; if(!s->has_display || slot>=15) return K_INVSTATE;
  NsImage* im=image_find(W(c,5)); if(!im || !im->window_pool) return K_NOTFOUND;
  u32 fence=~W(c,22), fval=W(c,24);
  /* word 7: the crop, (bottom << 16) | right, inclusive. Mario Kart World renders 1920x1080 into its 3840x2160 window
     images and shows only that corner (it filled a quarter of the screen without this) */
  { extern volatile i32 g_vi_crop[4]; u32 cr=W(c,7); if(cr){ g_vi_crop[0]=0; g_vi_crop[1]=0; g_vi_crop[2]=(i32)(cr&0xFFFF)+1; g_vi_crop[3]=(i32)(cr>>16)+1; } else memset((void*)g_vi_crop,0,sizeof g_vi_crop); }
  /* the image is complete once the GPU reached the fence. Mario Kart World passes no fence (its NativeSyncHandle is -1,
     which reads as syncpoint 0 here): that wait never ended and cost 200 ms each frame (5 FPS). The present goes to the
     GPU thread behind the submits that draw it anyway */
  { static int nl; if(nl<sw2_cap(3)){ nl++; LOG("switch 2: present words 20-25: %08x %08x %08x %08x %08x %08x\n",W(c,20),W(c,21),W(c,22),W(c,23),W(c,24),W(c,25)); } }
  if(fence!=~0u && fence!=0) syncpt_wait(fence,fval,50000000);
  u32 w=(im->pref[2]&0xFFFF)+1, h=(im->pref[2]>>16)+1, pitch=im->pref[5]*64;
  u64 a=nvmap_addr(im->mem); if(!a) return K_NOTFOUND;
  { static u64 pk=~0ull; static int np; if(pk==~0ull){ const char* e=getenv("SWR_PEEK"); pk= e? strtoull(e,NULL,16) : 0; }   /* debug: guest words at a GPU address, each present */
    { static u32 fw; static int done; if(!done && np==30){ done=1; const char* e=getenv("SWR_FIND"); if(e){ fw=(u32)strtoul(e,NULL,16); int hits=0;   /* debug: where a u32 sits in guest memory */
        for(u64 a=0x10000; a<(1ull<<39) && hits<24;){ MemBlock b; mem_query(a,&b); if(!b.size) break; u64 n=b.addr+b.size; if(n<=a) break;
          if(b.state!=MS_FREE && b.perm){ const u32* w=(const u32*)GP(b.addr); for(u64 i=0;i<b.size/4 && hits<24;i++) if(w[i]==fw){ hits++; LOG("find %08x at %llx\n",fw,(unsigned long long)(b.addr+i*4)); } }
          a=n; } LOG("find %08x: %d hits\n",fw,hits); } } }
    { static int done; if(!done && np==25){ const char* e=getenv("SWR_DUMPMEM"); if(e){ done=1; u64 da=strtoull(e,NULL,16), dn=4u<<20; extern u64 gmmu_translate(u64); u64 c0=gmmu_translate(da);   /* debug: 4 MB of guest memory at a GPU address */
        if(c0){ FILE* f=fopen("captures/memdump.bin","wb"); if(f){ fwrite(GP(c0),1,dn,f); fclose(f); LOG("dumped 4 MB at %llx\n",(unsigned long long)da); } } } } }
    if(pk && np%20==0){ extern u64 gmmu_translate(u64); u64 c0=gmmu_translate(pk); if(c0){ int nz=0, first=-1; for(int i=0;i<0x1000;i++) if(gr32(c0+i*4)){ nz++; if(first<0) first=i*4; } LOG("peek %llx (present %d): %d non-zero words in 16 KB (first at +%x)\n",(unsigned long long)pk,np,nz,first);
      if(np==20){ for(int r=0;r<0x240/16;r++){ float f[4]; memcpy(f,GP(c0+r*16),16); LOG("  +%03x: %g %g %g %g\n",r*16,f[0],f[1],f[2],f[3]); } } } }
    if(pk && np++<0){ extern u64 gmmu_translate(u64); u64 c=gmmu_translate(pk); if(c) LOG("peek %llx: %08x %08x %08x %08x  +0x40: %08x %08x %08x %08x  +0x210: %08x %08x %08x %08x\n",(unsigned long long)pk,gr32(c),gr32(c+4),gr32(c+8),gr32(c+12),gr32(c+0x40),gr32(c+0x44),gr32(c+0x48),gr32(c+0x4c),gr32(c+0x210),gr32(c+0x214),gr32(c+0x218),gr32(c+0x21c)); } }
  { static int said; if(said<sw2_cap(3)){ said++; LOG("switch 2: present image %u (%ux%u, pitch %u, block height 2^%u) slot %u, fence %d/%u\n",im->id,w,h,pitch,im->pref[4],slot,(int)fence,fval); } }
  vi_show_addr(a,w,h,pitch,3,im->pref[4]>=3? im->pref[4]-3 : 0,532120);   /* RGBA8, block linear, block height in GOBs */
  s->available|=1ull<<slot; vi2_note(v,s->avail_note);   /* shown already: the slot is free again */
  (void)fval; return 0; }

/* the chat context's session (GameChat camera images): command 11 hands out its notification event like vi2's;
   no camera, so the event never fires. The rest answers ok */
static int chat_disp(SvcObj* o, IpcCtx* c){
  if(c->cmd==11){ static KEvent* ev; if(!ev){ ev=kevent_new("chat notification",0); kobj_ref(&ev->o); } out_move_h(c,ev_h(ev)); return 0; }
  return ns2_unknown(o,c); }

/* video decoder (nn::codec::video): gsv 902/906/1002 hand out a session whose command 1 (CreateVideoDecoderService)
   hands out another. Nothing decodes yet: everything on them answers ok (movies get no picture) */
static int vdec_svc_disp(SvcObj* o, IpcCtx* c){ return ns2_unknown(o,c); }
static int vdec_disp(SvcObj* o, IpcCtx* c){
  if(c->cmd==1) return move_obj(c,svcobj_new("IVideoDecoderService",vdec_svc_disp,0),0);
  return ns2_unknown(o,c); }

static int vi2_disp(SvcObj* o, IpcCtx* c){   /* IVi2Session */
  Vi2* v=(Vi2*)o->data; ns2_lock(); int rc=0; u64 tok=W64(c,2); Vi2Client* s=vi2_find(v,tok);
  switch(c->cmd){
    case 1: case 3: case 5: out32(c,c->cmd==5? 7 : 0); break;           /* notification / session / request group limits */
    case 11: if(!v->ev){ v->ev=kevent_new("vi2 notification",0); kobj_ref(&v->ev->o); }   /* GetNotificationEvent */
      { int any=0; for(int i=0;i<32;i++) any|=v->notes[i]!=0; if(any) kevent_signal(v->ev); }
      out_move_h(c,ev_h(v->ev)); break;
    case 13: break;                                                     /* ReleaseNotificationEvent */
    case 31: case 32: { int i=c->cmd-31; if(!g_vsync[i]){ g_vsync[i]=kevent_new(i? "vi2 vsync 32" : "vi2 vsync 31",0); kobj_ref(&g_vsync[i]->o); }
      out_move_h(c,ev_h(g_vsync[i])); break; }                            /* vsync events, signalled at 60 Hz */
    case 21: { u64 a,sz; buf_out(c,0,&a,&sz); if(sz<sizeof v->notes){ rc=K_INVSIZE; break; }   /* GetNotifications */
      memcpy(GP(a),v->notes,sizeof v->notes); memset(v->notes,0,sizeof v->notes); if(v->ev) kevent_clear(v->ev); break; }
    case 51: rc= W(c,2)<8? 0 : K_INVCOMB; break;                        /* ConfigureRequestGroups */
    case 101: { u64 name=W64(c,2); u32 note=W(c,4);                       /* OpenDisplay */
      if(name!=NAME_DEFAULT){ rc=0; break; }   /* GameShare's player displays: accepted, nothing shown there */
      if(note!=1){ rc=K_NOTIMPL; break; } v->display_refs++; v->display_note=note; break; }
    case 102: if(W64(c,2)==NAME_DEFAULT && v->display_refs){ if(!--v->display_refs) vi2_note(v,v->display_note); } break;   /* CloseDisplay */
    case 111: if(!s && tok==NAME_DEFAULT){ v->endpoint=1; v->endpoint_token=tok; break; }   /* Mario Kart World opens it by display name ("default", "default") */
      if(!s || !s->has_display || v->endpoint){ rc= s? K_INVSTATE : K_NOTFOUND; break; } v->endpoint=1; v->endpoint_token=tok; break;   /* OpenEndpoint */
    case 112: if(!v->endpoint){ rc=K_NOTFOUND; break; } v->endpoint=0; break;   /* CloseEndpoint */
    case 104: case 105: break;   /* display "default", ~75 times a second in Mario Kart World: success, no outputs */
    case 201: { u32 a=W(c,4), b=W(c,5);                                 /* RegisterClientState {token, retire, available} */
      if(!tok || a>=32 || b>=32 || a==b){ rc=K_INVCOMB; break; } u32 sl=(1u<<a)|(1u<<b);
      if(s || (v->client_slots&sl)){ rc=K_INVSTATE; break; }
      Vi2Client* f=vi2_find(v,0); for(int i=0;i<16 && !f;i++) if(!v->cl[i].token) f=&v->cl[i];
      if(!f){ rc=K_OUTOFRES; break; }
      memset(f,0,sizeof *f); f->token=tok; f->slots=sl; f->retire_note=a; f->avail_note=b; f->available=0x7FFF; f->encoding=0x14; v->client_slots|=sl; break; }
    case 202: if(!s){ rc=K_NOTFOUND; break; } vi2_note(v,s->retire_note); v->client_slots&=~s->slots; memset(s,0,sizeof *s); break;   /* UnregisterClientState */
    case 212: if(!s){ rc=K_NOTFOUND; out64(c,0); break; } out64(c,s->available); break;   /* GetClientAvailability */
    case 228: { u32 slot=W(c,4)&0xFF; if(!s || slot>=15){ rc=K_NOTFOUND; } else s->available|=1ull<<slot;   /* CancelClientBuffer */
      out64(c,s? s->available : 0); for(int i=0;i<4;i++) out32(c,0); break; }
    case 229: { if(!s) rc=K_NOTFOUND; else { s->available&=~(1ull<<(W(c,4)&0xFF)); ns2_unlock(); rc=vi2_present(v,s,c); ns2_lock(); }   /* PresentClientBuffer */
      out64(c,s? s->available : 0); for(int i=0;i<4;i++) out32(c,0); break; }
    case 251: if(!s){ rc=K_NOTFOUND; break; } if(W64(c,4)==NAME_DEFAULT && !v->display_refs){ rc=K_INVSTATE; break; } s->has_display=1; break;   /* BindClientDisplay */
    case 252: if(!s || !s->has_display){ rc=K_NOTFOUND; break; } s->has_display=0; break;   /* UnbindClientDisplay */
    case 351: if(!s){ rc=K_NOTFOUND; break; } rc= W64(c,4)==0x14? 0 : K_NOTIMPL; break;   /* SetClientOutputEncoding */
    default: ns2_unlock(); return ns2_unknown(o,c);
  }
  ns2_unlock(); return rc; }

/* ============================================================ IGraphicsSupervisor */
static int gsv_disp(SvcObj* o, IpcCtx* c){
  int cmd=(int)c->cmd, rc=0;
  ns2_lock();
  switch(cmd){
    case 4: { u64 flags=W64(c,6); rc= g_phase? K_INVSTATE : 0; if(!rc) g_phase=1;   /* Initialize {process, aruid, flags, remote memory} */
      LOG("switch 2: graphics supervisor bootstrap (flags %llx)\n",(unsigned long long)flags); break; }
    case 11: rc= g_phase==1? 0 : K_INVSTATE; if(!rc) g_phase=2; break;  /* BindProcess */
    case 101: rc= g_phase==2? 0 : K_INVSTATE; if(!rc){ g_phase=3; LOG("switch 2: graphics supervisor ready\n"); } break;   /* CompleteBootstrap */
    case 111: { u64 sz=W64(c,3); u32 id=0;                             /* CreateNativeMemory {kind, size} */
      if(g_phase!=3) rc=K_INVSTATE; else if(!sz || sz>(1ull<<32) || (sz&0xFFF)) rc=K_INVSIZE; else if(g_nnative>=1024) rc=K_OUTOFRES;
      else { id=nv_native_handle(0,sz); if(!id) rc=K_OUTOFRES; else g_native_mem[g_nnative++]=id; }
      out32(c,id); break; }
    case 112: { u32 id=W(c,2); rc=K_NOTFOUND; for(u32 i=0;i<g_nnative;i++) if(g_native_mem[i]==id){ nv_native_free(id); g_native_mem[i]=g_native_mem[--g_nnative]; rc=0; break; } break; }   /* DestroyNativeMemory */
    case 114: { u32 id=W(c,2); u64 a=W64(c,3), sz=W64(c,5), fl=W64(c,7), off=W64(c,9);   /* BindNativeMemory */
      if(!native_mem_has(id)) rc=K_NOTFOUND; else if((fl!=0 && fl!=2) || off) rc=K_NOTIMPL; else if(!a || sz!=nvmap_size(id)) rc=K_INVSIZE;
      else if(a&0xFFF) rc=K_INVADDR; else if(fl==2 && !gpu_accessible(a,a+sz-1)) rc=K_INVMEM; else nv_native_bind(id,a);
      break; }
    case 115: rc= g_phase==3? 0 : K_INVSTATE; out64(c,0); break;       /* ConfigureNativeMemory: the nvdrv-compatible mode */
    case 201: rc= g_phase==3? 0 : K_INVSTATE; if(!rc) g_sync_ctx=1; break;   /* InitializeSyncpointContext */
    case 202: if(!g_sync_ctx){ rc=K_INVSTATE; break; } rc=move_obj(c,svcobj_new("ISyncpointSupervisor",soft_sync_disp,0),0); break;   /* GetSyncpointSession */
    case 204: { /* BindSyncpointMemory: two transfer memories, 0x1000 bytes written by the game, 0x2000 read by it */
      KTmem* rw= c->ncopy>0? (KTmem*)h_get_type(c->copy_h[0],KO_TMEM) : NULL; KTmem* ro= c->ncopy>1? (KTmem*)h_get_type(c->copy_h[1],KO_TMEM) : NULL;
      if(!g_sync_ctx || g_sc_rw) rc=K_INVSTATE; else if(!rw || !ro || rw==ro) rc=0xE401; else if(rw->size!=0x1000 || ro->size!=0x2000) rc=K_INVSIZE;
      if(rc){ out_move_h(c,0); out_move_h(c,0); break; }
      memset(GP(rw->addr),0,0x1000); memset(GP(ro->addr),0,0x2000);
      static const u32 hdr[8]={1,0,SC_N-1,0x40,0,0x640,8,0x648}; memcpy(GP(ro->addr),hdr,sizeof hdr);
      for(u32 i=0;i<SC_N;i++){ gw64(ro->addr+0x40+i*8,~0ull); g_sc_prev[i]=~0ull; }
      g_sc_rw=rw->addr; g_sc_ro=ro->addr; g_sc_req=kevent_new("syncpoint cache request",0); g_sc_done=kevent_new("syncpoint cache",0);
      kobj_ref(&g_sc_req->o); kobj_ref(&g_sc_done->o); plat_thread(sc_thread,NULL,256*1024);
      out_move_h(c,ev_h(g_sc_req)); out_move_h(c,ev_h(g_sc_done));
      LOG("switch 2: syncpoint cache at %llx / %llx\n",(unsigned long long)g_sc_rw,(unsigned long long)g_sc_ro); break; }
    case 301: rc= g_phase==3? 0 : K_INVSTATE; if(!rc) g_disp_ctx=1; break;   /* InitializeDisplayContext */
    case 305: if(!g_disp_ctx){ rc=K_INVSTATE; out_move_h(c,0); break; }       /* OpenDisplaySession */
      rc=move_obj(c,svcobj_new("IVi2Session",soft_vi2_disp,sizeof(Vi2)),0); break;
    case 314: case 315: { NsImage* im=image_find(W(c,2)); int create=cmd==315;   /* {Destroy,Create}NativeWindowAliasImagePool */
      if(!im) rc=K_NOTFOUND; else if(create && W(c,3)!=1) rc=K_NOTIMPL; else if(im->window_pool==create) rc=K_INVSTATE; else im->window_pool=create; break; }
    case 401: rc= g_phase==3? 0 : K_INVSTATE; if(!rc) g_gpu_ctx=1; break;   /* InitializeGpuContext */
    case 402: rc= g_gpu_ctx? 0 : K_INVSTATE; if(!rc) g_gpu_ready=1; break;  /* ActivateGpuContext */
    case 423: { u32 id=W(c,2), parent=W(c,7); u64 a=W64(c,3), sz=W64(c,5), off=W64(c,8);   /* BindNativeGpuMemory: a range of other native memory */
      u64 pa=nvmap_addr(parent);
      if(!pa || !native_mem_has(id) || off>nvmap_size(parent) || sz>nvmap_size(parent)-off || a!=pa+off) rc=K_NOTFOUND;
      else if(sz!=nvmap_size(id)) rc=K_INVSIZE; else nv_native_bind(id,a);
      break; }
    case 429: { u32 id=0; u64 sz=0;                                    /* CreateNativeImage {preference[16], count, memory} */
      u32 p[16]; for(int i=0;i<16;i++) p[i]=W(c,2+i);
      if(g_phase!=3 || !g_gpu_ready) rc=K_INVSTATE;
      else if(!image_size_any(p,W(c,18),&sz,NULL)) rc=K_NOTIMPL;
      else if(!native_mem_has(W(c,19)) || !nvmap_addr(W(c,19))) rc=K_NOTFOUND;
      else if(nvmap_size(W(c,19))<sz) rc=K_INVSIZE; else if(g_nimg>=1024) rc=K_OUTOFRES;
      else { NsImage* im=&g_img[g_nimg++]; memset(im,0,sizeof *im); im->id=id=g_next_img++; im->mem=W(c,19); memcpy(im->pref,p,sizeof p); im->size=sz; }
      { static int said; if(said<sw2_cap(4)){ said++; LOG("switch 2: native image %u: %ux%u, pitch %u GOBs, memory %u (%x)\n",id,(p[2]&0xFFFF)+1,(p[2]>>16)+1,p[5],W(c,19),rc); } }
      out32(c,id); break; }
    case 430: { NsImage* im=image_find(W(c,2)); if(!im) rc=K_NOTFOUND; else if(im->window_pool) rc=K_BUSY; else *im=g_img[--g_nimg]; break; }   /* DestroyNativeImage */
    case 434: { u32 id=W(c,2); rc= g_gpu_ready? K_NOTFOUND : K_INVSTATE;   /* RegisterGpuAddressSpace */
      if(g_gpu_ready) for(int i=0;i<8;i++) if(g_dev.as[i]==(int)id){ g_dev.as_reg[i]=1; rc=0; } break; }
    case 435: case 1510: { u32 p[16]; for(int i=0;i<16;i++) p[i]=W(c,2+i); u64 sz=0, al=0;   /* CalculateNativeImageSize / ImageRequirements */
      /* The window asks for its native image size before the optional image
         format context is activated, matching Eglantine's gsv 435/1510 path. */
      if(g_phase!=3) rc=K_INVSTATE; else if(!image_size_any(p,W(c,18),&sz,&al)) rc=K_NOTIMPL;
      { static int said; if(said<sw2_cap(2)){ said++; LOG("switch 2: %s {",cmd==1510? "image requirements" : "native image size"); for(int i=0;i<16;i++) LOG("%s%x",i? " " : "",p[i]); LOG("} count %u -> size %llx align %llx (%x)\n",W(c,18),(unsigned long long)sz,(unsigned long long)al,rc); } }
      out64(c,sz); if(cmd==1510) out64(c,al); break; }
    case 497: if(g_phase!=3){ rc=K_INVSTATE; out_move_h(c,0); break; }       /* OpenGpuSession */
      rc=move_obj(c,svcobj_new("IGpuSession",soft_gpusess_disp,0),0); break;
    /* 1201-1203: the chat (GameChat camera) context, nn::chat::gsv::Initialize. 1202 hands out a session the sdk
       calls next (it sent requests to handle 0 without one); everything on it answers ok for now */
    /* 601/602: another context with its session (the game sends requests on 602's right away); the session answers
       ok to everything for now, its commands show up in the log */
    case 901: case 1001: break;                                        /* the video decoder's contexts */
    case 902: case 906: case 1002: rc=move_obj(c,svcobj_new("IVideoDecoderSession",vdec_disp,0),0); break;
    /* 991: nn::codec::CalculateDecoderImagePoolBuffer, one block-linear NV12 frame: luma and chroma planes with
       their heights rounded to 128 lines (640x360 -> 0x64000). The size words aren't known yet: logged, 640x360
       unless the first words look like a size */
    case 991: { u32 w=W(c,2), h=W(c,3); if(w<16 || w>8192 || h<16 || h>8192){ w=640; h=360; }
      u64 pitch=(w+63)&~63ull, sz=pitch*((h+127)&~127ull)+pitch*(((h+1)/2+127)&~127ull);
      { static int said; if(said<sw2_cap(2)){ said++; LOG("switch 2: decoder image size {%x %x %x %x} -> %ux%u, %llx bytes\n",W(c,2),W(c,3),W(c,4),W(c,5),w,h,(unsigned long long)sz); } }
      out64(c,sz); out64(c,0x10000); break; }
    case 601: break;
    case 602: rc=move_obj(c,svcobj_new("IGsvSession602",ns2_unknown,0),0); break;
    case 1201: break;
    /* 1211: the chat camera's image pool {preference[16], count, memory}: one native image in that memory, its id is
       the pool's (nn::chat::gsv::GetImagePoolImageHandle hands it to QueryNativeImage, 428) */
    /* the pool's images get consecutive ids (nn::gs::sdk::CalculateNativeImageHandle is the first one + index), each
       at its own offset in the memory: as many as fit (the memory came from 1291's size) */
    case 1211: { u32 p[16]; for(int i=0;i<16;i++) p[i]=W(c,2+i); u32 mem=0; u64 sz=0;
      for(int i=18;i<22;i++) if(native_mem_has(W(c,i))){ mem=W(c,i); break; }
      image_size_any(p,1,&sz,NULL); u64 msz= mem? nvmap_size(mem) : 0; if(!sz || sz>msz) sz=msz;
      u32 n= sz? (u32)(msz/sz) : 0; if(n>16) n=16;
      if(!mem || !n) rc=K_NOTFOUND; else if(g_nimg+n>1024) rc=K_OUTOFRES;
      else { u32 first=g_next_img; for(u32 i=0;i<n;i++){ NsImage* im=&g_img[g_nimg++]; memset(im,0,sizeof *im); im->id=g_next_img++; im->mem=mem; memcpy(im->pref,p,sizeof p); im->size=sz; im->off=(u64)i*sz; }
        out32(c,first); }
      { static int said; if(said<sw2_cap(2)){ said++; LOG("switch 2: chat image pool in memory %u: %u images of %llx bytes (%x)\n",mem,n,(unsigned long long)sz,rc); } }
      if(rc) out32(c,0); break; }
    /* 428: QueryNativeImage. The sdk reads the address at data+8, then a 128 byte descriptor: two kind bytes that have
       to be 1 (data+16, data+48), the image's offset and size (data+56) */
    /* 426: MapNativeImage {image, address space, permission, ...}: the same answer as 428 with the GPU address. GPU
       addresses are the CPU ones here, the image's memory gets mapped at its own address. 427 unmaps (ok) */
    case 426: case 428: { NsImage* im=image_find(W(c,2)); if(!im){ rc=K_NOTFOUND; break; }
      u64 a=nvmap_addr(im->mem); if(a) a+=im->off;
      if(cmd==426 && a){ for(u32 i=0;i<g_nmaps;i++) if(g_maps[i].gva==a){ a=0; break; }
        if(a && !nv_native_map(a,im->mem,im->off,(im->size+0xFFF)&~0xFFFull) && g_nmaps<4096) g_maps[g_nmaps++]=(GpuMap){W(c,3),a,(im->size+0xFFF)&~0xFFFull,im->mem};
        a=nvmap_addr(im->mem)+im->off; }
      /* descriptor (nvnTextureInitializeFromNativeImage reads it): byte 0 = 1, +8 the size word ((w-1) | (h-1) << 16),
         +32 = 1 with the image kind above it (the preference's p[1]: 1 for color formats, 2 for the YUV ones),
         +40 offset and size */
      u32 kind= im->pref[1]==1 || im->pref[1]==2? im->pref[1] : 1;
      out64(c,a); out64(c,a); out64(c,1); out64(c,im->pref[2]);   /* data+0: the GPU address (MapNativeImage keys its mappings by it) */ out64(c,0); out64(c,0); out64(c,1|((u64)kind<<32));
      out64(c,(u64)(u32)im->size<<32); for(int i=0;i<10;i++) out64(c,0); out32(c,0);
      { static int said; if(said<sw2_cap(4)){ said++; LOG("switch 2: native image %u %s (%llx, %llx bytes)\n",im->id,cmd==426? "mapped" : "queried",(unsigned long long)a,(unsigned long long)im->size); } }
      break; }
    case 427: break;
    /* 1291: the chat camera's video memory for an image preference ({0, 1, size, ...} like 1510's): a size that's
       surely big enough, so CreateNativeMemory (111) gets a real size instead of 0 */
    case 1291: { u32 p[16]; for(int i=0;i<16;i++) p[i]=W(c,2+i); u64 sz=0, al=0x10000;
      image_size_any(p,1,&sz,&al); if(!sz) sz=0x400000; sz=(sz*4+0xFFFF)&~0xFFFFull;
      { static int said; if(said<sw2_cap(2)){ said++; LOG("switch 2: chat video memory %ux%u -> %llx bytes\n",(p[2]&0xFFFF)+1,(p[2]>>16)+1,(unsigned long long)sz); } }
      out64(c,sz); out64(c,al); break; }
    case 1202: rc=move_obj(c,svcobj_new("IChatSession",chat_disp,0),0); break;
    case 1101: rc= g_phase==3? 0 : K_INVSTATE; if(!rc) g_frame_ctx=1; break;   /* InitializeFrameContext */
    case 1102: rc= g_frame_ctx? 0 : K_INVSTATE; break;                         /* ActivateFrameContext */
    /* GetNvidiaDriver: an nvdrv session. games that bootstrap with flag bit 0 (nvdrv mode) ask for it right after
       CompleteBootstrap, without setting up the image context first */
    case 1402: if(g_phase!=3){ rc=K_INVSTATE; break; }
      out_move_h(c,session_new(nvdrv_obj_new("nvdrv:gsv"))); LOG("switch 2: nvdrv session for the game's NVN\n"); break;
    case 1501: rc= g_phase==3? 0 : K_INVSTATE; if(!rc) g_img_ctx=1; break;   /* InitializeImageContext */
    case 1502: rc= g_img_ctx? 0 : K_INVSTATE; if(!rc) g_img_formats=1; break;
    default: ns2_unlock(); return ns2_unknown(o,c);
  }
  ns2_unlock();
  if(rc && ipc_warn_once("gsv-fail",(u32)cmd)) WARN("switch 2: graphics supervisor cmd %d -> %x\n",cmd,rc);
  return rc; }

/* ISelfController 2000: the session is made once and handed out as a copy handle */
#define NS2_SOFT(f) static int soft_##f(SvcObj* o, IpcCtx* c){ return ns2_soft(o,c,f(o,c)); }
NS2_SOFT(worker_disp) NS2_SOFT(sync_disp) NS2_SOFT(vi2_disp) NS2_SOFT(gpusess_disp) NS2_SOFT(gsv_disp)

void ns2_graphics_supervisor(IpcCtx* c){
  static u32 h; static SvcObj* o;
  if(!o){ o=svcobj_new("IGraphicsSupervisor",soft_gsv_disp,0); h=session_new(o); LOG("switch 2: graphics supervisor opened\n"); }
  out_copy_h(c,h_new(h_get(h))); }   /* a handle of its own each time, to the same session */

/* renderer=vulkan (the NVN layer): the memory of native image id, for nvnMemoryPoolBuilderSetNativeHandleNVX */
int ns2_native_image_mem(u32 id, u64* a, u64* n){ NsImage* im=image_find(id); if(!im){ *a=*n=0; return 0; }
  *a=nvmap_addr(im->mem)+im->off; *n=im->size; return *a!=im->off || im->off; }
