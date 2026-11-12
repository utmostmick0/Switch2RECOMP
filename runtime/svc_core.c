/* SwitchRecomp - Copyright 2026 MZ Labs
   Licensed under the GNU Affero General Public License v3.0, see LICENSE.txt and NOTICE.txt.
   Forks and derived works have to keep the credit to SwitchRecomp by MZ Labs and the startup screen. */
/* sm, am, set, time, acc, apm and a bunch of stub services that just say ok (nifm, shop, prepo...) */
#include "rt.h"
#include "audio.h"
#include <math.h>

extern int ipc_warn_once(const char*, u32);
KShmem* kshmem_new(u64 size, const char* name);
u8* kshmem_ptr(KShmem* s);

/* ================================================================ sm */
static int sm_disp(SvcObj* o, IpcCtx* c){
  switch(c->cmd){
    case 0: return 0;                                   /* RegisterClient */
    case 1: {                                           /* GetServiceHandle */
      char name[9]={0}; memcpy(name,c->raw,8);
      SvcObj* s=svc_open(name);
      if(!s){ WARN("sm: service '%s' does not exist in SwitchRecomp: using a stub\n",name);
        extern SvcObj* svc_generic(const char* n); s=svc_generic(name); }
      LOG("sm: GetServiceHandle(%s)\n",name);
      out_move_h(c,session_new(s)); return 0; }
    case 2: case 3: case 4: return 0;
  }
  return stub_ok(o,c);
}

static SvcObj* new_sm(void){ return svcobj_new("sm:",sm_disp,0); }

/* unknown service -> generic stub, everything succeeds */
typedef struct { char name[16]; } GenData;

SvcObj* svc_generic(const char* n);
/* Switch 2 services SwitchRecomp doesn't have (chat:u, GameChat) hand out their interface with command 0: on a
   Switch 2 title an unknown service answers command 0 with an object (unknown too, so everything on it succeeds).
   Mario Kart World's nn::chat::Initialize called through the object it didn't get. SWR_NS2_STRICT=1 turns it off */
static int generic_disp(SvcObj* o, IpcCtx* c){ extern int ipc_warn_once(const char*,u32);
  int obj= c->cmd==0 && (g_title_id>>56)==0x04 && !getenv("SWR_NS2_STRICT");
  if(ipc_warn_once(((GenData*)o->data)->name,c->cmd)) WARN("  [not implemented] %s cmd %u -> ok%s\n",((GenData*)o->data)->name,c->cmd,obj? " with an object" : "");
  if(obj){ char n[16]; snprintf(n,sizeof n,"%.11s#obj",((GenData*)o->data)->name); out_obj(c,svc_generic(n)); }
  return 0; }

SvcObj* svc_generic(const char* n){ SvcObj* o=svcobj_new("generic",generic_disp,sizeof(GenData)); strncpy(((GenData*)o->data)->name,n,15); o->name=((GenData*)o->data)->name; return o; }

/* services that only get an empty ok. each (service, command) gets logged once, so if a game gets stuck waiting on
   one of them you can see it in the log */
static int quiet_ok(SvcObj* o, IpcCtx* c){ static struct { const char* n; u32 cmd; } seen[96]; static int ns;
  for(int i=0;i<ns;i++) if(seen[i].n==o->name && seen[i].cmd==c->cmd) return 0;
  if(ns<96){ seen[ns].n=o->name; seen[ns].cmd=c->cmd; ns++; LOG("ipc: %s cmd %u answered empty\n",o->name,c->cmd); }
  return 0; }

static SvcObj* quiet(const char* name){ return svcobj_new(name,quiet_ok,0); }

/* ================================================================ shared events */
static u32 ev_handle(KEvent* e){ return h_new(&e->o); }

/* ================================================================ am */
static KEvent* g_msg_event; static u32 g_msgq[16]; static int g_nmsg;
static KEvent* g_launch_ev; static KEvent* g_res_ev; static KEvent* g_opmode_ev;
/* Eglantine keeps these IApplicationFunctions events as stable kernel objects.  Returning a
   newly-created event for every query loses the identity that the SDK caches in its multi-wait
   holders, and is especially visible on Switch 2 during graphics startup. */
static KEvent* g_appfn_gpu_error;
static KEvent* g_appfn_friend_channel;
static KEvent* g_appfn_notification_channel;
static KEvent* g_appfn_health_warning;
static KEvent* g_appfn_opmode_refresh;
static u64 g_user_id[2]={0x0123456789ABCDEFull,0xFEDCBA9876543210ull};

static void am_push_msg(u32 m){ pm_lock(&g_klock); if(g_nmsg<16) g_msgq[g_nmsg++]=m; pm_unlock(&g_klock); kevent_signal(g_msg_event); }

static KEvent* am_appfn_event(KEvent** slot, const char* name){
  if(!*slot){ *slot=kevent_new(name,0); kobj_ref(&(*slot)->o); }
  return *slot;
}

/* IStorage / IStorageAccessor */
typedef struct { u8* d; u64 size; } StorageData;

static int storage_acc_disp(SvcObj* o, IpcCtx* c){
  StorageData* s=(StorageData*)(size_t)o->u[0];
  switch(c->cmd){
    case 0: out64(c,s->size); return 0;
    /* compare against size-off, off+n can wrap around if off is huge */
    case 10: { u64 off=in64(c,0), a, n; buf_in(c,0,&a,&n); if(off>s->size || n>s->size-off) return RC(128,503); memcpy(s->d+off,GP(a),n); return 0; }
    case 11: { u64 off=in64(c,0), a, n; buf_out(c,0,&a,&n); if(off>s->size) return RC(128,503); if(n>s->size-off) n=s->size-off; memcpy(GP(a),s->d+off,n); return 0; }
  }
  return stub_ok(o,c); }

static int storage_disp(SvcObj* o, IpcCtx* c){
  if(c->cmd==0 || c->cmd==1){ SvcObj* a=svcobj_new("IStorageAccessor",storage_acc_disp,0); a->u[0]=(u64)(size_t)o->data; o->refs++; out_obj(c,a); return 0; }
  return stub_ok(o,c); }

SvcObj* am_storage_new(u64 size, const void* init){
  SvcObj* o=svcobj_new("IStorage",storage_disp,sizeof(StorageData)); StorageData* s=o->data; s->d=calloc(1,size?size:1); s->size=size;
  if(init) memcpy(s->d,init,size); return o; }

static int am_csg(SvcObj* o, IpcCtx* c){           /* ICommonStateGetter */
  switch(c->cmd){
    case 0: out_copy_h(c,ev_handle(g_msg_event)); return 0;
    case 1: { pm_lock(&g_klock);
      if(!g_nmsg){ g_msg_event->signaled=0; pm_unlock(&g_klock); return RC(128,3); }
      u32 m=g_msgq[0]; memmove(g_msgq,g_msgq+1,(--g_nmsg)*4); if(!g_nmsg) g_msg_event->signaled=0; pm_unlock(&g_klock);
      { static int nl; if(nl<16){ nl++; LOG("applet: message %u delivered (%d left)\n",m,g_nmsg); } }
      out32(c,m); return 0; }
    case 5: out8(c,(u8)g_opt_docked); return 0;                      /* GetOperationMode */
    case 6: out32(c,(u32)g_opt_docked); return 0;                    /* GetPerformanceMode */
    case 8: out8(c,0); return 0;                                     /* GetBootMode */
    case 9: out8(c,1); return 0;                                     /* GetCurrentFocusState: InFocus */
    case 13: out_copy_h(c,ev_handle(kevent_new("sleep lock",0))); return 0;
    case 10: case 11: case 12: case 50: case 51: case 52: case 53: case 54: case 55: case 59: case 66: case 67: case 68: case 900: return 0;
    case 60: out32(c,g_opt_docked? 1920 : 1280); out32(c,g_opt_docked? 1080 : 720); return 0;   /* GetDefaultDisplayResolution */
    case 61: out_copy_h(c,ev_handle(g_res_ev)); return 0;
    case 62: out32(c,g_opt_docked? 1920 : 1280); out32(c,g_opt_docked? 1080 : 720); return 0;
    case 63: out_copy_h(c,ev_handle(g_res_ev)); return 0;
    case 100: out8(c,0); return 0;
    case 300: out32(c,0); return 0;                                  /* GetSettingsPlatformRegion */
    case 400: case 401: case 403: out_copy_h(c,ev_handle(kevent_new("csg ev",0))); return 0;
  }
  return stub_ok(o,c); }

static int am_self(SvcObj* o, IpcCtx* c){          /* ISelfController */
  switch(c->cmd){
    case 0: { extern void process_exit(int); process_exit(0); return 0; }   /* Exit: the system kills the process, libnx just sleeps
                                                                               until that happens */
    case 9: out_copy_h(c,ev_handle(g_launch_ev)); return 0;            /* GetLibraryAppletLaunchableEvent */
    case 40: { static u64 layer=1; out64(c,layer++); return 0; }       /* CreateManagedDisplayLayer */
    case 41: out64(c,0); return 0;
    case 44: out64(c,1); out64(c,2); return 0;
    case 62: return 0;
    case 63: out32(c,0); return 0;                                     /* GetIdleTimeDetectionExtension */
    case 69: out8(c,0); return 0;                                      /* IsAutoSleepDisabled */
    case 90: out64(c,0); return 0;                                     /* GetAccumulatedSuspendedTickValue */
    case 91: out_copy_h(c,ev_handle(kevent_new("suspend",0))); return 0;
    case 100: case 110: case 120: return 0;
    case 2000: { extern void ns2_graphics_supervisor(IpcCtx*); ns2_graphics_supervisor(c); return 0; }   /* GetGraphicsSupervisor (Switch 2, svc_ns2.c) */
  }
  return quiet_ok(o,c); }

static int am_window(SvcObj* o, IpcCtx* c){
  switch(c->cmd){ case 1: out64(c,0x1234); return 0; case 10: case 11: case 12: return 0; }
  return stub_ok(o,c); }

static int am_appfn(SvcObj* o, IpcCtx* c){         /* IApplicationFunctions */
  switch(c->cmd){
    case 1: { u32 kind=in32(c,0);
      if(kind==2){ /* PreselectedUser */
        static int given; if(given) return RC(128,2); given=1;
        u8 buf[0x88]; memset(buf,0,sizeof buf); u32 magic=0xC79497CA; memcpy(buf,&magic,4); u32 one=1; memcpy(buf+4,&one,4); memcpy(buf+8,g_user_id,16);
        out_obj(c,am_storage_new(sizeof buf,buf)); return 0; }
      return RC(128,2); }
    case 10: out_obj(c,am_storage_new(in64(c,0),NULL)); return 0;
    case 20: out64(c,0); return 0;                                     /* EnsureSaveData */
    case 21: { const char* l[]={"ja","en-US","fr","de","it","es","zh-CN","ko","nl","pt","ru","zh-TW","en-GB","fr-CA","es-419"};
      u64 v=0; const char* s=l[g_opt_lang%15]; memcpy(&v,s,strlen(s)); out64(c,v); return 0; }
    case 25: out64(c,0); return 0;                                     /* ExtendSaveData */
    case 26: out64(c,0x4000000); out64(c,0x4000000); return 0;       /* GetSaveDataSize */
    case 110: out32(c,0); return 0;
    case 22: case 27: case 28: case 32: case 33: case 34: case 35: case 36: case 37:
    case 60: case 61: case 66: case 67: case 68: case 70: case 71: case 72:
    case 80: case 90: case 100: case 101: case 112: case 113: case 124:
    case 180: case 181: case 190: case 200: case 220: case 230:
    case 300: case 310: return 0;
    case 151: return RC(128,2);                                      /* TryPopFromNotificationStorageChannel: nothing queued */
    case 23: { char v[16]="1.0.0"; outbytes(c,v,16); return 0; }         /* GetDisplayVersion */
    case 40: out8(c,0); return 0;                                      /* NotifyRunning */
    case 50: out64(c,0x1111222233334444ull); out64(c,0x5555666677778888ull); return 0;
    case 130: out_copy_h(c,ev_handle(am_appfn_event(&g_appfn_gpu_error,"appfn gpu error"))); return 0;
    case 140: out_copy_h(c,ev_handle(am_appfn_event(&g_appfn_friend_channel,"appfn friend channel"))); return 0;
    case 150: out_copy_h(c,ev_handle(am_appfn_event(&g_appfn_notification_channel,"appfn notification channel"))); return 0;
    case 160: out_copy_h(c,ev_handle(am_appfn_event(&g_appfn_health_warning,"appfn health warning"))); return 0;
    case 210: out_copy_h(c,ev_handle(am_appfn_event(&g_appfn_opmode_refresh,"appfn operation mode refresh"))); return 0;
    case 321: return 0;                                                 /* Switch 2 SDK extension */
    case 141: return RC(128,2);
    case 170: out8(c,0); return 0;
  }
  return stub_ok(o,c); }

SvcObj* ipc_in_obj(IpcCtx* c, int i);
char g_opt_swkbd[64]="Player";

/* default keyboard text (keyboard_text= in the ini), utf-8 to utf-16 (BMP) */
static int swkbd_default(u16* o, int max){ const u8* q=(const u8*)(g_opt_swkbd[0]? g_opt_swkbd : "Player"); int k=0;
  while(*q && k<max){ u32 cp=*q++;
    if(cp>=0xE0 && q[0] && q[1]){ cp=((cp&0x0F)<<12)|((q[0]&0x3F)<<6)|(q[1]&0x3F); q+=2; }
    else if(cp>=0xC0 && q[0]){ cp=((cp&0x1F)<<6)|(q[0]&0x3F); q++; }
    o[k++]=(u16)cp; }
  o[k]=0; return k; }

/* inline keyboard (swkbd in inline mode, the game draws its own text field, like tomodachi life). the game pushes
   requests with PushInteractiveInData (cmd 103): u32 command and then its argument. Calc (10) has the flags,
   "appear" is when the keyboard opens. the applet answers with PopInteractiveOutData (cmd 104) and every reply is
   { u32 state, u32 reply type, payload }. on appear the player types in our own text window and the game gets
   ChangedString + DecidedEnter like with a real keyboard */
static struct { SvcObj* acc; SvcObj* q[16]; int nq; KEvent* ev; u32 state; int utf8, v2, inited, said, appeared, autoshown; u64 init_ns; u16 itext[64]; int ilen;
  /* typing in progress: the text goes out one letter per poll, enter comes a while after the last one */
  u16 ttext[0x1F6]; int tlen, tsent, typing; u64 tlast_ns; int tpolls; } g_kbi;
static void kbi_reply(u32 type, const void* pl, u32 n){
  if(g_kbi.nq>=16) return; u8* b=calloc(1,8+n); memcpy(b,&g_kbi.state,4); memcpy(b+4,&type,4); if(pl&&n) memcpy(b+8,pl,n);
  g_kbi.q[g_kbi.nq++]=am_storage_new(8+n,b); free(b); if(g_kbi.ev) kevent_signal(g_kbi.ev); }
/* the text is 0x3EC bytes in utf-16 replies and 0x7D4 in utf-8 ones, the arguments go right after it (libnx
   checks the sizes: ChangedString 0x3FC, V2 0x3FD, DecidedEnter 0x3F0). if the length goes in the wrong place
   tomodachi reads 0 and says "the pronunciation can't be read". enter=0: ChangedString only, 1: DecidedEnter only */
static void kbi_text_reply(const u16* t, int k, int enter){
  u8 buf[0x7D4+16+4]; memset(buf,0,sizeof buf); u32 len=k, off= g_kbi.utf8? 0x7D4 : 0x3EC;
  if(g_kbi.utf8){ int o=0; for(int i=0;i<k && o<0x7D0;i++){ u32 c=t[i];       /* utf-16 (BMP) -> utf-8 */
      if(c<0x80) buf[o++]=c; else if(c<0x800){ buf[o++]=0xC0|(c>>6); buf[o++]=0x80|(c&0x3F); }
      else { buf[o++]=0xE0|(c>>12); buf[o++]=0x80|((c>>6)&0x3F); buf[o++]=0x80|(c&0x3F); } } len=o; }
  else { if(k>0x1F5) k=0x1F5; memcpy(buf,t,k*2); len=k; }
  /* ChangedString: text, { u32 length, s32 dictionary start, s32 dictionary end, s32 cursor } (+1 byte in V2) */
  len=k;   /* lengths and the cursor count characters, also in utf-8 */
  if(!enter){ i32 arg[4]={(i32)len,-1,-1,(i32)len}; memcpy(buf+off,arg,16);
    kbi_reply(g_kbi.utf8? (g_kbi.v2? 0xF : 0x7) : (g_kbi.v2? 0xD : 0x2), buf, off+16+(g_kbi.v2?1:0)); return; }
  /* DecidedEnter: text, u32 length */
  memcpy(buf+off,&len,4); kbi_reply(g_kbi.utf8? 0x9 : 0x5, buf, off+4); }

/* like a person typing: one ChangedString per letter, then enter a second later. tomodachi checks the
   pronunciation in the background every time the text changes; with the text and enter in the same frame it took
   the result for the empty text and said the pronunciation can't be read */
static void kbi_text(const u16* t, int k){
  if(k>0x1F5) k=0x1F5; memcpy(g_kbi.ttext,t,k*2); g_kbi.tlen=k; g_kbi.tsent=0; g_kbi.typing=1; g_kbi.tpolls=0; g_kbi.tlast_ns=plat_ns();
  if(!k){ kbi_text_reply(t,0,0); g_kbi.tsent=0; }
  else { kbi_text_reply(t,1,0); g_kbi.tsent=1; }
  if(g_kbi.ev) kevent_signal(g_kbi.ev); }

/* every poll of the game: the next letter, or enter once the text has been complete for a second */
static void kbi_typing_step(void){
  if(!g_kbi.typing || g_kbi.nq) return;
  g_kbi.tpolls++;
  /* by time too: a game that pops until the queue is empty would get every letter in one frame */
  if(g_kbi.tsent<g_kbi.tlen){ if(g_kbi.tpolls<2 || plat_ns()-g_kbi.tlast_ns<100000000ull) return; g_kbi.tpolls=0; g_kbi.tsent++; kbi_text_reply(g_kbi.ttext,g_kbi.tsent,0); g_kbi.tlast_ns=plat_ns(); return; }
  if(plat_ns()-g_kbi.tlast_ns<1000000000ull || g_kbi.tpolls<20) return;
  g_kbi.typing=0; kbi_text_reply(g_kbi.ttext,g_kbi.tlen,1); }
static void kbi_bind(SvcObj* acc){
  if(g_kbi.acc==acc) return; for(int i=0;i<g_kbi.nq;i++) svcobj_unref(g_kbi.q[i]);
  KEvent* ev=g_kbi.ev; int said=g_kbi.said; memset(&g_kbi,0,sizeof g_kbi); g_kbi.ev=ev; g_kbi.said=said; g_kbi.acc=acc; if(ev) kevent_clear(ev); }
/* the player types in our text window and the game gets ChangedString + DecidedEnter. autoshow=1 means the game
   never asked to show the keyboard (a field it only opens on touch, like the island name in tomodachi), there Esc
   sends nothing */
static void kbi_type(int autoshow){
  u16 def[64], typed[64]; int k=swkbd_default(def,32);
  if(g_kbi.ilen>0){ memcpy(def,g_kbi.itext,g_kbi.ilen*2); k=g_kbi.ilen; def[k]=0; }   /* the game's own text (the name, when it asks for the
                                                                                         pronunciation) */
  extern int plat_text_input(const u16* def, u16* out, int max); int n=plat_text_input(def,typed,32);
  if(autoshow && n<=0){ LOG("applet: inline keyboard opened by the runtime, cancelled\n"); return; }
  if(n>0){ memcpy(def,typed,n*2); k=n; }
  g_kbi.state=3;
  { char a[72]; int i=0; for(;i<k && i<70;i++) a[i]= def[i]>=0x20 && def[i]<0x7F? (char)def[i] : '?'; a[i]=0;
    LOG("applet: inline keyboard text entered: \"%s\" (%d characters%s%s, %s)\n",a,k,n>0? "" : ", default",autoshow? ", opened by the runtime" : "",g_kbi.utf8? "UTF-8" : "UTF-16"); }
  kbi_text(def,k); }
static void kbi_request(SvcObj* acc, SvcObj* st){
  StorageData* sd=st->data; if(!sd || sd->size<4) return; u32 cmd; memcpy(&cmd,sd->d,4);
  kbi_bind(acc);
  if(g_kbi.said<40){ g_kbi.said++; LOG("applet: inline keyboard request %u (%llu bytes)",cmd,(unsigned long long)sd->size);
    if(cmd==10 && sd->size>=0x14){ u64 fl; memcpy(&fl,sd->d+0xC,8); LOG(" flags %llx",(unsigned long long)fl); } LOG("\n"); }
  if(cmd==13){ g_kbi.v2=1; return; }                                     /* SetChangedStringV2Flag */
  if(cmd==4){ g_kbi.state=0; acc->u[5]=1; g_kbi.typing=0;               /* Finalize: the applet ends here and the game waits */
    if(acc->u[4]) kevent_signal((KEvent*)(size_t)acc->u[4]); return; }   /* on its state event before going on */
  if(cmd!=10 || sd->size<0x14) return;                                   /* Calc */
  u64 fl; memcpy(&fl,sd->d+0xC,8);
  /* bit 5 only says the utf-8 mode changed, the real value is the utf8Mode byte (0x45C in the 0x4A0 calc arg,
     0x484 in the 0x4E8 one, +4 for the command word) */
  if(fl&(1<<5)){ u16 csz; memcpy(&csz,sd->d+8,2); u32 uo= csz>=0x4E8? 0x488 : 0x460; if(uo<sd->size) g_kbi.utf8= sd->d[uo]!=0; }
  /* the text the game puts in the field = the longest printable utf-16 run in the request. the first keyboards
     also log the non-zero bytes of the request (the field's mode is in there) */
  { const u8* d=sd->d; u32 n=(u32)sd->size; int best=0, bo=0;
    for(u32 o=0x10;o+2<=n;o+=2){ int l=0; while(o+l*2+2<=n){ u16 ch=d[o+l*2]|(d[o+l*2+1]<<8); if(ch<0x20 || ch==0xFFFF || (ch>0x7E && ch<0xA0)) break; l++; } if(l>best){ best=l; bo=o; } if(l) o+=(l-1)*2; }
    if(best>=1 && best<64 && (fl&(1<<3))){ g_kbi.ilen=best; for(int i=0;i<best;i++) g_kbi.itext[i]=d[bo+i*2]|(d[bo+i*2+1]<<8); }
    static int dumped; if(dumped<6 && (fl&(1<<2))){ dumped++; LOG("applet: inline keyboard appear request, text field at %#x (%d chars), non-zero bytes:",bo,best);
      for(u32 o=0;o<n;o+=16){ int nz=0; for(u32 k=0;k<16 && o+k<n;k++) if(d[o+k]) nz=1; if(!nz) continue; LOG("\n    %03x:",o); for(u32 k=0;k<16 && o+k<n;k++) LOG(" %02x",d[o+k]); }
      LOG("\n"); } }
  if(fl&1) g_kbi.init_ns=plat_ns();
  if((fl&1) && !g_kbi.inited){ g_kbi.inited=1; g_kbi.state=1; u8 z=0; kbi_reply(0x0,&z,1); }    /* FinishedInitialize, hidden */
  if(fl&(1<<2)){ g_kbi.appeared=1; kbi_type(0); }                         /* appear: the player types now */
  if(fl&(1<<7)){ g_kbi.state=1; g_kbi.typing=0; kbi_reply(0x1,NULL,0); }  /* disappear: Default reply with the hidden state */
}

/* library applets (swkbd, error...) finish right away with an empty result */
static int am_lib_accessor(SvcObj* o, IpcCtx* c){
  switch(c->cmd){
    /* the inline keyboard (swkbd created with a non-zero mode) keeps running. if it looks finished the game
       creates it again every frame (tomodachi life). it sends FinishedInitialize when it starts */
    case 0: { if(!(o->u[2]==0x11 && o->u[3])){ KEvent* e=kevent_new("applet state",0); e->signaled=1; out_copy_h(c,h_new(&e->o)); return 0; }
      if(!o->u[4]) o->u[4]=(u64)(size_t)kevent_new("applet state",0);      /* one event per inline keyboard, kept */
      KEvent* e=(KEvent*)(size_t)o->u[4]; if(o->u[5]) e->signaled=1; e->o.refs++; out_copy_h(c,h_new(&e->o)); return 0; }
    case 1: out8(c,(o->u[2]==0x11 && o->u[3] && !o->u[5])? 0 : 1); return 0;
    case 10: if(o->u[2]==0x11 && o->u[3]){ g_kbi.acc=NULL; kbi_bind(o);   /* a new keyboard can get the same address as the one
                                                                             that was freed */ if(!g_kbi.inited){ g_kbi.inited=1; g_kbi.state=1; u8 z=0; kbi_reply(0x0,&z,1); }
        { static int n; if(n++<8) LOG("applet: inline keyboard started\n"); } }
      return 0;
    case 20: case 25: case 30: case 100: case 50: case 60: case 150: return 0;
    case 160: out64(c,0x1C0); return 0;                                   /* GetIndirectLayerConsumerHandle (the keyboard picture) */
    case 103: { SvcObj* st=ipc_in_obj(c,0); if(st){ if(o->u[2]==0x11) kbi_request(o,st); svcobj_unref(st); } return 0; }
    case 104: if(g_kbi.acc==o){
        /* initialized but never shown after 1.5 s, so we open the text window ourselves */
        if(!g_kbi.nq && g_kbi.init_ns && !g_kbi.appeared && !g_kbi.autoshown && !o->u[5] && plat_ns()-g_kbi.init_ns>1500000000ull){ g_kbi.autoshown=1; kbi_type(1); }
        kbi_typing_step();
        if(!g_kbi.nq){ if(g_kbi.ev && !g_kbi.typing) kevent_clear(g_kbi.ev); return RC(128,2); }   /* still typing: stays signaled so the game polls */
        SvcObj* st=g_kbi.q[0]; memmove(g_kbi.q,g_kbi.q+1,(--g_kbi.nq)*sizeof g_kbi.q[0]); if(!g_kbi.nq && g_kbi.ev && !g_kbi.typing) kevent_clear(g_kbi.ev);
        out_obj(c,st); return 0; }
      /* fall through, the normal keyboard and the other applets answer with the normal output */
    case 101: { if(o->u[1]++) return RC(128,2);
      /* applet output. the web applets (Web, Shop, OfflineWeb, LoginShare, WifiWebAuth) give back a 0x1010 byte
         WebCommonReturnValue (exit reason 0, last url, url size) and the callers check that size */
      u32 id=(u32)o->u[2]; u64 n=0x10;
      if(id==0x13 || id==0x14 || id==0x17 || id==0x18 || id==0x19) n=0x1010;
      SvcObj* st;
      if(id==0x11){ /* swkbd: SwkbdResult { u32 result (0 = OK); u16 text[1002]; } = 0x7D8 bytes. on windows the
                       player types it, anywhere else it's "Player" (keyboard_text= in the ini changes that) */
        u8 r[0x7D8]; memset(r,0,sizeof r); { u16 t[64]; int k=swkbd_default(t,63); memcpy(r+4,t,k*2); }
        /* on windows the player types it in a text box over the game (default text already selected) */
        { extern int plat_text_input(const u16* def, u16* out, int max); u16 def[1002], typed[1002]; memcpy(def,r+4,sizeof def); def[1001]=0;
          int k=plat_text_input(def,typed,32);
          if(k>0){ memset(r+4,0,0x7D4); memcpy(r+4,typed,k*2); LOG("applet: keyboard text typed (%d characters)\n",k); } }
        n=sizeof r; st=am_storage_new(n,r); }
      else if(id==0x10){ /* PlayerSelect: UiReturnArg { u64 result; Uid uid; } with the console user. deltarune
                            keeps asking forever if it gets "no user" */
        u8 r[0x18]; memset(r,0,sizeof r); memcpy(r+8,g_user_id,16); n=sizeof r; st=am_storage_new(n,r); }
      else st=am_storage_new(n,NULL);
      { static int said; if(said<4){ said++; LOG("applet: library applet %02x closed right away (no applet UI here), %llu bytes of output\n",id,(unsigned long long)n); } }
      out_obj(c,st); return 0; }
    case 105: { KEvent* e=kevent_new("applet data",0); e->signaled=1; out_copy_h(c,h_new(&e->o)); return 0; }
    /* these applets have no interactive output, so the event stays clear. if it was signaled libnx's join loop
       pops (cmd 104 fails) and waits again forever */
    case 106: { if(o->u[2]==0x11){ kbi_bind(o);
        if(!g_kbi.ev) g_kbi.ev=kevent_new("keyboard interactive data",0); if(g_kbi.nq) g_kbi.ev->signaled=1;
        g_kbi.ev->o.refs++; out_copy_h(c,h_new(&g_kbi.ev->o)); return 0; }
      KEvent* e=kevent_new("applet interactive data",0); out_copy_h(c,h_new(&e->o)); return 0; }
    case 120: out64(c,0); return 0;
  }
  return 0; }

static int am_lac(SvcObj* o, IpcCtx* c){          /* ILibraryAppletCreator */
  switch(c->cmd){
    case 0: case 3: { /* CreateLibraryApplet(id, mode). 3 is the newer one (SDK 20, tomodachi uses it for swkbd)
                         with the same first args, it has to return the object or the game calls through a null
                         pointer */
      SvcObj* a=svcobj_new("ILibraryAppletAccessor",am_lib_accessor,0); a->u[2]=in32(c,0); a->u[3]=in32(c,4); out_obj(c,a);
      { static int said; if(said<6){ said++; LOG("applet: library applet %02x created (cmd %u, mode %u)\n",in32(c,0),c->cmd,in32(c,4)); } }
      return 0; } case 10: out_obj(c,am_storage_new(in64(c,0),NULL)); return 0; case 11: out_obj(c,am_storage_new(in64(c,0),NULL)); return 0; }
  return stub_ok(o,c); }

static int am_audio(SvcObj* o, IpcCtx* c){ (void)o; if(c->cmd==1){ out32(c,0x3F800000); return 0; } if(c->cmd==2){ out32(c,0x3F800000); out32(c,0x3F800000); return 0; } return 0; }

static int am_display(SvcObj* o, IpcCtx* c){ (void)o; (void)c; return 0; }

static int am_debug(SvcObj* o, IpcCtx* c){ (void)o; (void)c; return 0; }

/* Switch 2's IApplicationProxy hands out two more interfaces (commands 40 and 60), one of them
   IGraphicsScalingParametersFunctions. Mario Kart World calls through it (nn::oe::SetGraphicsScaleChangedNotification-
   Enabled) and jumped to 0 when the command gave no object. Every command answers ok; the data starts with 10, the
   scale nn::oe::GetCurrentGraphicsScale accepts (10, 20 or 30, anything else aborts) */
static int am_sw2_extra(SvcObj* o, IpcCtx* c){
  if(ipc_warn_once("am-sw2",((u32)(uintptr_t)o->name<<8)^c->cmd)) LOG("applet: %s cmd %u (switch 2, answered ok)\n",o->name,c->cmd);
  out32(c,10); out32(c,0); out32(c,0); out32(c,0); return 0; }

/* chat:u (Switch 2 GameChat). Command 0 hands out the user service; on it command 1 gives the "chatting" event that
   nn::chat::IsChatting polls (it waited on handle 0 without one). Nobody chats here, so it never fires */
static int chat_user(SvcObj* o, IpcCtx* c){
  if(c->cmd==1){ static KEvent* ev; if(!ev){ ev=kevent_new("chat state",0); kobj_ref(&ev->o); } ev->o.refs++; out_copy_h(c,h_new(&ev->o)); return 0; }
  return quiet_ok(o,c); }
static int chat_u(SvcObj* o, IpcCtx* c){ if(c->cmd==0){ out_obj(c,svcobj_new("IChatUserService",chat_user,0)); return 0; } return quiet_ok(o,c); }
static SvcObj* new_chat_u(void){ return svcobj_new("chat:u",chat_u,0); }

static int am_proxy(SvcObj* o, IpcCtx* c){        /* IApplicationProxy */
  switch(c->cmd){
    case 0: out_obj(c,svcobj_new("ICommonStateGetter",am_csg,0)); return 0;
    case 1: out_obj(c,svcobj_new("ISelfController",am_self,0)); return 0;
    case 2: out_obj(c,svcobj_new("IWindowController",am_window,0)); return 0;
    case 3: out_obj(c,svcobj_new("IAudioController",am_audio,0)); return 0;
    case 4: out_obj(c,svcobj_new("IDisplayController",am_display,0)); return 0;
    case 10: out_obj(c,quiet("IProcessWindingController")); return 0;
    case 11: out_obj(c,svcobj_new("ILibraryAppletCreator",am_lac,0)); return 0;
    case 20: out_obj(c,svcobj_new("IApplicationFunctions",am_appfn,0)); return 0;
    case 1000: out_obj(c,svcobj_new("IDebugFunctions",am_debug,0)); return 0;
    case 40: case 60: if((g_title_id>>56)==0x04){ out_obj(c,svcobj_new(c->cmd==60? "IApplicationProxy60" : "IApplicationProxy40",am_sw2_extra,0)); return 0; } break;
  }
  return stub_ok(o,c); }

static int am_oe(SvcObj* o, IpcCtx* c){
  /* Switch 2 opens the proxy with cmd 10 */
  if(c->cmd==0 || c->cmd==10){ out_obj(c,svcobj_new("IApplicationProxy",am_proxy,0)); return 0; }
  return stub_ok(o,c); }

static SvcObj* new_appletoe(void){ return svcobj_new("appletOE",am_oe,0); }

static SvcObj* new_appletae(void){ return svcobj_new("appletAE",am_oe,0); }

/* ================================================================ set */
static int set_disp(SvcObj* o, IpcCtx* c){
  static const char* codes[]={"ja","en-US","fr","de","it","es","zh-CN","ko","nl","pt","ru","zh-TW","en-GB","fr-CA","es-419","zh-Hans","zh-Hant","pt-BR"};
  switch(c->cmd){
    case 0: { u64 v=0; const char* s=codes[g_opt_lang%18]; memcpy(&v,s,strlen(s)); out64(c,v); return 0; }     /* GetLanguageCode */
    case 1: case 5: { u64 a,s; buf_out(c,0,&a,&s); u32 n=(u32)(s/8); u32 max= c->cmd==1? 15 : 18; if(n>max) n=max;
      for(u32 i=0;i<n;i++){ u64 v=0; memcpy(&v,codes[i],strlen(codes[i])); gw64(a+i*8,v); } out32(c,n); return 0; }
    case 2: { u32 idx=in32(c,0); u64 v=0; if(idx<18) memcpy(&v,codes[idx],strlen(codes[idx])); out64(c,v); return 0; }   /* MakeLanguageCode */
    case 3: out32(c,15); return 0;
    case 6: out32(c,18); return 0;
    case 4: out32(c,1); return 0;                     /* GetRegionCode: usa */
    case 7: case 9: { u64 a,s; buf_out(c,0,&a,&s); memset(GP(a),0,s); return 0; }
    case 8: out32(c,0); return 0;
    case 11: { u64 a,s; buf_out(c,0,&a,&s); memset(GP(a),0,s); strcpy((char*)GP(a),"SwitchRecomp"); return 0; }
  }
  return stub_ok(o,c); }

static SvcObj* new_set(void){ return svcobj_new("set",set_disp,0); }

static int setsys_disp(SvcObj* o, IpcCtx* c){
  switch(c->cmd){
    case 3: case 4: { u64 a,s; buf_out(c,0,&a,&s); u8 fw[0x100]; memset(fw,0,sizeof fw); fw[0]=12; fw[1]=1; fw[2]=0; fw[4]=12; fw[5]=1; fw[6]=0; fw[7]=0;
      strcpy((char*)fw+8,"NintendoSDK Firmware for NX"); strcpy((char*)fw+0x28,"12.1.0-1.0"); strcpy((char*)fw+0x68,"12.1.0"); strcpy((char*)fw+0x80,"NintendoSDK Firmware for NX 12.1.0-1.0");
      memcpy(GP(a),fw,s<0x100?s:0x100); return 0; }
    case 23: out32(c,0); return 0;                  /* GetColorSetId */
    case 38: case 62: out32(c,0); return 0;
    case 37: { u64 a,s; buf_out(c,0,&a,&s); memset(GP(a),0,s); out64(c,0); return 0; }  /* GetSettingsItemValueSize */
    case 90: case 91: out32(c,0); return 0;
  }
  return quiet_ok(o,c); }

static SvcObj* new_setsys(void){ return svcobj_new("set:sys",setsys_disp,0); }

/* ================================================================ time */
static KShmem* g_time_shm;

static int sysclock_disp(SvcObj* o, IpcCtx* c){
  switch(c->cmd){
    case 0: out64(c,(u64)plat_unix_time()); return 0;
    case 1: return 0;
    case 2: { u8 ctx[0x20]; memset(ctx,0,sizeof ctx); i64 t=plat_unix_time(); memcpy(ctx,&t,8); outbytes(c,ctx,0x20); return 0; }
    case 3: return 0;
    case 4: out_copy_h(c,ev_handle(kevent_new("clock op",0))); return 0;   /* GetOperationEventReadableHandle */
  }
  return stub_ok(o,c); }

static u8 g_clock_id[16]={1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16};

static int steady_disp(SvcObj* o, IpcCtx* c){
  switch(c->cmd){
    case 0: { u64 s=plat_ns()/1000000000ull; out64(c,s); outbytes(c,g_clock_id,16); return 0; }
    case 2: case 3: out64(c,0); return 0;
    case 100: out64(c,0); return 0;
    case 200: out64(c,0); out64(c,0); return 0;
    case 300: out64(c,0); return 0;
  }
  return stub_ok(o,c); }

static i64 g_tz_off;

static i64 days_from_civil(i64 y, unsigned m, unsigned d){
  y-= m<=2; i64 era=(y>=0?y:y-399)/400; unsigned yoe=(unsigned)(y-era*400);
  unsigned doy=(153*(m+(m>2?-3:9))+2)/5+d-1; unsigned doe=yoe*365+yoe/4-yoe/100+doy; return era*146097+(i64)doe-719468; }

/* posix time (already in local time) -> CalendarTime (8 bytes) + CalendarAdditionalInfo (0x18) */
static void calendar_of(i64 t, u8* cal, u8* add){
  i64 days=t/86400, rem=t%86400; if(rem<0){ rem+=86400; days--; }
  int hh=(int)(rem/3600), mm=(int)(rem%3600/60), ss=(int)(rem%60);
  /* days -> y/m/d */
  i64 z=days+719468; i64 era=(z>=0?z:z-146096)/146097; unsigned doe=(unsigned)(z-era*146097);
  unsigned yoe=(doe-doe/1460+doe/36524-doe/146096)/365; i64 y=(i64)yoe+era*400; unsigned doy=doe-(365*yoe+yoe/4-yoe/100);
  unsigned mp=(5*doy+2)/153; unsigned d=doy-(153*mp+2)/5+1; unsigned m=mp<10?mp+3:mp-9; y+= m<=2;
  u16 yy=(u16)y; memcpy(cal,&yy,2); cal[2]=(u8)m; cal[3]=(u8)d; cal[4]=(u8)hh; cal[5]=(u8)mm; cal[6]=(u8)ss; cal[7]=0;
  u32 wday=(u32)((days%7+11)%7), yday=(u32)(days-days_from_civil(y,1,1)); char tz[8]="UTC"; i32 off=(i32)g_tz_off; u32 dst=0;
  memcpy(add,&wday,4); memcpy(add+4,&yday,4); memcpy(add+8,tz,8); memcpy(add+16,&dst,4); memcpy(add+20,&off,4); }

static void to_calendar(i64 t, IpcCtx* c){ u8 cal[8], add[0x18]; calendar_of(t,cal,add); outbytes(c,cal,8); outbytes(c,add,0x18); }

/* nn::time::ClockSnapshot (0xD0): user and network SystemClockContext {i64 offset; i64 time_point; u8 id[16]}, their
   posix times, calendar times and extra info (local), the steady time point, location name, the automatic correction
   flag and the type. without it the game gets a zeroed date */
static void clock_snapshot(u8* p, u8 type, const u8* uctx, const u8* nctx){
  { static int tzi; if(!tzi){ tzi=1; if(!g_tz_off) g_tz_off=plat_tz_offset(); } }   /* the time zone service may not have run yet */
  i64 steady=(i64)(plat_ns()/1000000000ull), now=plat_unix_time();
  u8 own[0x20]; { i64 off=now-steady; memcpy(own,&off,8); memcpy(own+8,&steady,8); memcpy(own+16,g_clock_id,16); }
  memset(p,0,0xD0); memcpy(p,uctx? uctx : own,0x20); memcpy(p+0x20,nctx? nctx : own,0x20);
  for(int k=0;k<2;k++){ const u8* x=p+k*0x20; i64 off; memcpy(&off,x,8);
    i64 t= !memcmp(x+16,g_clock_id,16)? off+steady : now;   /* a context from another steady clock: just the PC time */
    memcpy(p+0x40+k*8,&t,8); calendar_of(t+g_tz_off,p+0x50+k*8,p+0x60+k*0x18); }
  memcpy(p+0x90,&steady,8); memcpy(p+0x98,g_clock_id,16);
  strcpy((char*)p+0xA8,"UTC"); p[0xCC]=1; p[0xCD]=type; }

static int tz_disp(SvcObj* o, IpcCtx* c){
  { static int init; if(!init){ init=1; g_tz_off=plat_tz_offset(); LOG("time: PC time zone UTC%+.1f\n",g_tz_off/3600.0); } }
  switch(c->cmd){
    case 0: { char n[0x24]; memset(n,0,sizeof n); strcpy(n,"UTC"); outbytes(c,n,0x24); return 0; }
    case 1: return 0;
    case 2: out32(c,1); return 0;
    case 3: { out32(c,1); return 0; }
    case 4: { u64 a,s; buf_out(c,0,&a,&s); memset(GP(a),0,s); return 0; }
    case 5: { char v[16]="2021a"; outbytes(c,v,16); return 0; }
    /* guest wall clock = host local time */
    case 100: case 101: { i64 t=(i64)in64(c,0)+g_tz_off; to_calendar(t,c); return 0; }
    case 201: case 202: { u64 a,s; buf_out(c,0,&a,&s); /* rough inverse */
      u16 y; memcpy(&y,c->raw,2); u8 mo=c->raw[2], d=c->raw[3], h=c->raw[4], mi=c->raw[5], se=c->raw[6];
      i64 yy=y-(mo<=2); i64 era=(yy>=0?yy:yy-399)/400; unsigned yoe=(unsigned)(yy-era*400); unsigned doy=(153*(mo+(mo>2?-3:9))+2)/5+d-1;
      unsigned doe=yoe*365+yoe/4-yoe/100+doy; i64 days=era*146097+(i64)doe-719468; i64 t=days*86400+h*3600+mi*60+se;
      t-=g_tz_off; if(a && s>=8) gw64(a,(u64)t); out32(c,1); return 0; }
  }
  return stub_ok(o,c); }

static void time_shm_update(void){
  if(!g_time_shm) return; u8* p=kshmem_ptr(g_time_shm);
  /* steady clock {i64 base_time_ns; u8 id[16]} x2 at 0x08/0x20, system clocks {i64 offset; i64 time_point; u8
     id[16]} x2 */
  u32 cnt=0; memcpy(p,&cnt,4);
  for(int k=0;k<2;k++){ i64 base=0; memcpy(p+8+k*0x18,&base,8); memcpy(p+8+k*0x18+8,g_clock_id,16); }
  extern u64 g_t0_ns(void);
  i64 elapsed=(i64)((plat_ns()-g_t0_ns())/1000000000ull);
  i64 off=plat_unix_time()-elapsed;
  for(int c2=0;c2<2;c2++){ u8* q=p+(c2? 0x80 : 0x38); memcpy(q,&cnt,4);
    for(int k=0;k<2;k++){ u8* e=q+8+k*0x20; i64 tp=0; memcpy(e,&off,8); memcpy(e+8,&tp,8); memcpy(e+16,g_clock_id,16); } }
  /* auto correction {u32 counter; bool[2]} at 0xC8 */
  memcpy(p+0xC8,&cnt,4); p[0xCC]=1; p[0xCD]=1;
  /* ContinuousAdjustmentTimePoint (17.0+) {u32 counter; pad; 2 x {rtc_offset, diff_scale, shift+pad, lower{t,id},
     upper{t,id}}} at 0xD0 */
  memcpy(p+0xD0,&cnt,4);
  for(int k=0;k<2;k++){ u8* e=p+0xD8+k*0x48; memset(e,0,0x48); memcpy(e+0x18+8,g_clock_id,16); memcpy(e+0x30+8,g_clock_id,16); }
}

static int time_disp(SvcObj* o, IpcCtx* c){
  switch(c->cmd){
    case 0: case 1: case 4: out_obj(c,svcobj_new("ISystemClock",sysclock_disp,0)); return 0;
    case 2: out_obj(c,svcobj_new("ISteadyClock",steady_disp,0)); return 0;
    case 3: out_obj(c,svcobj_new("ITimeZoneService",tz_disp,0)); return 0;
    case 5: out_obj(c,svcobj_new("IEphemeralNetworkSystemClock",sysclock_disp,0)); return 0;
    case 20: { if(!g_time_shm){ g_time_shm=kshmem_new(0x1000,"time"); kobj_ref(&g_time_shm->o); time_shm_update(); } out_copy_h(c,h_new(&g_time_shm->o)); return 0; }
    case 100: case 101: out8(c,1); return 0;
    case 200: out8(c,1); return 0;
    case 300: { i64 t=plat_unix_time(); out64(c,(u64)t); return 0; }
    case 400: case 401: { u64 a,n; buf_out(c,0,&a,&n); if(!a || n<0xD0) return 0;   /* GetClockSnapshot(FromSystemClockContext) */
      u8 snap[0xD0]; clock_snapshot(snap,c->raw[0],c->cmd==401? c->raw+8 : NULL,c->cmd==401? c->raw+0x28 : NULL); memcpy(GP(a),snap,0xD0); return 0; }
    case 500: case 501: { u64 a0,n0,a1,n1; buf_in(c,0,&a0,&n0); buf_in(c,1,&a1,&n1); i64 span=0;
      if(a0 && a1 && n0>=0xD0 && n1>=0xD0){ const u8* x=GP(a0); const u8* y=GP(a1); i64 t0,t1;
        if(c->cmd==500){ memcpy(&t0,x+0x40,8); memcpy(&t1,y+0x40,8); }   /* user clock difference */
        else if(!memcmp(x+0x98,y+0x98,16)){ memcpy(&t0,x+0x90,8); memcpy(&t1,y+0x90,8); }   /* CalculateSpanBetween: steady if the same clock */
        else { memcpy(&t0,x+0x48,8); memcpy(&t1,y+0x48,8); }
        span=(t1-t0)*1000000000ll; }
      out64(c,(u64)span); return 0; }
  }
  return stub_ok(o,c); }

static SvcObj* new_time(void){ return svcobj_new("time",time_disp,0); }

/* ================================================================ acc */
static int profile_disp(SvcObj* o, IpcCtx* c){
  switch(c->cmd){
    case 0: case 1: {
      if(c->cmd==0){ u64 a,s; buf_out(c,0,&a,&s); if(a){ memset(GP(a),0,s); } }
      u8 base[0x38]; memset(base,0,sizeof base); memcpy(base,g_user_id,16); u64 ts=1600000000; memcpy(base+0x10,&ts,8); strcpy((char*)base+0x18,"Player");
      outbytes(c,base,0x38); return 0; }
    case 10: out32(c,0); return 0;
    case 11: out32(c,0); return 0;
  }
  return stub_ok(o,c); }

/* IManagerForApplication, the network service side of a user. there's no NSA on pc so CheckAvailability says "not
   available" (same as yuzu) and the account id is just a fixed non-zero value */
static int accmgr_disp(SvcObj* o, IpcCtx* c){
  switch(c->cmd){
    case 0: out8(c,0); return 0;                        /* CheckAvailability */
    case 1: out64(c,0x0123456789ABCDEFull); return 0;   /* GetAccountId */
  }
  return stub_ok(o,c); }

static SvcObj* new_accmgr(void){ return svcobj_new("IManagerForApplication",accmgr_disp,0); }

static int acc_disp(SvcObj* o, IpcCtx* c){
  switch(c->cmd){
    case 0: out32(c,1); return 0;
    case 1: out8(c,1); return 0;
    case 2: case 3: { u64 a,s; buf_out(c,0,&a,&s); if(a){ memset(GP(a),0,s); if(s>=16) memcpy(GP(a),g_user_id,16); } return 0; }
    case 4: outbytes(c,g_user_id,16); return 0;
    case 5: out_obj(c,svcobj_new("IProfile",profile_disp,0)); return 0;
    case 50: out8(c,0); return 0;
    case 51: outbytes(c,g_user_id,16); return 0;
    case 60: out32(c,1); return 0;
    case 100: case 140: case 111: return 0;
    case 150: out8(c,0); return 0;   /* IsUserAccountSwitchLocked */
    case 101: out_obj(c,new_accmgr()); return 0;
    case 110: return 0;
    /* LoadOpenContext gives back the manager of the user the game started with. splatoon 3 calls through it in
       IsNetworkServiceAccountAvailable */
    case 130: out_obj(c,new_accmgr()); return 0;
    /* ListOpenContextStoredUsers: the user the game started with and the rest of the list zeroed.
       nn::account::PopOpenUsers counts the non-zero entries and aborts if there's more than it asked for
       (bayonetta 3 at boot, it had stack garbage in the buffer) */
    case 131: { u64 a,s; buf_out(c,0,&a,&s); if(a && s){ memset(GP(a),0,s); if(s>=16) memcpy(GP(a),g_user_id,16); } return 0; }
  }
  return stub_ok(o,c); }

static SvcObj* new_acc(void){ return svcobj_new("acc:u0",acc_disp,0); }

/* ================================================================ ldr:ro / ro:1 (nn::ro)
   for games that load .nro modules from their romfs while running (super mario party). the SDK reads the file
   into a buffer and asks ro to map it plus a bss buffer as code, relocation and init happen inside the SDK. if
   the recompiler already compiled that module from the romfs it goes to its compiled base (matched by build id),
   anything else goes to a free address and runs in the interpreter */
typedef struct { u64 base, size; } RoMap;

static RoMap g_ro[64]; static PMutex g_ro_lk;

static u64 ro_map(u64 nro, u64 nro_size, u64 bss, u64 bss_size){
  if(nro_size<0x80 || (nro|nro_size|bss_size)&0xFFF) return 0;
  const u8* h=GP(nro); if(memcmp(h+0x10,"NRO0",4)) return 0;
  u64 tot=nro_size+bss_size, base=0; const SwrModInfo* mi=NULL;
  for(u32 i=0;i<g_mod->nmods;i++){ const SwrModInfo* m=&g_mod->mods[i];
    if(m->is_nro==2 && !memcmp(m->build_id,h+0x40,32) && tot<=m->size){ mi=m; break; } }
  if(mi && !mem_map(mi->base,tot,MS_CODE,PERM_RW)) base=mi->base;
  if(!base){ u64 lo=(g_code_hi+0x1FFFFFull)&~0x1FFFFFull;
    for(int tries=0;tries<8 && !base;tries++){ u64 a=mem_find_free(lo,HEAP_BASE,tot+0x2000,0x200000); if(!a) break;
      if(!mem_map(a,tot,MS_CODE,PERM_RW)) base=a; else lo=a+0x200000; } }
  if(!base) return 0;
  memcpy(GP(base),GP(nro),nro_size);
  if(bss_size) memset(GP(base+nro_size),0,bss_size);
  u32 seg[6]; memcpy(seg,h+0x20,24);   /* text, ro, data: offset/size */
  mem_set_state(base+seg[0],(seg[1]+0xFFF)&~0xFFFu,MS_CODE,PERM_RX);
  mem_set_state(base+seg[2],(seg[3]+0xFFF)&~0xFFFu,MS_CODE,PERM_R);
  mem_set_state(base+seg[4],tot-seg[4],MS_CODEDATA,PERM_RW);
  pm_lock(&g_ro_lk); for(int i=0;i<64;i++) if(!g_ro[i].base){ g_ro[i].base=base; g_ro[i].size=tot; break; } pm_unlock(&g_ro_lk);
  LOG("ro: module %02x%02x%02x%02x... mapped at %llx (%.1f MB, %s)\n",h[0x40],h[0x41],h[0x42],h[0x43],(unsigned long long)base,tot/1048576.0,
      base==(mi? mi->base : 0)? "recompiled" : "interpreted, not in the recompiled code");
  return base; }

static int ro_disp(SvcObj* o, IpcCtx* c){
  switch(c->cmd){
    case 0: { u64 a=ro_map(in64(c,8),in64(c,16),in64(c,24),in64(c,32)); if(!a) return RC(22,4); out64(c,a); return 0; }   /* MapManualLoadModuleMemory */
    case 1: { u64 a=in64(c,8);                                                                                              /* UnmapManualLoadModuleMemory */
      pm_lock(&g_ro_lk); for(int i=0;i<64;i++) if(g_ro[i].base==a){ mem_unmap(a,g_ro[i].size); g_ro[i].base=0; break; } pm_unlock(&g_ro_lk);
      return 0; }
    case 2: case 3: case 4: case 10: return 0;   /* (Un)RegisterModuleInfo (.nrr), RegisterProcessHandle, RegisterProcessModuleInfo */
  }
  return stub_ok(o,c); }

static SvcObj* new_ro(void){ return svcobj_new("ldr:ro",ro_disp,0); }

/* ================================================================ apm and misc */
static int apm_session(SvcObj* o, IpcCtx* c){ (void)o; if(c->cmd==1) out32(c,0x00020003); return 0; }

static int apm_disp(SvcObj* o, IpcCtx* c){
  switch(c->cmd){ case 0: out_obj(c,svcobj_new("apm:ISession",apm_session,0)); return 0; case 1: out32(c,(u32)g_opt_docked); return 0; case 6: out8(c,0); return 0; }
  return stub_ok(o,c); }

static SvcObj* new_apm(void){ return svcobj_new("apm",apm_disp,0); }

static int lm_logger(SvcObj* o, IpcCtx* c){
  (void)o;
  if(c->cmd==0){ u64 a,s; buf_in(c,0,&a,&s); if(a && s>0x18){ /* lm packet: 0x18 hdr, then (type,len,data) fields */
      u8* p=GP(a); u64 i=0x18; char msg[1024]; int n=0;
      while(i+2<s){ u8 t=p[i], l=p[i+1]; if(i+2+l>s) break; if(t==2 && n+l<1000){ memcpy(msg+n,p+i+2,l); n+=l; } i+=2+l; }
      if(n){ msg[n]=0; LOG("[game lm] %s%s",msg,(msg[n-1]=='\n')?"":"\n"); } } }
  return 0; }

static int lm_disp(SvcObj* o, IpcCtx* c){ if(c->cmd==0){ out_obj(c,svcobj_new("ILogger",lm_logger,0)); return 0; } return quiet_ok(o,c); }

static SvcObj* new_lm(void){ return svcobj_new("lm",lm_disp,0); }

static int pctl_obj(SvcObj* o, IpcCtx* c){ (void)o;
  switch(c->cmd){ case 1001: case 1002: case 1004: return 0; case 1031: out8(c,0); return 0; case 1032: out32(c,0); return 0; case 1403: out8(c,0); return 0;
    case 1018: out8(c,1); return 0;                                    /* IsFreeCommunicationAvailable */
    case 1039: out32(c,0); return 0;
    case 1065: out8(c,1); return 0;                                    /* IsStereoVisionPermitted */
    case 1453: out8(c,0); return 0;                                    /* IsPlayTimerEnabled */
    case 1473: out8(c,0); return 0;
    case 1432: case 1433: case 1434: case 1457: out_copy_h(c,ev_handle(kevent_new("pctl ev",0))); return 0; }
  return 0; }

static int pctl_disp(SvcObj* o, IpcCtx* c){ if(c->cmd==0||c->cmd==1){ out_obj(c,svcobj_new("IParentalControlService",pctl_obj,0)); return 0; } return quiet_ok(o,c); }

static SvcObj* new_pctl(void){ return svcobj_new("pctl",pctl_disp,0); }

static int nifm_req(SvcObj* o, IpcCtx* c){ (void)o;
  switch(c->cmd){ case 0: out32(c,1); return 0; case 1: return RC(110,300);
    case 2: { KEvent* a=kevent_new("nifm0",0); KEvent* b=kevent_new("nifm1",0); a->signaled=1; out_copy_h(c,ev_handle(a)); out_copy_h(c,ev_handle(b)); return 0; }
    case 3: case 4: case 5: case 6: case 11: case 21: return 0; }
  return 0; }

static int nifm_gen(SvcObj* o, IpcCtx* c){ (void)o;
  switch(c->cmd){ case 4: out_obj(c,svcobj_new("IRequest",nifm_req,0)); return 0; case 2: out_obj(c,svcobj_new("IScanRequest",nifm_req,0)); return 0; case 5: case 12: return RC(110,300);
    case 18: out32(c,0); return 0; case 21: out8(c,0); return 0; case 22: out8(c,0); return 0; case 1: outbytes(c,"\x01\x02\x03\x04\x05\x06\x07\x08\x09\x0a\x0b\x0c\x0d\x0e\x0f\x10",16); return 0; }
  return 0; }

static int nifm_disp(SvcObj* o, IpcCtx* c){ if(c->cmd==4||c->cmd==5){ out_obj(c,svcobj_new("IGeneralService",nifm_gen,0)); return 0; } return quiet_ok(o,c); }

static SvcObj* new_nifm(void){ return svcobj_new("nifm",nifm_disp,0); }

static int friend_svc(SvcObj* o, IpcCtx* c){ (void)o; if(c->cmd==0){ out_copy_h(c,ev_handle(kevent_new("friend",0))); return 0; } if(c->cmd>=10100 && c->cmd<=10102){ out32(c,0); return 0; } return 0; }

static int friend_notif(SvcObj* o, IpcCtx* c){ (void)o; if(c->cmd==0){ out_copy_h(c,ev_handle(kevent_new("friend notif",0))); return 0; } if(c->cmd==2) return RC(121,15); return 0; }

static int friend_disp(SvcObj* o, IpcCtx* c){ if(c->cmd==0){ out_obj(c,svcobj_new("IFriendService",friend_svc,0)); return 0; } if(c->cmd==1){ out_obj(c,svcobj_new("INotificationService",friend_notif,0)); return 0; }
  if(c->cmd==2){ out_obj(c,quiet("IDaemonSuspendSessionService")); return 0; } return quiet_ok(o,c); }

static SvcObj* new_friend(void){ return svcobj_new("friend",friend_disp,0); }

static int ns_disp(SvcObj* o, IpcCtx* c){ (void)o;
  switch(c->cmd){ case 7996: case 7989: case 7995: case 7988: case 7994: case 7997: case 7998: case 7999: case 7991: out_obj(c,quiet("ns:sub")); return 0; }
  return 0; }

static SvcObj* new_ns(void){ return svcobj_new("ns",ns_disp,0); }

/* audio: pretend, no output */
static KEvent* g_aud_ev;
static int g_aud_catchup;
/* a late AUX renderer catches up one guest turn at a time. the event has to be signaled again even if its normal
   timer wakeups got merged */
void audren_signal_ready(int ready){ __atomic_store_n(&g_aud_catchup,ready,__ATOMIC_RELEASE); if(ready && g_aud_ev) kevent_signal(g_aud_ev); }
static void aout_tick(void);

/* renderer event fires every 5 ms (240 samples at 48k) like on HOS */
static void audio_clock(void* arg){ (void)arg; extern u64 guest_ns(void); u64 next=guest_ns();
  for(;;){ next+=5000000ull;
    u64 now; while((now=guest_ns())<next){
      /* SDKs can reset the event after RequestUpdate, so pending work stays visible until the renderer acks its
         sample deadline */
      if(__atomic_load_n(&g_aud_catchup,__ATOMIC_ACQUIRE)) kevent_signal(g_aud_ev);
      u64 remaining=next-now; plat_sleep_ns((i64)(remaining>1000000?1000000:remaining)); }
    if(now-next>50000000ull) next=now;
    kevent_signal(g_aud_ev);
  }
}

static int audren_obj(SvcObj* o, IpcCtx* c){
  extern int audren_update(SvcObj* o, IpcCtx* c);
  switch(c->cmd){
    case 0: out32(c,(u32)o->u[0]); return 0;
    case 1: out32(c,(u32)o->u[1]); return 0;
    case 2: out32(c,(u32)o->u[2]); return 0;
    case 3: out32(c,(u32)o->u[3]); return 0;
    case 4: case 10: return audren_update(o,c);
    case 5: o->u[3]=0; o->u[6]=0; return 0;
    case 6: o->u[3]=1; o->u[6]=0; audren_signal_ready(0); return 0;
    case 7: out_copy_h(c,ev_handle(g_aud_ev)); return 0;
    case 8: case 9: return 0;
    case 11: out32(c,0); return 0;
  }
  return quiet_ok(o,c); }

static int auddev_disp(SvcObj* o, IpcCtx* c){ (void)o;
  static const char* nm="AudioTvOutput";
  switch(c->cmd){
    case 0: case 6: { u64 a,s; if(buf_out(c,0,&a,&s) && a && s>=0x100){ memset(GP(a),0,0x100); strcpy((char*)GP(a),nm); out32(c,1); } else out32(c,0); return 0; }
    case 2: case 8: out32(c,0x3F800000); return 0;
    case 3: case 10: case 13: { u64 a,s; if(buf_out(c,0,&a,&s) && a){ memset(GP(a),0,s); strncpy((char*)GP(a),nm,s); } return 0; }
    case 4: case 11: case 12: { KEvent* e=kevent_new("audio device",0); e->signaled=1; out_copy_h(c,ev_handle(e)); return 0; }
    case 5: out32(c,2); return 0;
  }
  return 0; }

static int audren_disp(SvcObj* o, IpcCtx* c){
  switch(c->cmd){
    case 0: { SvcObj* r=svcobj_new("IAudioRenderer",audren_obj,0x100); r->destroy=swr_audio_destroy;
      memcpy(r->data,c->raw,0x34<0x100?0x34:0x100);
      r->u[0]=in32(c,0); r->u[1]=in32(c,4); r->u[2]=in32(c,8); r->u[3]=1;
      out_obj(c,r); return 0; }
    case 1: { u64 sz=0x4000; u32 voices=in32(c,0x10), sinks=in32(c,0x14), effects=in32(c,0x1C); sz+= (u64)voices*0x400 + sinks*0x200 + effects*0x800 + 0x40000; out64(c,sz); return 0; }
    case 2: case 4: out_obj(c,svcobj_new("IAudioDevice",auddev_disp,0)); return 0;
  }
  return quiet_ok(o,c); }

static SvcObj* new_audren(void){ return svcobj_new("audren:u",audren_disp,0); }
/* aud:u (Switch 2): the audio entry point. Command 2 hands out the renderer manager, the same one audren:u is */
static int aud_u(SvcObj* o, IpcCtx* c){ if(c->cmd==2){ out_obj(c,svcobj_new("IAudioRendererManager",audren_disp,0)); return 0; } return quiet_ok(o,c); }
static SvcObj* new_aud_u(void){ return svcobj_new("aud:u",aud_u,0); }

/* audout: send the guest's PCM16 buffers to the shared output/recording backend. the guest owns the buffers until
   their samples get played */
#define AOUT_MAX 32
typedef struct AudOut {
  struct AudOut* next;
  KEvent* ev;
  int started;
  u64 tag[AOUT_MAX], dur[AOUT_MAX], address[AOUT_MAX], frames[AOUT_MAX]; int nq;   /* queued, oldest first */
  u64 rel[AOUT_MAX]; int nrel;                /* played, waiting for GetReleased */
  u64 deadline, cursor;                         /* next 5ms quantum and where we are in the first buffer */
  float volume,peak; u64 status_time; u32 bad_reads;
  u64 played;                                 /* samples */
  u32 channels;                               /* what OpenAudioOut answered: 2 or 6 */
} AudOut;

static AudOut* g_aouts;
static PMutex g_aout_lk;

/* PCM16 at 48 kHz with the channel count we told the game in OpenAudioOut */
static u64 aout_ns(u64 bytes, u32 ch){ return bytes/(2ull*(ch? ch : 2))*1000000000ull/48000; }

/* call with g_aout_lk held */
static void aout_pop(AudOut* a){
  a->rel[a->nrel++]=a->tag[0]; a->nq--; a->cursor=0;
  memmove(a->tag,a->tag+1,a->nq*8); memmove(a->dur,a->dur+1,a->nq*8);
  memmove(a->address,a->address+1,a->nq*8); memmove(a->frames,a->frames+1,a->nq*8);
}
static int aout_advance(AudOut* a, u64 now){
  int moved=0;
  if(!a->started || !a->nq) return 0;
  if(!a->deadline) a->deadline=now+5000000ull;
  for(unsigned tick=0;tick<200 && a->nq && now>=a->deadline;tick++){
    float pcm[SWR_AUDIO_FRAMES*2]={0}; unsigned used=0;
    while(used<SWR_AUDIO_FRAMES && a->nq && a->nrel<AOUT_MAX){
      u64 left=a->frames[0]-a->cursor;
      unsigned take=(unsigned)(left>SWR_AUDIO_FRAMES-used?SWR_AUDIO_FRAMES-used:left);
      if(take){
        if(!swr_audio_read_pcm16(a->address[0]+a->cursor*a->channels*2,take,a->channels,a->volume,pcm+used*2)) a->bad_reads++;
        for(unsigned j=0;j<take*2;j++){ float level=fabsf(pcm[used*2+j]); if(level>a->peak) a->peak=level; }
        used+=take; a->cursor+=take; a->played+=take;
      }
      if(a->cursor==a->frames[0]){ aout_pop(a); moved=1; }
    }
    if(!used) break;
    swr_audio_submit_at(pcm,SWR_AUDIO_FRAMES,a->deadline);
    a->deadline+=5000000ull;
    if(!a->nq) a->deadline=0;
  }
  return moved;
}
static void aout_tick(void){
  extern u64 guest_ns(void); u64 now=guest_ns();
  pm_lock(&g_aout_lk);
  for(AudOut* a=g_aouts;a;a=a->next){
    if(aout_advance(a,now)) kevent_signal(a->ev);
    if(!a->status_time || now-a->status_time>=5000000000ull){ a->status_time=now;
      LOG("audout: state=%s queued=%d released=%d played=%llu peak=%.5f unreadable=%u volume=%.3f\n",a->started?"started":"stopped",a->nq,a->nrel,(unsigned long long)a->played,(double)a->peak,a->bad_reads,(double)a->volume); a->peak=0; }
  }
  pm_unlock(&g_aout_lk);
}

/* PCM output can't depend on audren's renderer event or who waits on it. service polling and the frontend share
   the same locked playback deadlines */
void swr_audout_tick(void){ aout_tick(); }
static void aout_clock(void* arg){ (void)arg; for(;;){ aout_tick(); plat_sleep_ns(2500000); } }

static void aout_destroy(SvcObj* o){
  AudOut* a=o->data;
  pm_lock(&g_aout_lk);
  for(AudOut** p=&g_aouts; *p; p=&(*p)->next) if(*p==a){ *p=a->next; break; }
  pm_unlock(&g_aout_lk);
  o->data=NULL; free(a); }

static int audout_obj(SvcObj* o, IpcCtx* c){
  AudOut* a=o->data; int r=0;
  pm_lock(&g_aout_lk);
  {static unsigned seen[16]; if(c->cmd<16 && seen[c->cmd]++<2) LOG("audout: command %u queued=%d started=%d\n",c->cmd,a->nq,a->started); }

  switch(c->cmd){
    case 0: out32(c,a->started? 0 : 1); break;                 /* GetAudioOutState: 0 started, 1 stopped */
    case 1: {extern u64 guest_ns(void); a->started=1; LOG("audout: START (%d buffers)\n",a->nq); if(a->nq && !a->deadline) a->deadline=guest_ns()+5000000ull; break; }
    case 2: LOG("audout: STOP\n"); a->started=0; a->deadline=0; break;
    case 3: case 7: {                                          /* AppendAudioOutBuffer(Auto) */
      u64 tag=in64(c,0),b,n,bytes=0,cap=0,address=0;
      if(buf_in(c,0,&b,&n) && b && n>=0x20){ address=gr64(b+8); cap=gr64(b+0x10); bytes=gr64(b+0x18); }
      /* the service uses Data/DataSize. the linked list and trailing offset fields belong to the client and
         official SDKs can leave junk in them */
      if(a->nq==AOUT_MAX){ r=RC(153,8); break; }
      if(!address || !bytes || !cap || bytes>cap || address>=AS_SIZE || bytes>AS_SIZE-address || bytes>(64ull<<20)){
        r=RC(153,4); break;
      }
      u64 frames=bytes/(2*a->channels); if(!frames){ r=RC(153,4); break; }
      u64 d=aout_ns(bytes,a->channels);
      {static int said; if(said<6){ said++; LOG("audout: playing PCM16 %u channels, %llu frames (%llu us), tag=%llx data=%llx bytes=%llu\n",a->channels,(unsigned long long)frames,(unsigned long long)(d/1000),(unsigned long long)tag,(unsigned long long)address,(unsigned long long)bytes); }}
      int k=a->nq++; a->tag[k]=tag; a->dur[k]=d; a->address[k]=address; a->frames[k]=frames;
      if(a->started && !a->deadline){ extern u64 guest_ns(void); a->deadline=guest_ns()+5000000ull; }
      break; }
    case 4: out_copy_h(c,ev_handle(a->ev)); break;            /* RegisterBufferEvent */
    case 5: case 8: {                                          /* GetReleasedAudioOutBuffers(Auto) */
      {extern u64 guest_ns(void); if(aout_advance(a,guest_ns())) kevent_signal(a->ev); }
      u64 b, n; u32 cnt=0;
      if(buf_out(c,0,&b,&n) && b){ u32 cap=(u32)(n/8);
        /* the SDK's single buffer wrapper reads the first tag even when Count is 0, an old tag turns into a bogus
           next append pointer */
        if(cap) gw64(b,0);
        while(cnt<cap && cnt<(u32)a->nrel){ gw64(b+cnt*8ull,a->rel[cnt]); cnt++; }
        a->nrel-=cnt; memmove(a->rel,a->rel+cnt,a->nrel*8); }
      out32(c,cnt); break; }
    case 6: { u64 tag=in64(c,0); int has=0;                   /* ContainsAudioOutBuffer */
      for(int i=0;i<a->nq;i++) if(a->tag[i]==tag) has=1;
      out8(c,(u8)has); break; }
    case 9: out32(c,(u32)a->nq); break;                        /* GetAudioOutBufferCount */
    case 10: out64(c,a->played); break;                        /* GetAudioOutPlayedSampleCount */
    case 11: {                                                 /* FlushAudioOutBuffers: give everything back now */
      int any=a->nq>0;
      while(a->nq && a->nrel<AOUT_MAX) aout_pop(a);
      a->deadline=0; if(any) kevent_signal(a->ev);
      out8(c,(u8)any); break; }
    case 12: {u32 bits=in32(c,0); float v; memcpy(&v,&bits,4); a->volume=isfinite(v) && v>0?(v>16?16:v):0; break; }
    case 13: {u32 bits; memcpy(&bits,&a->volume,4); out32(c,bits); break; }                       /* GetAudioOutVolume: 1.0f */
  }
  pm_unlock(&g_aout_lk);
  return r; }

static SvcObj* aout_new(u32 ch){
  SvcObj* o=svcobj_new("IAudioOut",audout_obj,0);
  AudOut* a=calloc(1,sizeof *a); a->ev=kevent_new("audout buffers",0); a->channels=ch; a->volume=1;
  o->data=a; o->destroy=aout_destroy;
  pm_lock(&g_aout_lk); a->next=g_aouts; g_aouts=a; pm_unlock(&g_aout_lk);
  return o; }

static int audout_disp(SvcObj* o, IpcCtx* c){
  if(c->cmd==0||c->cmd==2){ u64 a,s; if(buf_out(c,0,&a,&s) && a){ strcpy((char*)GP(a),"DeviceOut"); } out32(c,1); return 0; }
  if(c->cmd==1||c->cmd==3){
    u64 a,s; if(buf_out(c,0,&a,&s) && a && s>=10) strcpy((char*)GP(a),"DeviceOut");   /* the name we actually opened */
    /* AudioOutParameter { u32 sample_rate; u16 channel_count; }. the channel count goes back as it came (0 means
       the default, 2), CRI in unicorn overlord asserts that GetAudioOutChannelCount() is what it asked for */
    u32 want=in32(c,4)&0xFFFF, ch= want>2? 6 : 2;
    out32(c,48000); out32(c,ch); out32(c,2); out32(c,1); out_obj(c,aout_new(ch)); return 0; }
  return quiet_ok(o,c); }

static SvcObj* new_audout(void){ return svcobj_new("audout:u",audout_disp,0); }

/* hwopus, packets get decoded with libopus. sonic 1 (sega ages) spins on the same packet forever after the logos
   if it gets "0 bytes used, 0 samples". input is { u32 size (big endian), u32 final_range } and then the opus
   packet, consumed = size + 8. output is interleaved s16 at the rate and channel count the decoder was opened with */
#ifndef SWR_NO_OPUS
#include "opus.h"
#include "opus_multistream.h"
#endif

#define OPUS_ERR (111u | (1040u<<9))

typedef struct { void* dec; int ms; u32 rate, ch; } HwOpus;

static u32 be32(const u8* p){ return ((u32)p[0]<<24)|((u32)p[1]<<16)|((u32)p[2]<<8)|p[3]; }

/* samples per channel in a packet, from the TOC byte. only used when there's no libopus */
static int opus_samples(const u8* d, u32 n, u32 rate){
  if(!n) return 0;
  u32 cfg=d[0]>>3, cnt=d[0]&3, frames= cnt==0? 1 : cnt<3? 2 : (n>1? (d[1]&0x3F) : 0);
  u32 us;   /* frame duration in 1/400 s units * 1000 */
  if(cfg<12) us=(u32[]){10000,20000,40000,60000}[cfg&3];
  else if(cfg<16) us=(cfg&1)? 20000 : 10000;
  else us=(u32[]){2500,5000,10000,20000}[cfg&3];
  return (int)((u64)frames*us*rate/1000000); }

static void hwopus_destroy(SvcObj* o){
  HwOpus* h=(HwOpus*)o->data; if(!h || !h->dec) return;
#ifndef SWR_NO_OPUS
  if(h->ms) opus_multistream_decoder_destroy((OpusMSDecoder*)h->dec); else opus_decoder_destroy((OpusDecoder*)h->dec);
#endif
  h->dec=NULL; }

static int hwopus_dec(SvcObj* o, IpcCtx* c){
  HwOpus* h=(HwOpus*)o->data;
  switch(c->cmd){
    case 0: case 2: case 4: case 5: case 6: case 7: case 8: case 9: break;
    default: return 0;                                   /* SetContext and the rest: nothing to keep */
  }
  int perf= c->cmd>=4, reset= (c->cmd>=6 && (in32(c,0)&1));
  u64 ia,is,oa,os; buf_in(c,0,&ia,&is); buf_out(c,0,&oa,&os);
  if(!ia || is<8){ out32(c,0); out32(c,0); if(perf) out64(c,0); return 0; }
  const u8* in=GP(ia); u32 size=be32(in);
  if((u64)size+8>is) return OPUS_ERR;
  int smp=0;
#ifndef SWR_NO_OPUS
  if(h->dec){
    int cap= os? (int)(os/(2u*h->ch)) : 0;
    if(reset){ if(h->ms) opus_multistream_decoder_ctl((OpusMSDecoder*)h->dec,OPUS_RESET_STATE); else opus_decoder_ctl((OpusDecoder*)h->dec,OPUS_RESET_STATE); }
    smp= h->ms? opus_multistream_decode((OpusMSDecoder*)h->dec,in+8,(opus_int32)size,(opus_int16*)GP(oa),cap,0)
              : opus_decode((OpusDecoder*)h->dec,in+8,(opus_int32)size,(opus_int16*)GP(oa),cap,0);
    if(smp<0){ static int said; if(said<4){ said++; LOG("audio: opus packet of %u bytes failed to decode (%d)\n",size,smp); } return OPUS_ERR; }
  } else
#endif
  { smp=opus_samples(in+8,size,h->rate); u64 bytes=(u64)smp*h->ch*2; if(bytes>os) bytes=os; if(oa) memset(GP(oa),0,(size_t)bytes); }
  out32(c,size+8); out32(c,(u32)smp); if(perf) out64(c,0);
  return 0; }

/* OpusMultiStreamParameters(Ex): rate, channels, streams, stereo streams, [use_large_frame, pad7], mapping[256] */
static SvcObj* hwopus_open(u32 rate, u32 ch, const u8* ms, int ex){
  SvcObj* o=svcobj_new("IHardwareOpusDecoder",hwopus_dec,sizeof(HwOpus)); o->destroy=hwopus_destroy;
  HwOpus* h=(HwOpus*)o->data; h->rate= rate? rate : 48000; h->ch= ch? ch : 2;
  if(ms){ memcpy(&h->rate,ms,4); memcpy(&h->ch,ms+4,4); if(!h->ch) h->ch=2; }
#ifndef SWR_NO_OPUS
  int err=0;
  if(ms){ u32 st,ss; memcpy(&st,ms+8,4); memcpy(&ss,ms+12,4);
    h->ms=1; h->dec=opus_multistream_decoder_create((opus_int32)h->rate,(int)h->ch,(int)st,(int)ss,ms+(ex? 24 : 16),&err); }
  else h->dec=opus_decoder_create((opus_int32)h->rate,(int)h->ch,&err);
  if(!h->dec || err){ static int said; if(said<4){ said++; LOG("audio: opus decoder %uHz x%u could not be created (%d), the game gets silence\n",h->rate,h->ch,err); } h->dec=NULL; }
  else { static int said; if(said<2){ said++; LOG("audio: opus decoder %uHz, %u channels%s\n",h->rate,h->ch,ms? " (multistream)" : ""); } }
#else
  (void)ex;
#endif
  return o; }

static int hwopus_disp(SvcObj* o, IpcCtx* c){
  u64 a,s;
  switch(c->cmd){
    case 0: case 4: out_obj(c,hwopus_open(in32(c,0),in32(c,4),NULL,0)); return 0;
    case 2: case 6: buf_in(c,0,&a,&s); out_obj(c,hwopus_open(0,0,(a && s>=16)? GP(a) : NULL,c->cmd==6)); return 0;
    case 1: case 3: case 5: case 7: case 8: case 9: out32(c,0x10000); return 0;
  }
  return quiet_ok(o,c); }

static SvcObj* new_hwopus(void){ return svcobj_new("hwopus",hwopus_disp,0); }

static int bsd_disp(SvcObj* o, IpcCtx* c){ (void)o;
  switch(c->cmd){ case 0: out32(c,0); return 0; case 1: return 0; case 2: out32(c,(u32)-1); out32(c,106); return 0; }
  out32(c,(u32)-1); out32(c,106); return 0; }

static SvcObj* new_bsd(void){ return svcobj_new("bsd",bsd_disp,0); }

static int ssl_disp(SvcObj* o, IpcCtx* c){ if(c->cmd==0){ out_obj(c,quiet("ISslContext")); return 0; } return quiet_ok(o,c); }

static SvcObj* new_ssl(void){ return svcobj_new("ssl",ssl_disp,0); }

static int prepo_disp(SvcObj* o, IpcCtx* c){ (void)o; (void)c; return 0; }

static SvcObj* new_prepo(void){ return svcobj_new("prepo",prepo_disp,0); }

static int psm_session(SvcObj* o, IpcCtx* c){ (void)o; if(c->cmd==0){ out_copy_h(c,ev_handle(kevent_new("psm",0))); return 0; } return 0; }

/* the pc's own battery (100% and charging on a desktop) */
static int psm_disp(SvcObj* o, IpcCtx* c){ (void)o; int pct, chg; plat_battery(&pct,&chg); switch(c->cmd){ case 0: out32(c,(u32)pct); return 0; case 1: out32(c,chg? 1 : 0); return 0; case 7: out_obj(c,svcobj_new("IPsmSession",psm_session,0)); return 0; case 4: case 5: out8(c,0); return 0; } return 0; }

static SvcObj* new_psm(void){ return svcobj_new("psm",psm_disp,0); }

static int fatal_disp(SvcObj* o, IpcCtx* c){ (void)o; fatal("The game called fatal:u (code %x)",in32(c,0)); return 0; }

static SvcObj* new_fatal(void){ return svcobj_new("fatal:u",fatal_disp,0); }

static int csrng_disp(SvcObj* o, IpcCtx* c){ (void)o; if(c->cmd==0){ u64 a,s; buf_out(c,0,&a,&s); static u64 x=0x9E3779B97F4A7C15ull; for(u64 i=0;i<s;i++){ x^=x<<13; x^=x>>7; x^=x<<17; GP(a)[i]=(u8)x; } } return 0; }

static SvcObj* new_csrng(void){ return svcobj_new("csrng",csrng_disp,0); }

static int mm_disp(SvcObj* o, IpcCtx* c){ (void)o; if(c->cmd==4||c->cmd==6) out32(c,1); return 0; }

static SvcObj* new_mm(void){ return svcobj_new("mm:u",mm_disp,0); }

/* nfp:user (amiibo). there's no reader here but the state still has to follow the calls. super mario odyssey
   finalizes nfp on every scene change and its NfpControllerThread polls GetState until it says "not initialized"
   before it exits, if it never does the scene loader waits for it forever (endless loading screen). same answers
   as yuzu with no amiibo on the reader */
typedef struct { int init; u32 dev; KEvent* ev[3]; } NfpUser;

static int nfp_user(SvcObj* o, IpcCtx* c){
  NfpUser* u=(NfpUser*)o->data;
  switch(c->cmd){
    case 0: u->init=1; u->dev=0; return 0;                                  /* Initialize */
    case 1: u->init=0; u->dev=0; return 0;                                  /* Finalize */
    case 2: { u64 a,s; u32 n=0;                                             /* ListDevices: player 1's controller */
      if(u->init && buf_out(c,0,&a,&s) && a && s>=8){ gw64(a,0); n=1; }
      out32(c,n); return 0; }
    case 3: if(u->init) u->dev=1; return 0;                                 /* StartDetection: searching */
    case 4: if(u->init) u->dev=0; return 0;                                 /* StopDetection */
    case 17: case 18: case 23: { int k= c->cmd==17? 0 : c->cmd==18? 1 : 2;  /* activate / deactivate / availability events */
      if(!u->ev[k]) u->ev[k]=kevent_new("nfp",0);
      out_copy_h(c,ev_handle(u->ev[k])); return 0; }
    case 19: out32(c,u->init? 1 : 0); return 0;                             /* GetState */
    case 20: out32(c,u->init? u->dev : 6); return 0;                        /* GetDeviceState: 6 = finalized */
    case 21: out32(c,0); return 0;                                          /* GetNpadId */
    case 22: out32(c,0); return 0;                                          /* GetApplicationAreaSize */
  }
  /* mount, tag info, application area: there's never a tag, a real console says "device not found" */
  if((c->cmd>=5 && c->cmd<=16) || c->cmd==24) return 115u | (64u<<9);
  return 0; }

static int nfp_disp(SvcObj* o, IpcCtx* c){ if(c->cmd==0){ out_obj(c,svcobj_new("IUser",nfp_user,sizeof(NfpUser))); return 0; } return quiet_ok(o,c); }

static SvcObj* new_nfp(void){ return svcobj_new("nfp:user",nfp_disp,0); }

static int caps_disp(SvcObj* o, IpcCtx* c){ (void)o; (void)c; return 0; }

static SvcObj* new_caps(void){ return svcobj_new("caps",caps_disp,0); }

/* BCAT. acts like an offline console: sync finishes right away (Done/OK) and the delivery cache is empty. games do
   wait on the progress object so it has to exist */
static int bcat_progress(SvcObj* o, IpcCtx* c){ (void)o;
  switch(c->cmd){
    case 0: { KEvent* e=kevent_new("bcat progress",0); e->signaled=1; out_copy_h(c,ev_handle(e)); return 0; }   /* GetEvent */
    case 1: { u64 a,sz; buf_out(c,0,&a,&sz); if(a && sz){ memset(GP(a),0,sz); if(sz>=8){ u32 st=9, rs=0; memcpy(GP(a),&st,4); memcpy(GP(a)+4,&rs,4); } } return 0; }   /* GetImpl: Done/OK */
  }
  return 0; }

static int bcat_dir(SvcObj* o, IpcCtx* c){ (void)o;
  switch(c->cmd){ case 0: return 0;                                   /* Open */
    case 1: case 2: out32(c,0); return 0; }                             /* Read / GetCount: no files */
  return 0; }

static int bcat_file(SvcObj* o, IpcCtx* c){ (void)o;
  switch(c->cmd){ case 0: return RC(122,2);                            /* Open: not found */
    case 1: out64(c,0); return 0; case 2: out64(c,0); return 0; case 3: { u8 d[0x10]; memset(d,0,sizeof d); outbytes(c,d,0x10); return 0; } }
  return 0; }

static int bcat_storage(SvcObj* o, IpcCtx* c){ (void)o;
  switch(c->cmd){
    case 0: out_obj(c,svcobj_new("IDeliveryCacheFileService",bcat_file,0)); return 0;
    case 1: out_obj(c,svcobj_new("IDeliveryCacheDirectoryService",bcat_dir,0)); return 0;
    case 10: out32(c,0); return 0; }                                    /* EnumerateDeliveryCacheDirectory: none */
  return 0; }

static int bcat_service(SvcObj* o, IpcCtx* c){ (void)o;
  switch(c->cmd){
    case 10100: case 10101: case 20100: case 20101: case 20300: case 20301:
      out_obj(c,svcobj_new("IDeliveryCacheProgressService",bcat_progress,0)); return 0; }
  return 0; }

static int bcat_disp(SvcObj* o, IpcCtx* c){ (void)o;
  switch(c->cmd){
    case 0: out_obj(c,svcobj_new("IBcatService",bcat_service,0)); return 0;
    case 1: case 2: out_obj(c,svcobj_new("IDeliveryCacheStorageService",bcat_storage,0)); return 0; }
  return 0; }

static SvcObj* new_bcat(void){ return svcobj_new("bcat",bcat_disp,0); }

static int aoc_purchase(SvcObj* o, IpcCtx* c){ (void)o; if(c->cmd==2){ out_copy_h(c,ev_handle(kevent_new("aoc purchase",0))); return 0; } if(c->cmd==3||c->cmd==4) return RC(164,400); return 0; }

static int aoc_disp(SvcObj* o, IpcCtx* c){ (void)o;
  switch(c->cmd){
    case 0: case 1: case 2: case 3: out32(c,0); return 0;                     /* Count/List: no dlc */
    case 5: case 6: out64(c,(g_title_id&~0xFFFull)+0x1000); return 0;         /* GetAddOnContentBaseId */
    case 7: case 9: case 11: case 12: case 13: case 50: return 0;
    case 8: case 10: out_copy_h(c,ev_handle(kevent_new("aoc",0))); return 0;   /* GetAddOnContentListChangedEvent */
    case 100: case 101: out_obj(c,svcobj_new("IPurchaseEventManager",aoc_purchase,0)); return 0; }
  return 0; }

static SvcObj* new_aoc(void){ return svcobj_new("aoc:u",aoc_disp,0); }

static int irs_disp(SvcObj* o, IpcCtx* c){ (void)o; if(c->cmd==303||c->cmd==304){ KShmem* s=kshmem_new(0x8000,"irs"); out_copy_h(c,h_new(&s->o)); return 0; } if(c->cmd==311){ out32(c,0); return 0; } return 0; }

static SvcObj* new_irs(void){ return svcobj_new("irs",irs_disp,0); }

/* CharInfo (0x58 bytes) of the console's default mii ("no name"). an all-zero CharInfo isn't a valid mii,
   tomodachi life builds its first mii with BuildDefault and the loader never finishes with zeros */
static void mii_default(IpcCtx* c){
  u8 ci[0x58]; memset(ci,0,sizeof ci);
  static const u8 id[16]={0x5b,0x3e,0x11,0x9a,0x2c,0x47,0x4d,0x0e,0x9f,0x31,0x6a,0x52,0x8e,0x07,0xc4,0x21};   /* any v4 uuid */
  memcpy(ci,id,16);
  const char* nm="no name"; for(int i=0;nm[i];i++) ci[0x10+i*2]=(u8)nm[i];
  static const u8 f[50]={
    0, 0, 0, 64, 64, 0, 0,          /* font region, favorite color, gender, height, build, type, region move */
    0, 0, 0, 0,                     /* faceline type, color, wrinkle, make */
    33, 1, 0,                       /* hair type, color, flip */
    2, 0, 4, 3, 4, 2, 12,           /* eye type, color, scale, aspect, rotate, x, y */
    6, 1, 4, 3, 6, 2, 10,           /* eyebrow type, color, scale, aspect, rotate, x, y */
    1, 4, 9,                        /* nose type, scale, y */
    23, 0, 4, 3, 13,                /* mouth type, color, scale, aspect, y */
    0, 0,                           /* beard color, type */
    0, 4, 10,                       /* mustache type, scale, y */
    0, 0, 4, 10,                    /* glasses type, color, scale, y */
    0, 4, 2, 20,                    /* mole type, scale, x, y */
    0 };
  memcpy(ci+0x26,f,sizeof f);
  outbytes(c,ci,sizeof ci); }

static int mii_db(SvcObj* o, IpcCtx* c){ (void)o; static u32 seen[4]; u32 b=c->cmd&127;
  if(!(seen[b>>5]&(1u<<(b&31)))){ seen[b>>5]|=1u<<(b&31); LOG("mii: IDatabaseService cmd %u\n",c->cmd); }
  if(c->cmd==0||c->cmd==2||c->cmd==3) out32(c,0);
  else if(c->cmd==1) out8(c,0);                         /* IsFullDatabase */
  else if(c->cmd==6 || c->cmd==7) mii_default(c);       /* BuildRandom / BuildDefault -> CharInfo */
  return 0; }

static int mii_disp(SvcObj* o, IpcCtx* c){ if(c->cmd==0){ out_obj(c,svcobj_new("IDatabaseService",mii_db,0)); return 0; } return quiet_ok(o,c); }

static SvcObj* new_mii(void){ return svcobj_new("mii:u",mii_disp,0); }

static int ldn_disp(SvcObj* o, IpcCtx* c){ if(c->cmd==0){ out_obj(c,quiet("IUserLocalCommunicationService")); return 0; } return quiet_ok(o,c); }

static SvcObj* new_ldn(void){ return svcobj_new("ldn:u",ldn_disp,0); }

static int ectx_disp(SvcObj* o, IpcCtx* c){ (void)o; (void)c; return 0; }

static SvcObj* new_ectx(void){ return svcobj_new("ectx:aw",ectx_disp,0); }

static int spl_disp(SvcObj* o, IpcCtx* c){ (void)o; if(c->cmd==0){ out64(c,0); return 0; } if(c->cmd==7){ u64 a,s; buf_out(c,0,&a,&s); memset(GP(a),0x5A,s); } return 0; }

static SvcObj* new_spl(void){ return svcobj_new("spl:",spl_disp,0); }

/* ngc:u, the ng word filter (tomodachi asks for it): nothing is a bad word and Mask gives the text back as is */
static int ngc_disp(SvcObj* o, IpcCtx* c){ (void)o;
  switch(c->cmd){
    case 0: out32(c,1); return 0;                                         /* GetContentVersion */
    case 1: out32(c,0); return 0;                                         /* Check: no matches */
    case 2: { u64 ia,in,oa,on; buf_in(c,0,&ia,&in); buf_out(c,0,&oa,&on);   /* Mask */
      if(ia && oa){ u64 n= in<on? in : on; memmove(GP(oa),GP(ia),n); } out32(c,0); return 0; }
    case 3: return 0;                                                     /* Reload */
  }
  return 0; }
static SvcObj* new_ngc(void){ return svcobj_new("ngc:u",ngc_disp,0); }

void svc_core_init(void){
  swr_audio_init();
  g_msg_event=kevent_new("applet msg",0); g_launch_ev=kevent_new("launchable",0); g_res_ev=kevent_new("res change",0); g_opmode_ev=kevent_new("opmode",0);
  g_aud_ev=kevent_new("audio renderer",0);
  pm_init(&g_aout_lk);
  /* the runtime keeps signaling these, so we hold a reference and a game closing its handles can't free them */
  kobj_ref(&g_msg_event->o); kobj_ref(&g_launch_ev->o); kobj_ref(&g_res_ev->o); kobj_ref(&g_opmode_ev->o); kobj_ref(&g_aud_ev->o);
  /* glibc accounts for the runtime's static TLS in each pthread's stack.  The
     shader diagnostic ring alone is 128 KiB, so the old 64 KiB request fails
     with EINVAL on Linux and leaves audio waiting forever for its clock event. */
  if(plat_thread(audio_clock,NULL,1u<<20)) WARN("audio: clock thread unavailable\n");
  if(plat_thread(aout_clock,NULL,256*1024)) WARN("audout: timer thread unavailable, using frontend playback pump\n");
  am_push_msg(0xF);          /* FocusStateChanged */
  /* ChangeIntoForeground: the app is in the foreground now. newer SDKs wait for this before they create the
     display layer (tomodachi life stays black without it) */
  am_push_msg(0x1);
  am_push_msg(0x1E);         /* OperationModeChanged */
  am_push_msg(0x1F);         /* PerformanceModeChanged */
  kevent_signal(g_launch_ev);
  svc_register("sm:",new_sm);
  svc_register("appletOE",new_appletoe); svc_register("appletAE",new_appletae);
  svc_register("set",new_set); svc_register("set:sys",new_setsys);
  svc_register("time:u",new_time); svc_register("time:a",new_time); svc_register("time:s",new_time);
  svc_register("acc:u0",new_acc); svc_register("acc:u1",new_acc); svc_register("acc:su",new_acc);
  svc_register("apm",new_apm); svc_register("apm:p",new_apm); svc_register("apm:am",new_apm);
  svc_register("ldr:ro",new_ro); svc_register("ro:1",new_ro);
  svc_register("chat:u",new_chat_u);
  svc_register("lm",new_lm); svc_register("pctl",new_pctl); svc_register("pctl:a",new_pctl); svc_register("pctl:s",new_pctl); svc_register("pctl:r",new_pctl);
  svc_register("nifm:u",new_nifm); svc_register("nifm:a",new_nifm); svc_register("nifm:s",new_nifm);
  svc_register("friend:u",new_friend); svc_register("friend:a",new_friend); svc_register("friend:v",new_friend);
  svc_register("ns:am2",new_ns); svc_register("ns:ec",new_ns); svc_register("ns:rid",new_ns); svc_register("ns:rt",new_ns); svc_register("ns:web",new_ns); svc_register("ns:ro",new_ns);
  svc_register("aud:u",new_aud_u); svc_register("audren:u",new_audren); svc_register("audout:u",new_audout); svc_register("audin:u",new_audout); svc_register("hwopus",new_hwopus);
  svc_register("bsd:u",new_bsd); svc_register("bsd:s",new_bsd); svc_register("ssl",new_ssl);
  svc_register("prepo:u",new_prepo); svc_register("prepo:a",new_prepo); svc_register("prepo:a2",new_prepo); svc_register("psm",new_psm);
  svc_register("fatal:u",new_fatal); svc_register("csrng",new_csrng); svc_register("mm:u",new_mm);
  svc_register("nfp:user",new_nfp); svc_register("nfc:user",new_nfp); svc_register("caps:u",new_caps); svc_register("caps:a",new_caps); svc_register("caps:su",new_caps); svc_register("caps:ss",new_caps);
  svc_register("bcat:u",new_bcat); svc_register("bcat:a",new_bcat); svc_register("aoc:u",new_aoc); svc_register("irs",new_irs);
  svc_register("mii:e",new_mii); svc_register("mii:u",new_mii); svc_register("ldn:u",new_ldn); svc_register("ectx:aw",new_ectx); svc_register("spl:",new_spl); svc_register("spl:mig",new_spl); svc_register("ngc:u",new_ngc);
}
