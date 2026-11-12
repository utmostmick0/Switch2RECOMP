/* SwitchRecomp - Copyright 2026 MZ Labs
   Licensed under the GNU Affero General Public License v3.0, see LICENSE.txt and NOTICE.txt.
   Forks and derived works have to keep the credit to SwitchRecomp by MZ Labs and the startup screen. */
/* HLE kernel: handles, objects, guest threads (1:1 with host threads), sync (events, mutex/condvar, address
   arbiter) and the SVCs games really call */
#include "rt.h"

PMutex g_klock;
u64 g_title_id = 0x0100000000001000ull;
u64 g_sysres_size;
int g_exiting;
static u64 g_next_tid = 0x50;

#define R_TIMEOUT     0xEA01
#define R_CANCELLED   0xEC01
#define R_BADHANDLE   0xE401
#define R_BADSTATE    0xFA01
#define R_BADADDR     0xCC01
#define R_OUTOFMEM    0xD001
#define R_BADENUM     0xF001
#define R_NOTFOUND    0xF201
#define R_OUTOFRANGE  0xEE01
#define R_BADMEMSTATE 0xD401
#define R_BADREGION   0xDC01
#define R_NOTIMPL     0xF601
#define HANDLE_WAIT   0x40000000u
#define H_CUR_PROC    0xFFFF8001u
#define H_CUR_THREAD  0xFFFF8000u
typedef struct { u32 imm, res; u64 lr, a[4], o1; } SvcRec;

static SvcRec g_svc_ring[64]; static u32 g_svc_ring_n;

/* ============================================================ handles */
#define MAXH 4096
static KObj* htab[MAXH]; static u16 hgen[MAXH]; static int hnext=1;

void kobj_ref(KObj* o){ if(o) __atomic_add_fetch(&o->refs,1,__ATOMIC_SEQ_CST); }

void kobj_unref(KObj* o){ if(o && __atomic_sub_fetch(&o->refs,1,__ATOMIC_SEQ_CST)==0 && o->destroy) o->destroy(o); }

u32 h_new(KObj* o){
  pm_lock(&g_klock);
  for(int k=0;k<MAXH;k++){ int i=hnext; hnext=hnext+1>=MAXH? 1 : hnext+1;
    if(!htab[i]){ htab[i]=o; kobj_ref(o); hgen[i]=(u16)((hgen[i]+1)&0x7FFF); if(!hgen[i]) hgen[i]=1; pm_unlock(&g_klock); return ((u32)hgen[i]<<15)|(u32)i; } }
  pm_unlock(&g_klock); fatal("no free handles"); return 0; }

static KObj* h_get_nl(u32 h){
  if(h==H_CUR_THREAD) return (KObj*)kthread_cur();
  u32 i=h&0x7FFF; if(!i || i>=MAXH || !htab[i] || hgen[i]!=(h>>15)) return NULL; return htab[i]; }

KObj* h_get(u32 h){ pm_lock(&g_klock); KObj* o=h_get_nl(h); pm_unlock(&g_klock); return o; }

KObj* h_get_type(u32 h, int t){ KObj* o=h_get(h); return (o && o->type==t)? o : NULL; }

int h_close(u32 h){
  pm_lock(&g_klock); u32 i=h&0x7FFF;
  if(!i || i>=MAXH || !htab[i] || hgen[i]!=(h>>15)){ pm_unlock(&g_klock); return R_BADHANDLE; }
  KObj* o=htab[i]; htab[i]=NULL; pm_unlock(&g_klock); kobj_unref(o); return 0; }

/* ============================================================ waits */
static void waiter_add(KObj* o, KThread* t){
  if(o->nwait==o->capwait){ o->capwait=o->capwait? o->capwait*2 : 4; o->waiters=realloc(o->waiters,sizeof(KThread*)*o->capwait); }
  o->waiters[o->nwait++]=t; }

static void waiter_del(KObj* o, KThread* t){
  for(int i=0;i<o->nwait;i++) if(o->waiters[i]==t){ o->waiters[i]=o->waiters[--o->nwait]; return; } }

static void wake(KThread* t, int result){ t->woken=1; t->wait_result=result; pc_signal(&t->cv); }

static void kobj_signal_nl(KObj* o){ for(int i=0;i<o->nwait;i++) wake(o->waiters[i],0); }

void kobj_signal(KObj* o){ pm_lock(&g_klock); kobj_signal_nl(o); pm_unlock(&g_klock); }

/* call with the lock held. 1 = woken, 0 = timeout */
static int sleep_nl(KThread* t, i64 timeout){
  if(timeout<0){ while(!t->woken) pc_wait(&t->cv,&g_klock,-1); return 1; }
  u64 end=plat_ns()+(u64)timeout;
  while(!t->woken){ u64 now=plat_ns(); if(now>=end) return 0; pc_wait(&t->cv,&g_klock,(i64)(end-now)); }
  return 1; }

/* ============================================================ events */
static int ev_sig(KObj* o){ return ((KEvent*)o)->signaled; }

static void ev_destroy(KObj* o){ free(o->waiters); free(o); }

KEvent* kevent_new(const char* name, int autoclear){
  KEvent* e=calloc(1,sizeof *e); e->o.type=KO_EVENT; e->o.is_signaled=ev_sig; e->o.destroy=ev_destroy; e->o.name=name; e->autoclear=autoclear; return e; }

void kevent_signal(KEvent* e){ pm_lock(&g_klock); e->signaled=1; kobj_signal_nl(&e->o); pm_unlock(&g_klock); }

void kevent_clear(KEvent* e){ pm_lock(&g_klock); e->signaled=0; pm_unlock(&g_klock); }

/* ============================================================ threads */
static KThread* g_threads[256]; static int g_nthreads;
KThread* kthread_cur(void){ return (KThread*)tls_thread; }

static void kthread_set(void* t){ tls_thread=t; }

static int th_sig(KObj* o){ return ((KThread*)o)->state==2; }

static void th_destroy(KObj* o){ (void)o; /* thread objects are never freed */ }

static u64 alloc_tls(void){ u64 a=kmem_alloc(0x1000,MS_TLS,PERM_RW); memset(GP(a),0,0x1000); return a; }

KThread* kthread_create(u64 entry, u64 arg, u64 stack_top, int prio, int core){
  KThread* t=calloc(1,sizeof *t);
  t->o.type=KO_THREAD; t->o.is_signaled=th_sig; t->o.destroy=th_destroy; t->o.name="thread";
  t->entry=entry; t->arg=arg; t->stack_top=stack_top; t->prio=prio; t->core=core<0? 0 : core; t->ideal=t->core; t->affinity=1ull<<t->core;
  t->tls=alloc_tls(); pc_init(&t->cv);
  pm_lock(&g_klock); t->id=g_next_tid++; if(g_nthreads<256) g_threads[g_nthreads++]=t; pm_unlock(&g_klock);
  CPU* c=&t->cpu; memset(c,0,sizeof *c);
  c->mem=g_mem; c->disp=g_disp; c->code_lo=g_code_lo; c->code_hi=g_code_hi; c->rt=&g_rtapi; c->thread=t;
  c->tpidrro=t->tls; c->x[0]=arg; c->x[31]=stack_top; c->pc=entry;
  return t;
}

void swr_fpcr_apply(CPU* c);

static void thread_body(void* p){
  KThread* t=p; kthread_set(t); CPU* c=&t->cpu;
  __atomic_store_n(&t->host,plat_thread_self(),__ATOMIC_RELEASE);
  swr_fpcr_apply(c);
  LOGV("[thread %llu] starts at %llx\n",(unsigned long long)t->id,(unsigned long long)c->pc);
  for(;;){
    if(UNLIKELY(c->pc==0)){ /* entry function returned */
      extern void svc_exit_thread(KThread* t); svc_exit_thread(t); }
    GuestFn f=swr_lookup(c,c->pc); f(c,c->pc);
  }
}

void kthread_start(KThread* t){
  t->state=1;
  if(plat_thread(thread_body,t,(size_t)64<<20)) fatal("could not create a system thread");
}

/* the stall report samples a thread through its host handle for ~130 ms; a thread that exits in the meantime waits
   here, or its handle was freed (closed on Windows) while the sampler still used it */
static volatile int g_host_lk;
static void host_lock(void){ while(__atomic_exchange_n(&g_host_lk,1,__ATOMIC_ACQUIRE)) plat_sleep_ns(100000); }
static void host_unlock(void){ __atomic_store_n(&g_host_lk,0,__ATOMIC_RELEASE); }

void svc_exit_thread(KThread* t){
  pm_lock(&g_klock); t->state=2; kobj_signal_nl(&t->o); pm_unlock(&g_klock);
  host_lock(); plat_thread_forget(__atomic_exchange_n(&t->host,(void*)0,__ATOMIC_ACQ_REL)); host_unlock();
  LOGV("[thread %llu] exits\n",(unsigned long long)t->id);
  plat_thread_exit();
}

void kernel_init(void){ pm_init(&g_klock); }

/* main thread: stack size from npdm, x0=0, x1=own handle */
static KThread* g_main;

void kernel_run_main(u64 entry, u64 stack_size, int prio, int core){
  stack_size=(stack_size+0xFFF)&~0xFFFull;
  u64 st=mem_find_free(STACK_BASE,STACK_BASE+STACK_SIZE,stack_size+0x2000,0x1000)+0x1000;
  mem_map(st,stack_size,MS_STACK,PERM_RW);
  KThread* t=kthread_create(entry,0,st+stack_size,prio,core);
  t->is_main=1; g_main=t; strcpy(t->name,"main");
  u32 h=h_new(&t->o); t->cpu.x[1]=h;
  kthread_start(t);
}

void process_exit(int code){
  g_exiting=1; LOG("The game exited (code %d)\n",code);
  fflush(NULL); exit(code);
}

/* ============================================================ kernel mutex arbitration */
static KThread* g_mwait;     /* waiters on a mutex (wait_kind 2), condvar (3) or address (4) */
static void wl_add(KThread* t){ t->next_waiter=g_mwait; g_mwait=t; }

static void wl_del(KThread* t){ KThread** p=&g_mwait; while(*p){ if(*p==t){ *p=t->next_waiter; t->next_waiter=NULL; return; } p=&(*p)->next_waiter; } }

static int wl_has(KThread* t){ for(KThread* w=g_mwait;w;w=w->next_waiter) if(w==t) return 1; return 0; }

/* best priority first (lowest number), FIFO within */
static KThread* wl_best(int kind, u64 key){
  KThread* best=NULL;
  for(KThread* w=g_mwait;w;w=w->next_waiter){
    if(w->wait_kind!=kind) continue;
    if((kind==2 && w->wait_addr!=key) || (kind==3 && w->wait_key!=key) || (kind==4 && w->wait_addr!=key)) continue;
    if(!best || w->prio<=best->prio) best=w;       /* list is reversed so <= picks the oldest */
  }
  return best; }

static int wl_count(int kind, u64 key){ int n=0;
  for(KThread* w=g_mwait;w;w=w->next_waiter) if(w->wait_kind==kind && ((kind==3? w->wait_key : w->wait_addr)==key)) n++; return n; }

static u32* U32(u64 a){ return (u32*)GP(a); }

static void unlock_nl(u64 addr){
  KThread* n=wl_best(2,addr);
  if(!n){ __atomic_store_n(U32(addr),0,__ATOMIC_SEQ_CST); return; }
  wl_del(n); n->wait_kind=0;
  int more=wl_count(2,addr)>0;
  __atomic_store_n(U32(addr),n->wait_tag|(more? HANDLE_WAIT : 0),__ATOMIC_SEQ_CST);
  wake(n,0);
}

/* checks for a stale owner tag. code built with old tcc did LDXR/STXR with its own spinlock, that isn't atomic
   against the kernel's writes, so the game could stomp our release and leave a dead owner there. the owner is
   bogus if the mutex word is 0, the thread exited, or it's waiting on this mutex itself (or on a condvar of it) */
static int g_heal_n;

static int owner_is_stale_nl(u32 tagv, u64 addr){
  u32 o=tagv&~HANDLE_WAIT; if(!o) return 1;
  if(o==H_CUR_THREAD) return 0;                                   /* not sure, leave it */
  KObj* ob=h_get_nl(o); if(!ob || ob->type!=KO_THREAD) return 0;  /* same thread; never steal from a real owner */
  KThread* ot=(KThread*)ob; if(ot->state==2) return 1;
  if((ot->wait_kind==2 || ot->wait_kind==3) && ot->wait_addr==addr && wl_has(ot)) return 1;
  return 0; }

static void heal_note(const char* what, u64 addr, u32 v){
  if(g_heal_n++<20 || !(g_heal_n&1023)) WARN("kernel: mutex %llx repaired (%s, value %x) [%d times]\n",(unsigned long long)addr,what,v,g_heal_n); }

static u32 svc_arbitrate_lock(KThread* t, u32 owner, u64 addr, u32 tag){
  if(addr&3) return R_BADADDR;
  pm_lock(&g_klock);
  u32 v=__atomic_load_n(U32(addr),__ATOMIC_SEQ_CST);
  if(v!=(owner|HANDLE_WAIT)){ pm_unlock(&g_klock); return 0; }
  if(owner_is_stale_nl(v,addr)){
    /* already released: hand it to us, keep the waiters bit if anyone else is queued */
    u32 nv=tag|(wl_count(2,addr)? HANDLE_WAIT : 0);
    if(__atomic_compare_exchange_n(U32(addr),&v,nv,0,__ATOMIC_SEQ_CST,__ATOMIC_SEQ_CST)) heal_note("on request",addr,v);
    pm_unlock(&g_klock); return 0; }   /* caller rereads the word and retries */
  t->wait_kind=2; t->wait_addr=addr; t->wait_tag=tag; t->woken=0; wl_add(t);
  sleep_nl(t,-1);
  u32 r=t->wait_result; pm_unlock(&g_klock); return r; }

static u32 svc_arbitrate_unlock(u64 addr){
  if(addr&3) return R_BADADDR;
  pm_lock(&g_klock); unlock_nl(addr); pm_unlock(&g_klock); return 0; }

static u32 svc_wait_cv(KThread* t, u64 maddr, u64 key, u32 tag, i64 timeout){
  pm_lock(&g_klock);
  unlock_nl(maddr);
  if(timeout==0){ pm_unlock(&g_klock); return R_TIMEOUT; }
  t->wait_kind=3; t->wait_key=key; t->wait_addr=maddr; t->wait_tag=tag; t->woken=0; wl_add(t);
  __atomic_store_n(U32(key),1,__ATOMIC_SEQ_CST);
  int ok=sleep_nl(t,timeout);
  u32 r;
  if(!ok){ if(wl_has(t)){ wl_del(t); } t->wait_kind=0; r=R_TIMEOUT;
    if(!wl_count(3,key)) __atomic_store_n(U32(key),0,__ATOMIC_SEQ_CST); }
  else r=t->wait_result;
  pm_unlock(&g_klock); return r; }

static u32 svc_signal_cv(u64 key, i32 count){
  pm_lock(&g_klock);
  int n=0;
  while(count<=0 || n<count){
    KThread* w=wl_best(3,key); if(!w) break;
    wl_del(w); n++;
    u64 ma=w->wait_addr;
    for(;;){
      u32 v=__atomic_load_n(U32(ma),__ATOMIC_SEQ_CST);
      if(v==0){ u32 z=0; if(__atomic_compare_exchange_n(U32(ma),&z,w->wait_tag,0,__ATOMIC_SEQ_CST,__ATOMIC_SEQ_CST)){ w->wait_kind=0; wake(w,0); break; } }
      else { if(__atomic_compare_exchange_n(U32(ma),&v,v|HANDLE_WAIT,0,__ATOMIC_SEQ_CST,__ATOMIC_SEQ_CST)){ w->wait_kind=2; wl_add(w); break; } }
    }
  }
  if(!wl_count(3,key)) __atomic_store_n(U32(key),0,__ATOMIC_SEQ_CST);
  pm_unlock(&g_klock); return 0; }

/* per frame sweep for mutex waiters stuck behind a bogus owner, or whose waiters bit got cleared (then the owner
   unlocks without calling us) */
void kernel_heal_mutexes(void){
  pm_lock(&g_klock);
  for(int guard=0; guard<64; guard++){
    int changed=0;
    for(KThread* w=g_mwait; w; w=w->next_waiter){
      if(w->wait_kind!=2) continue;
      u64 a=w->wait_addr; u32 v=__atomic_load_n(U32(a),__ATOMIC_SEQ_CST);
      if(owner_is_stale_nl(v,a)){
        KThread* n=wl_best(2,a); if(!n) continue;
        wl_del(n); int more=wl_count(2,a)>0; wl_add(n);
        u32 nv=n->wait_tag|(more? HANDLE_WAIT : 0);
        if(__atomic_compare_exchange_n(U32(a),&v,nv,0,__ATOMIC_SEQ_CST,__ATOMIC_SEQ_CST)){
          wl_del(n); n->wait_kind=0; wake(n,0); heal_note("stale owner",a,v); changed=1; break; }
      } else if(!(v&HANDLE_WAIT)){
        if(__atomic_compare_exchange_n(U32(a),&v,v|HANDLE_WAIT,0,__ATOMIC_SEQ_CST,__ATOMIC_SEQ_CST)) heal_note("lost waiter flag",a,v);
      }
    }
    if(!changed) break;
  }
  pm_unlock(&g_klock); }

/* ============================================================ address arbitration */
/* last address arbiter calls, printed in threads.txt next to the threads still waiting on an address */
typedef struct { u64 tid, addr, lr; i64 arg; u32 type, res; i32 value, before, after; u8 op, waiters; } ArbRec;

/* kept per address so a thread polling like crazy can't push the others out: 4096 addresses x 8 calls */
typedef struct { u64 addr; u32 n; ArbRec r[8]; } ArbSlot;

static ArbSlot g_arbs[4096]; static PMutex g_arb_lk;

static ArbSlot* arb_slot(u64 addr, int create){
  u32 h=(u32)((addr>>2)*2654435761u)&4095;
  for(int i=0;i<16;i++){ ArbSlot* s=&g_arbs[(h+i)&4095]; if(s->addr==addr) return s; if(!s->addr){ if(!create) return NULL; s->addr=addr; s->n=0; return s; } }
  if(!create) return NULL; ArbSlot* s=&g_arbs[h]; s->addr=addr; s->n=0; return s; }

static void arb_note(u8 op, KThread* t, u64 addr, u32 type, i32 value, i64 arg, u32 res, i32 before, int waiters){
  pm_lock(&g_arb_lk); ArbSlot* sl=arb_slot(addr,1);
  ArbRec* r=&sl->r[sl->n++&7];
  r->op=op; r->tid= t? t->id : 0; r->addr=addr; r->lr= t? t->cpu.x[30] : 0; r->type=type; r->value=value; r->arg=arg; r->res=res;
  r->before=before; r->after= (addr&3)? 0 : (i32)gr32(addr); r->waiters=(u8)(waiters>255? 255 : waiters); pm_unlock(&g_arb_lk); }

static u32 svc_wait_addr(KThread* t, u64 addr, u32 type, i32 value, i64 timeout){
  if(addr&3) return R_BADADDR;
  pm_lock(&g_klock);
  i32* p=(i32*)GP(addr);
  i32 cur=__atomic_load_n(p,__ATOMIC_SEQ_CST);
  switch(type){
    case 0: if(cur>=value){ pm_unlock(&g_klock); return R_BADSTATE; } break;
    case 1: for(;;){ if(cur>=value){ pm_unlock(&g_klock); return R_BADSTATE; }
              if(__atomic_compare_exchange_n(p,&cur,cur-1,0,__ATOMIC_SEQ_CST,__ATOMIC_SEQ_CST)) break; } break;
    case 2: if(cur!=value){ pm_unlock(&g_klock); return R_BADSTATE; } break;
    default: pm_unlock(&g_klock); return R_BADENUM;
  }
  if(timeout==0){ pm_unlock(&g_klock); return R_TIMEOUT; }
  t->wait_kind=4; t->wait_addr=addr; t->woken=0; wl_add(t);
  int ok=sleep_nl(t,timeout);
  u32 r= ok? t->wait_result : R_TIMEOUT;
  if(!ok && wl_has(t)) wl_del(t);
  t->wait_kind=0;
  pm_unlock(&g_klock); return r; }

static void wake_addr_nl(u64 addr, i32 count){
  int n=0; while(count<=0 || n<count){ KThread* w=wl_best(4,addr); if(!w) break; wl_del(w); w->wait_kind=0; wake(w,0); n++; } }

static u32 svc_signal_addr(u64 addr, u32 type, i32 value, i32 count){
  if(addr&3) return R_BADADDR;
  { static int said[3]; if(type<3 && !said[type]){ said[type]=1; LOG("kernel: SignalToAddress type %u in use\n",type); } }
  pm_lock(&g_klock);
  i32* p=(i32*)GP(addr);
  if(type==1){ i32 exp=value; if(!__atomic_compare_exchange_n(p,&exp,value+1,0,__ATOMIC_SEQ_CST,__ATOMIC_SEQ_CST)){ pm_unlock(&g_klock); return R_BADSTATE; } }
  else if(type==2){
    int total=wl_count(4,addr); i32 nv;
    /* no waiters: +1 (signaled). all of them woken: -1 (nobody waits). some still asleep: leave it, so the next
       signal comes here again and wakes them (auto clear LightEvents need this) */
    if(count<=0) nv= total>0? value-2 : value+1;
    /* same as the real kernel: no waiters +1 (signaled), all woken -1 (nobody waits), some still asleep leave it.
       with one waiter it has to be -1 too, newer SDK games (mario wonder) hang if it gives +1 */
    else nv= total==0? value+1 : total<=count? value-1 : value;
    i32 exp=value;
    if(nv!=value){ if(!__atomic_compare_exchange_n(p,&exp,nv,0,__ATOMIC_SEQ_CST,__ATOMIC_SEQ_CST)){ pm_unlock(&g_klock); return R_BADSTATE; } }
    else if(__atomic_load_n(p,__ATOMIC_SEQ_CST)!=value){ pm_unlock(&g_klock); return R_BADSTATE; }
  } else if(type!=0){ pm_unlock(&g_klock); return R_BADENUM; }
  wake_addr_nl(addr,count);
  pm_unlock(&g_klock); return 0; }

/* ============================================================ WaitSynchronization */
static u32 svc_wait_sync(KThread* t, u64 hptr, u32 n, i64 timeout, u32* out_idx){
  if(n>64) return R_OUTOFRANGE;
  KObj* objs[64]; u32 hs[64];
  for(u32 i=0;i<n;i++) hs[i]=gr32(hptr+i*4);
  pm_lock(&g_klock);
  for(u32 i=0;i<n;i++){ objs[i]=h_get_nl(hs[i]); if(!objs[i] || !objs[i]->is_signaled){ pm_unlock(&g_klock); if(!objs[i]){ static u32 nw; if(nw++<20 || !(nw&0xFFFF)) WARN("WaitSynchronization: invalid handle %x (%u times)\n",hs[i],nw); } return R_BADHANDLE; } }
  if(t->cancel){ t->cancel=0; pm_unlock(&g_klock); return R_CANCELLED; }
  u64 end= timeout<0? 0 : plat_ns()+(u64)timeout;
  for(;;){
    for(u32 i=0;i<n;i++) if(objs[i]->is_signaled(objs[i])){ *out_idx=i; pm_unlock(&g_klock); return 0; }
    if(timeout==0){ pm_unlock(&g_klock); return R_TIMEOUT; }
    i64 rem=-1; if(timeout>0){ u64 now=plat_ns(); if(now>=end){ pm_unlock(&g_klock); return R_TIMEOUT; } rem=(i64)(end-now); }
    /* n==0 is a plain sleep that CancelSynchronization ends (nn::os MultiWait with only user objects) */
    t->woken=0; t->wait_kind=1; t->wait_name= n? objs[0]->name : "sleep"; t->wait_timeout=timeout;
    for(u32 i=0;i<n;i++) waiter_add(objs[i],t);
    sleep_nl(t,rem);
    for(u32 i=0;i<n;i++) waiter_del(objs[i],t);
    t->wait_kind=0;
    if(t->cancel){ t->cancel=0; pm_unlock(&g_klock); return R_CANCELLED; }
  }
}

/* ============================================================ memory */
static u32 svc_query(u64 info, u64 addr){
  MemBlock b; mem_query(addr,&b);
  gw64(info,b.addr); gw64(info+8,b.size); gw32(info+16,b.state&0xFF); gw32(info+20,b.attr); gw32(info+24,b.perm&7);
  gw32(info+28,b.ipc); gw32(info+32,b.dev); gw32(info+36,0);
  return 0; }

static u32 svc_map_memory(u64 dst, u64 src, u64 size){
  if((dst|src|size)&0xFFF || !size) return R_BADADDR;
  int in_stack= dst>=STACK_BASE && dst+size<=STACK_BASE+STACK_SIZE;
  int in_alias= dst>=ALIAS_BASE && dst+size<=ALIAS_BASE+ALIAS_SIZE;
  /* 2017 SDKs (puyo puyo tetris, 1-2-switch, arms) don't ask for the stack region. they map every thread stack at
     a random free address in the low 2 GB (the map region of the 36 bit layout) and abort in CreateThread after a
     few refusals, so that range is allowed too */
  if(!in_stack && !in_alias && dst>=AS_BASE && dst+size<=0x80000000ull) in_stack=1;
  if(!in_stack && !in_alias) return R_BADREGION;
  /* mem_map checks that the range is free under the memory lock */
  { int r=mem_map(dst,size,in_stack? MS_STACK : MS_NORMAL,PERM_RW); if(r) return r==-1? R_BADMEMSTATE : R_OUTOFMEM; }
  memcpy(GP(dst),GP(src),size);
  mem_set_attr(src,size,1,1);         /* locked */
  mem_set_state(src,size,0xFFFFFFFFu,PERM_NONE);
  return 0; }

static u32 svc_unmap_memory(u64 dst, u64 src, u64 size){
  if((dst|src|size)&0xFFF || !size) return R_BADADDR;
  memcpy(GP(src),GP(dst),size);
  mem_unmap(dst,size);
  mem_set_attr(src,size,1,0);
  mem_set_state(src,size,0xFFFFFFFFu,PERM_RW);
  return 0; }

static void shm_destroy(KObj* o){ KShmem* s=(KShmem*)o; if(!s->gaddr) free(s->host); free(o->waiters); free(s); }

KShmem* kshmem_new(u64 size, const char* name){
  KShmem* s=calloc(1,sizeof *s); s->o.type=KO_SHMEM; s->o.destroy=shm_destroy; s->o.name=name;
  s->size=(size+0xFFF)&~0xFFFull; s->host=calloc(1,s->size); return s; }

u8* kshmem_ptr(KShmem* s){ return s->gaddr? GP(s->gaddr) : s->host; }

static u32 svc_map_shm(u32 h, u64 addr, u64 size, u32 perm){
  KShmem* s=(KShmem*)h_get_type(h,KO_SHMEM); if(!s) return R_BADHANDLE;
  if((addr|size)&0xFFF || !size) return R_BADADDR;
  if(size<s->size) size=s->size;
  if(mem_map(addr,size,MS_SHARED,perm&3)) return R_BADMEMSTATE;
  memcpy(GP(addr),s->host,s->size);
  s->gaddr=addr;
  return 0; }

static u32 svc_unmap_shm(u32 h, u64 addr, u64 size){
  KShmem* s=(KShmem*)h_get_type(h,KO_SHMEM); if(!s) return R_BADHANDLE;
  if(s->gaddr==addr){ memcpy(s->host,GP(addr),s->size); s->gaddr=0; }
  mem_unmap(addr,size); return 0; }

static void tmem_destroy(KObj* o){ KTmem* t=(KTmem*)o; mem_set_state(t->addr,t->size,0xFFFFFFFFu,PERM_RW); free(o->waiters); free(o); }

/* ============================================================ GetInfo */
/* application memory size. retail gives 3.2 GB, memory_gb can raise it (yuzu calls this extended memory). totk
   defaults to 5.2 GB, with 3.2 its allocator returns NULL during load */
int g_opt_mem_gb;

static u64 mem_total(void){
  /* Switch 2 (title ids 04xx...): the console has 12 GB and games get about 9 of it. Mario Kart World takes one 7 GB
     block at boot (its heap then comes out at ~7.7 GB, still inside our 8 GB heap region) */
  if((g_title_id>>56)==0x04 && g_opt_mem_gb<=0) return 0x240000000ull;
  if(g_opt_mem_gb>=8) return 0x1CD500000ull;
  if(g_opt_mem_gb>=6) return 0x14D500000ull;
  if(g_opt_mem_gb>=4 || g_opt_mem_gb<0) return 0xCD500000ull;
  if(g_title_id==0x0100F2C0115B6000ull) return 0x14D500000ull;     /* Tears of the Kingdom */
  /* these games grab the whole switch memory budget at boot, so leave some room instead of giving their allocator
     an almost empty pool */
  {extern char g_exename[]; const char* title=g_mod?g_mod->title:NULL;
   if((title && strstr(title,"Xenoblade")) || strstr(g_exename,"Xenoblade") || strstr(g_exename,"xenoblade")) return 0x14D500000ull; }
  return 0xCD500000ull; }

u64 kernel_mem_total(void){ return mem_total(); }

/* svcMapPhysicalMemory pages count as used, like on hw */
static u64 g_phys_mapped;

/* the ideal core of threads created with -2 (main.npdm) */
static int default_core(void){ return g_mod? (int)g_mod->main_core : 0; }

/* what the kernel counts before the game allocates anything: the loaded modules plus the main thread stack. mario
   wonder checks one of its HeapDef sizes (85 MB) against this at boot and aborts if the size isn't bigger, so it
   has to be the real number and not a guess */
static u64 image_memory(void){
  static u64 sz;
  if(!sz){
    for(u32 i=0;i<g_mod->nmods;i++) sz+=(g_mod->mods[i].size+0xFFF)&~0xFFFull;
    sz+=((g_mod->main_stack? g_mod->main_stack : 0x100000)+0xFFF)&~0xFFFull; }
  return sz; }

static u64 used_memory(void){ return image_memory()+g_heap_size+g_phys_mapped; }

void mem_report(char* out, int n){ snprintf(out,n,"heap %llu MB, mapped physical memory %llu MB, used %llu MB of %llu MB",
  (unsigned long long)(g_heap_size>>20),(unsigned long long)(g_phys_mapped>>20),(unsigned long long)(used_memory()>>20),(unsigned long long)(mem_total()>>20)); }

static u32 svc_get_info_(u32 id0, u32 h, u64 id1, u64* out);

static u32 svc_get_info(u32 id0, u32 h, u64 id1, u64* out){
  u32 r=svc_get_info_(id0,h,id1,out);
  static u8 seen[64]; if(id0<64 && !seen[id0]){ seen[id0]=1; LOG("GetInfo %u/%llu -> %llx\n",id0,(unsigned long long)id1,(unsigned long long)*out); }
  return r; }

static u32 svc_get_info_(u32 id0, u32 h, u64 id1, u64* out){
  switch(id0){
    case 0: *out=0xF; return 0;                                  /* CoreMask */
    case 1: *out=0xFFFFFFFFFFFFFFFFull>>(64-60)<<4; *out=0xFFFFFFFFFFFFFFF0ull; return 0;
    case 2: *out=ALIAS_BASE; return 0;
    case 3: *out=ALIAS_SIZE; return 0;
    case 4: *out=HEAP_BASE; return 0;
    case 5: *out=HEAP_SIZE; return 0;
    case 6: { *out=mem_total(); static int said;
      /* games made for 3.2 GB size their heaps from this. smo and mk8d don't load if it reports more */
      if(!said && g_opt_mem_gb>4){ said=1; WARN("memory_gb=%d: the game sees %llu MB instead of the console's 3285. Only a few games need this (Tears of the Kingdom); if this one crashes while loading, set memory_gb=0\n",g_opt_mem_gb,(unsigned long long)(*out>>20)); }
      return 0; }                                                 /* total app memory */
    case 7: *out=used_memory(); return 0;
    case 8: *out=0; return 0;
    case 9: *out=0; return 0;                                    /* resource limit handle 0 */
    case 10: *out=0; return 0;
    case 11: { u64 r=plat_ns()*0x9E3779B97F4A7C15ull^(id1*0xC2B2AE3D27D4EB4Full); *out=r; return 0; }
    case 12: *out=AS_BASE; return 0;
    case 13: *out=(g_as36? 0x1000000000ull : AS_SIZE)-AS_BASE; return 0;
    case 14: *out=STACK_BASE; return 0;
    case 15: *out=STACK_SIZE; return 0;
    case 16: *out=g_sysres_size; return 0;                       /* SystemResourceSize (npdm) */
    case 17: *out=g_sysres_size? 0x80000ull : 0; return 0;
    case 18: *out=g_title_id; return 0;
    case 19: *out=0; return 0;
    case 20: { static u64 uectx; if(!uectx) uectx=kmem_alloc(0x1000,MS_TLS,PERM_RW); *out=uectx; return 0; }
    case 21: *out=mem_total(); return 0;
    case 22: *out=used_memory(); return 0;
    case 23: *out=1; return 0;
    case 24: { int live=0; for(int i=0;i<g_nthreads;i++) if(g_threads[i] && g_threads[i]->state!=2) live++; *out=(u64)(live<96? 96-live : 0); return 0; }  /* FreeThreadCount: unity skips its job threads if this
                                                                                                                                                              is 0 */
    case 0xF0000002: { KThread* t=kthread_cur(); (void)t; *out=plat_ns()*192/10000; return 0; }
    case 26: *out=1; return 0;
    case 27: case 28: *out=0; return 0;
    /* Switch 2: 29/30 are read but 0 is fine. 33 is the memory page granularity (ro checks relro alignment with
       it, the sdk heap grows by it with MapPhysicalMemory: 0 there spins forever) */
    case 29: case 30: *out=0; return 0;
    case 33: *out=0x1000; return 0;
    default: WARN("GetInfo %u/%llu not implemented\n",id0,(unsigned long long)id1); *out=0; return 0;
  }
  (void)h;
}

/* ============================================================ SVC */
/* nearest exported symbol via each module's dynsym */
typedef struct { u64 addr; u32 name_off; u32 mod; } GSym;

static GSym* g_gsyms; static int g_ngsyms; static u64 g_gstr[16];

static int gsym_cmp(const void* a, const void* b){ u64 x=((const GSym*)a)->addr, y=((const GSym*)b)->addr; return x<y? -1 : x>y; }

static void gsym_load(void){
  static int done; if(done) return; done=1;
  for(u32 m=0;m<g_mod->nmods && m<16;m++){ u64 base=g_mod->mods[m].base; if(!base) continue;
    MemBlock b; mem_query(base,&b); if(b.state==MS_FREE) continue;
    u64 mod0=base+gr32(base+4); if(gr32(mod0)!=0x30444F4D) continue;
    u64 dyn=mod0+(u64)(i64)(i32)gr32(mod0+4), symtab=0, strtab=0, hash=0;
    for(int i=0;i<256;i++){ u64 tag=gr64(dyn+i*16), val=gr64(dyn+i*16+8); if(!tag) break; if(tag==6) symtab=val; else if(tag==5) strtab=val; else if(tag==4) hash=val; }
    if(!symtab||!strtab) continue;
    u64 n= hash? gr32(base+hash+4) : (strtab>symtab? (strtab-symtab)/24 : 0); if(n>2000000) n=0;
    g_gstr[m]=base+strtab;
    g_gsyms=realloc(g_gsyms,(g_ngsyms+n)*sizeof(GSym));
    for(u64 i=1;i<n;i++){ u64 s=base+symtab+i*24; u64 v=gr64(s+8); u16 sh=*(u16*)GP(s+6); if(!v || !sh) continue;
      g_gsyms[g_ngsyms].addr=base+v; g_gsyms[g_ngsyms].name_off=gr32(s); g_gsyms[g_ngsyms].mod=m; g_ngsyms++; } }
  if(g_ngsyms) qsort(g_gsyms,g_ngsyms,sizeof(GSym),gsym_cmp);
}

static const char* gsym(u64 a){
  static char buf[4][200]; static int k; char* o=buf[k++&3]; o[0]=0;
  gsym_load(); int lo=0, hi=g_ngsyms-1, best=-1;
  while(lo<=hi){ int mid=(lo+hi)/2; if(g_gsyms[mid].addr<=a){ best=mid; lo=mid+1; } else hi=mid-1; }
  if(best<0 || a-g_gsyms[best].addr>0x20000) return o;
  snprintf(o,200," <%.150s+%llx>",(const char*)GP(g_gstr[g_gsyms[best].mod]+g_gsyms[best].name_off),(unsigned long long)(a-g_gsyms[best].addr));
  return o; }

static void guest_backtrace(CPU* c){
  WARN("  pc=%llx lr=%llx sp=%llx fp=%llx\n",(unsigned long long)c->pc,(unsigned long long)c->x[30],(unsigned long long)c->x[31],(unsigned long long)c->x[29]);
  { /* this also runs from the crash handler: a fault here would kill the report */
    u64 x16=c->x[16]; MemBlock xb; mem_query(x16,&xb);
    int x16ok= x16>=0x10000 && x16<AS_SIZE-8 && xb.state!=MS_FREE && xb.state!=MS_INACCESSIBLE && x16+8<=xb.addr+xb.size;
    WARN("  pc%s  lr%s  x16->%s  x17%s\n",gsym(c->pc),gsym(c->x[30]),x16ok? gsym(gr64(x16)) : "",gsym(c->x[17])); }
  u64 fp=c->x[29];
  for(int i=0;i<24 && fp>=AS_BASE && fp<AS_SIZE && !(fp&7);i++){
    MemBlock b; mem_query(fp,&b); if(b.state==MS_FREE || b.state==MS_INACCESSIBLE) break;
    u64 lr=gr64(fp+8); WARN("   #%d %llx%s\n",i,(unsigned long long)lr,gsym(lr)); fp=gr64(fp); }
}

/* SDK functions we replace with native code. only calls that go through the dispatch table see this, so calls from
   the game into the sdk module (PLT), that's how games get to these. nn::hid::ShowController*: the controller
   applet. tomodachi life (SDK 20) aborts inside ShowControllerSupport with hid 710 (npad not connected) before the
   applet even launches. with one controller connected the applet returns right away: 1 player, No.1. SWR_NO_HLE=1
   turns this off */
static void hle_ctrl_support(CPU* RESTRICT c, u64 entry){ (void)entry;
  u64 info=c->x[0]; if(info>=AS_BASE && info<AS_SIZE){ u32 v[2]={1,0}; memcpy(GP(info),v,8); }   /* playerCount=1 (+pad), selectedId=No1 */
  c->x[0]=0; c->pc=c->x[30];   /* return like RET: callers check pc == their return address */
  static int said; if(!said){ said=1; LOG("hid: ShowControllerSupport answered by the runtime (1 player, controller 1)\n"); } }

static void hle_ctrl_other(CPU* RESTRICT c, u64 entry){ (void)entry; c->x[0]=0; c->pc=c->x[30];
  static int said; if(!said){ said=1; LOG("hid: controller applet call answered by the runtime (ok)\n"); } }

/* Switch 2 SDK's SystemEvent wrapper asserts when a service-backed event has
   no native SystemEventType storage.  The service side still owns and signals
   the kernel event; keep this thin wrapper from aborting while the runtime
   completes that hand-off. */
static void hle_wait_system_event(CPU* RESTRICT c, u64 entry){ (void)entry;
  c->x[0]=0; c->pc=c->x[30];
  static int said; if(!said++){ LOG("hle: WaitSystemEvent completed through the runtime event bridge\n"); }
}

static void hle_wsi_present(CPU* RESTRICT c, u64 entry){ (void)entry;
  extern void ns2_native_present(u32 slot);
  ns2_native_present((u32)c->x[1]);
  c->x[0]=0; c->pc=c->x[30];
  static int said; if(!said++){ LOG("hle: Ounce NativeWindow::Present completed through vi2\n"); }
}

static void hle_wsi_acquire(CPU* RESTRICT c, u64 entry){ (void)entry;
  /* Acquire's first output is the swapchain slot.  The NVN shim owns the
     actual pacing; return slot zero here so the SDK's wrapper can continue. */
  if(c->x[1]>=AS_BASE && c->x[1]+4<AS_SIZE) gw32(c->x[1],0);
  c->x[0]=0; c->pc=c->x[30];
  static int said; if(!said++){ LOG("hle: Ounce NativeWindow::Acquire completed through NVN\n"); }
}

/* sead::ExpHeap only works from one thread at a time unless the game turns its lock on. on the switch the threads
   sharing one of those heaps sit on the same core and never run at once, here they do: odyssey's archive loader and
   HakoniwaSequence::initSystem broke the free list on PCs with many cores and the game halted in ExpHeap::tryAlloc.
   calls through the vtable (all of them in practice) take one lock. SWR_NO_HEAP_LOCK=1 turns it off */
#define HL_MAX 32
static struct { u64 a; GuestFn f; } g_hl[HL_MAX]; static int g_nhl;
static PMutex g_hl_m; static volatile u64 g_hl_owner; static int g_hl_depth;

static void hle_heap_locked(CPU* RESTRICT c, u64 entry){
  GuestFn f=NULL; for(int i=0;i<g_nhl;i++) if(g_hl[i].a==entry){ f=g_hl[i].f; break; }
  if(!f){ c->x[0]=0; c->pc=c->x[30]; return; }
  u64 me=(u64)(uintptr_t)c;   /* one CPU struct per guest thread */
  if(__atomic_load_n(&g_hl_owner,__ATOMIC_ACQUIRE)==me) g_hl_depth++;
  else { pm_lock(&g_hl_m); __atomic_store_n(&g_hl_owner,me,__ATOMIC_RELEASE); g_hl_depth=1; }
  f(c,entry);
  if(--g_hl_depth==0){ __atomic_store_n(&g_hl_owner,0,__ATOMIC_RELEASE); pm_unlock(&g_hl_m); } }

/* Switch 2: NVN's GPU device comes from NvRmGpuLibOpen/NvRmGpuDeviceOpen. their results are logged (the first few calls)
   so a device that fails to open shows up in the log instead of as a NULL call much later */
#define NT_MAX 400
/* Switch 2 titles (04...) get the driver trace by default, so a crash log already shows the last driver calls.
   SWR_TRACE_NVOS=1 turns it on for any game, SWR_TRACE_OFF=1 turns it off */
static int nvrm_trace_on(void){ static int v=-1; if(v<0) v= getenv("SWR_TRACE_OFF")? 0 : (getenv("SWR_TRACE_NVOS") || (g_title_id>>56)==0x04); return v; }
/* how many calls of one function get logged: the first few normally, a lot more while the trace is on (the game's own
   memory pools and window textures come after the driver's, they were cut off at 6) */
static int nvrm_cap(const char* nm){ int os=!strncmp(nm,"NvOsDrv",7); if(strstr(nm,"ErrorNotification")) return 4; return nvrm_trace_on()? (os? 400 : 150) : (os? 40 : 6); }
static int guest_ok(u64 a, u64 n){ MemBlock b; if(a<0x10000) return 0; mem_query(a,&b); return b.state!=MS_FREE && a+n<=b.addr+b.size; }
/* NvRmMem handles the driver made (NvRmMemHandleAllocAttr) and the memory they cover: a window texture whose pool
   reads back handle 0 gets the handle of the memory it sits in */
#define NMH_MAX 1024
static struct { u32 id; u64 a, sz; } g_nmh[NMH_MAX]; static int g_nnmh; static u64 g_cgam_a, g_cgam_sz;
static u32 nmh_find(u64 a){ for(int i=g_nnmh-1;i>=0;i--) if(a>=g_nmh[i].a && a<g_nmh[i].a+g_nmh[i].sz) return g_nmh[i].id; return 0; }
static void dump_words(const char* what, u64 a, u32 n){
  if(!guest_ok(a,n)){ LOG("nvrm:   %s at %llx: not readable\n",what,(unsigned long long)a); return; }
  LOG("nvrm:   %s at %llx:",what,(unsigned long long)a); for(u32 i=0;i<n;i+=8) LOG("%s%llx",i%64? " " : "\n[      ]     ",(unsigned long long)gr64(a+i)); LOG("\n"); }
/* the pool (or texture) holds its memory's address somewhere in its first 0x100 bytes */
static u32 nmh_scan(u64 obj){ if(!guest_ok(obj,0x100)) return 0; for(u32 i=0;i<0x100;i+=8){ u32 id=nmh_find(gr64(obj+i)); if(id) return id; } return 0; }
u64 g_nvrm_pend;
static struct { u64 a; GuestFn f; const char* nm; int n; } g_nt[NT_MAX]; static int g_nnt;
static void hle_nvrm_trace(CPU* RESTRICT c, u64 entry){
  int k=-1; for(int i=0;i<g_nnt;i++) if(g_nt[i].a==entry){ k=i; break; }
  if(k<0){ c->x[0]=0; c->pc=c->x[30]; return; }
  u64 a0=c->x[0], a1=c->x[1], a2=c->x[2], a3=c->x[3];
  /* these are tail calls into the driver, the result isn't there yet when f returns: the out pointer of the last
     DeviceOpen is read at the next traced call */
  extern u64 g_nvrm_pend; u64 pend=g_nvrm_pend; g_nvrm_pend=0; if(pend){ MemBlock b; mem_query(pend,&b); if(b.state!=MS_FREE) LOG("nvrm: the device NvRmGpuDeviceOpen wrote: %llx\n",(unsigned long long)gr64(pend)); pend=0; }
  int cap=nvrm_cap(g_nt[k].nm);
  /* nn::fs opens (Switch 2): the path and whether it was there, a file missing from a partial romfs shows up here */
  if(!strncmp(g_nt[k].nm,"_ZN2nn2fs",9)){ u64 pa=strstr(g_nt[k].nm,"OpenFile") || strstr(g_nt[k].nm,"OpenDirectory")? a1 : a1; char path[256]={0};
    if(guest_ok(pa,1)){ for(int i=0;i<255 && guest_ok(pa+i,1);i++){ char ch=*(char*)GP(pa+i); if(!ch) break; path[i]=ch; } }
    u64 lr2=c->x[30]; g_nt[k].f(c,entry);
    if(c->pc==lr2 && (u32)c->x[0]){ static int nm2, cap2=-1; if(cap2<0) cap2= getenv("SWR_FS_MISS_ALL")? 1000000 : sw2_cap(40); if(nm2<cap2){ nm2++; LOG("fs: %s %s -> %x (not there)\n",strstr(g_nt[k].nm,"OpenFile")? "OpenFile" : strstr(g_nt[k].nm,"OpenDirectory")? "OpenDirectory" : "GetEntryType",path,(u32)c->x[0]); } }
    return; }
  if(!strcmp(g_nt[k].nm,"NvRmMemGetFd") && !(u32)a0){ u64 tex=c->x[21], pool= guest_ok(tex+16,8)? gr64(tex+16) : 0;
    static int nd; if(nd<8){ nd++; LOG("nvrm: NvRmMemGetFd of handle 0 (lr %llx): texture %llx, pool %llx\n",(unsigned long long)c->x[30],(unsigned long long)tex,(unsigned long long)pool); dump_words("texture",tex,0x80); dump_words("pool",pool,0x100); }
    u32 id= nmh_scan(pool); if(!id) id=nmh_scan(tex);
    if(id && !getenv("SWR_NO_FD_FIX")){ LOG("nvrm:   handle 0 -> %u (the NvRmMem handle of the memory the pool sits in; SWR_NO_FD_FIX=1 turns this off)\n",id); c->x[0]=a0=id; if(pool && guest_ok(pool+88,4) && !gr32(pool+88)) gw32(pool+88,id); }
    else LOG("nvrm:   no NvRmMem handle covers that pool (%d handles known)\n",g_nnmh); }
  if(g_nt[k].n<cap && ++g_nt[k].n) LOG("nvrm: %s(%llx, %llx, %llx, %llx) lr %llx\n",g_nt[k].nm,(unsigned long long)a0,(unsigned long long)a1,(unsigned long long)a2,(unsigned long long)a3,(unsigned long long)c->x[30]);
  if(!strcmp(g_nt[k].nm,"NvRmGpuDeviceOpen")) g_nvrm_pend=a3;
  /* some game versions (a newer Mario Kart World) pass a NULL device to NvRmGpuDeviceChooseKind on their first GPU
     memory allocation and the SDK reads through it. The device NvRmGpuDeviceOpen made is the only one there is */
  { static u64 dev; if(!strcmp(g_nt[k].nm,"NvRmGpuDeviceChooseKind") && !a0 && dev){ static int nl; if(nl++<3) LOG("nvrm: NvRmGpuDeviceChooseKind with no device: using %llx\n",(unsigned long long)dev); c->x[0]=a0=dev; }
    if(!strcmp(g_nt[k].nm,"NvRmGpuDeviceGetInfo") && a0>=0x10000 && !dev) dev=a0; }
  if(strstr(g_nt[k].nm,"SetPreemptionModes") && a0>=0x10000) LOG("nvrm:   target %llx\n",(unsigned long long)gr64(gr64(a0)+80));
  if(!strcmp(g_nt[k].nm,"NvOsDrvIoctl") && (u32)a1==0xc0184102 && a2>=0x10000) LOG("nvrm:   alloc_space {pages %x, page size %x, flags %x, offset %llx}\n",gr32(a2),gr32(a2+4),gr32(a2+8),(unsigned long long)gr64(a2+16));
  u64 lr=c->x[30]; int show=g_nt[k].n<=cap;
  int alloc=!strcmp(g_nt[k].nm,"NvRmMemHandleAllocAttr"); u64 ua= alloc && guest_ok(a1,76)? gr64(a1+68) : 0, usz= alloc && guest_ok(a1,76)? gr64(a1+20) : 0;
  if(alloc) g_cgam_a=g_cgam_sz=0;
  if(strstr(g_nt[k].nm,"CreateGpuAccessibleMemory")){ g_cgam_a=a2; g_cgam_sz=a3; }   /* AllocAttr makes the memory GPU accessible with this */
  g_nt[k].f(c,entry);
  if(alloc && !ua){ ua=g_cgam_a; usz=g_cgam_sz; }
  /* the display's native sync handle has no NvRm fence behind it here (id -1). mario kart world treats that as "no
     fence", other games abort in nn::wsi OnAcquireTexture. syncpoint 0 with value 0 is a fence that's already done */
  if(c->pc==lr && (u32)c->x[0]==0xFFFFFFFFu && strstr(g_nt[k].nm,"GetNvRmFenceFromNativeSyncHandle") && !getenv("SWR_NO_FENCE_FIX")){
    static int nf; if(nf++<3) LOG("nvrm: native sync handle without a fence -> syncpoint 0 value 0 (already signaled)\n"); c->x[0]=0; }
  if(alloc && c->pc==lr && !(u32)c->x[0] && guest_ok(a2,4)){ u32 id=gr32(a2);
    if(show) LOG("nvrm:   handle %u, memory %llx size %llx\n",id,(unsigned long long)ua,(unsigned long long)usz);
    if(ua && usz && g_nnmh<NMH_MAX){ g_nmh[g_nnmh].id=id; g_nmh[g_nnmh].a=ua; g_nmh[g_nnmh].sz=usz; g_nnmh++; } }
  if(show && c->pc==lr) LOG("nvrm: %s -> %llx\n",g_nt[k].nm,(unsigned long long)c->x[0]); }

/* SWR_TRACE_FN=addr,addr,... (hex guest addresses): logs the arguments and the result of those functions */
#define TF_MAX 16
static struct { u64 a; GuestFn f; int n; } g_tf[TF_MAX]; static int g_ntf;
static void hle_fn_trace(CPU* RESTRICT c, u64 entry){
  int k=-1; for(int i=0;i<g_ntf;i++) if(g_tf[i].a==entry){ k=i; break; }
  if(k<0){ c->x[0]=0; c->pc=c->x[30]; return; }
  u64 a0=c->x[0], a1=c->x[1], a2=c->x[2], a3=c->x[3], lr=c->x[30];
  if(g_tf[k].n<8) LOG("trace: %llx(%llx, %llx, %llx, %llx) from %llx called\n",(unsigned long long)entry,(unsigned long long)a0,(unsigned long long)a1,(unsigned long long)a2,(unsigned long long)a3,(unsigned long long)lr);   /* a call that never returns still shows */
  g_tf[k].f(c,entry);
  if(g_tf[k].n<8 && ++g_tf[k].n) LOG("trace: %llx(%llx, %llx, %llx, %llx) from %llx -> %llx%s\n",(unsigned long long)entry,(unsigned long long)a0,(unsigned long long)a1,(unsigned long long)a2,(unsigned long long)a3,
    (unsigned long long)lr,(unsigned long long)c->x[0], c->pc==lr? "" : " (tail call)"); }

static int heap_fn_wanted(const char* nm){
  if(strncmp(nm,"_ZN4sead7ExpHeap",16) && strncmp(nm,"_ZNK4sead7ExpHeap",17)) return 0;
  /* destroy/freeAll run disposers (game code that can wait on other threads), not those */
  static const char* fns[]={"8tryAllocE","4freeEPv","10tryReallocE","11resizeFrontE","10resizeBackE","6adjustE","11getFreeSizeE","21getMaxAllocatableSizeE","13getAllocSizeE",NULL};
  for(int i=0;fns[i];i++) if(strstr(nm,fns[i])) return 1;
  return 0; }

static u64 gsym_find(const char* name){
  gsym_load(); for(int i=0;i<g_ngsyms;i++) if(!strcmp((const char*)GP(g_gstr[g_gsyms[i].mod]+g_gsyms[i].name_off),name)) return g_gsyms[i].addr;
  return 0; }

void hle_install(void){
  if(getenv("SWR_NO_HLE")) return;
  extern GuestFn* g_disp; extern u64 g_code_lo, g_code_hi;
  gsym_load(); int n=0;
  { extern void nvn_hook_install(u64 (*)(const char*)); nvn_hook_install(gsym_find); }
  { const char* e=getenv("SWR_TRACE_FN"); while(e && *e && g_ntf<TF_MAX){ u64 a=strtoull(e,(char**)&e,16);
      if(a>=g_code_lo && a<g_code_hi && !(a&3)){ GuestFn* d=&g_disp[(a-g_code_lo)/4]; if(*d){ g_tf[g_ntf].a=a; g_tf[g_ntf].f=*d; g_ntf++; *d=hle_fn_trace; } }
      while(*e==',' || *e==' ') e++; } }
  for(int i=0;i<g_ngsyms;i++){ const char* nm=(const char*)GP(g_gstr[g_gsyms[i].mod]+g_gsyms[i].name_off); u64 a=g_gsyms[i].addr;
    if(heap_fn_wanted(nm) && !getenv("SWR_NO_HEAP_LOCK") && a>=g_code_lo && a<g_code_hi && !(a&3) && g_nhl<HL_MAX){
      GuestFn* d=&g_disp[(a-g_code_lo)/4]; if(*d && *d!=hle_heap_locked){ if(!g_nhl) pm_init(&g_hl_m); g_hl[g_nhl].a=a; g_hl[g_nhl].f=*d; g_nhl++; *d=hle_heap_locked; }
      continue; }
    if((!strcmp(nm,"NvRmGpuLibOpen") || !strcmp(nm,"NvRmGpuDeviceOpen") || !strcmp(nm,"NvRmGpuDeviceChooseKind") || !strcmp(nm,"NvRmGpuLibListDevices") || !strcmp(nm,"NvRmGpuDeviceGetInfo") || !strcmp(nm,"NvRmGpuAddressSpaceCreate") || !strcmp(nm,"NvRmGpuAddressSpaceAllocationCreate") || !strcmp(nm,"NvRmGpuDeviceAllocateMemory") || (nvrm_trace_on() && (!strncmp(nm,"NvOsDrv",7) || !strncmp(nm,"NvRmGpu",7) || !strncmp(nm,"NvRmMem",7) || !strncmp(nm,"_ZN2nn2gs8external",18) || !strncmp(nm,"_ZN2nn3gpu3sdk",14) || !strncmp(nm,"_ZN2nn3wsi",10) || !strcmp(nm,"_ZN2nn2fs8OpenFileEPNS0_10FileHandleEPKci") || !strcmp(nm,"_ZN2nn2fs12GetEntryTypeEPNS0_18DirectoryEntryTypeEPKc") || !strcmp(nm,"_ZN2nn2fs13OpenDirectoryEPNS0_15DirectoryHandleEPKci")))) && a>=g_code_lo && a<g_code_hi && !(a&3) && g_nnt<NT_MAX){
      GuestFn* d=&g_disp[(a-g_code_lo)/4]; if(*d && *d!=hle_nvrm_trace){ g_nt[g_nnt].a=a; g_nt[g_nnt].f=*d; g_nt[g_nnt].nm=nm; g_nnt++; *d=hle_nvrm_trace; }
      continue; }
    if(strncmp(nm,"_ZN2nn3hid",10) || !strstr(nm,"ShowController")) continue;
    if(a<g_code_lo || a>=g_code_hi || (a&3)) continue;
    int with_info= strstr(nm,"ShowControllerSupport") && strstr(nm,"ControllerSupportResultInfo");
    g_disp[(a-g_code_lo)/4]= with_info? hle_ctrl_support : hle_ctrl_other; n++;
    LOG("hle: %s at %llx\n",nm,(unsigned long long)a); }
  { const char* nm="_ZN2nn2os15WaitSystemEventEPNS0_15SystemEventTypeE"; u64 a=gsym_find(nm);
    if(a>=g_code_lo && a<g_code_hi && !(a&3)){ g_disp[(a-g_code_lo)/4]=hle_wait_system_event; LOG("hle: %s at %llx\n",nm,(unsigned long long)a); } }
  { const char* nm="_ZN2nn3wsi5ounce6native12NativeWindow7PresentEjRKNS_2gs16NativeSyncHandleE"; u64 a=gsym_find(nm);
    if(a>=g_code_lo && a<g_code_hi && !(a&3)){ g_disp[(a-g_code_lo)/4]=hle_wsi_present; LOG("hle: %s at %llx\n",nm,(unsigned long long)a); } }
  { const char* nm="_ZN2nn3wsi5ounce6native12NativeWindow7AcquireEPjPNS_2gs16NativeSyncHandleE"; u64 a=gsym_find(nm);
    if(a>=g_code_lo && a<g_code_hi && !(a&3)){ g_disp[(a-g_code_lo)/4]=hle_wsi_acquire; LOG("hle: %s at %llx\n",nm,(unsigned long long)a); } }
  if(g_nhl) LOG("hle: %d sead::ExpHeap functions run under one lock (threads that share a core on the switch run at once here)\n",g_nhl);
  (void)n; }

/* imports rtld couldn't resolve (left at 0) */
static void dump_unresolved(void){
  int shown=0;
  for(u32 m=0;m<g_mod->nmods;m++){ u64 base=g_mod->mods[m].base; if(!base) continue;
    MemBlock b; mem_query(base,&b); if(b.state==MS_FREE) continue;
    u64 mod0=base+gr32(base+4); if(gr32(mod0)!=0x30444F4D) continue;
    u64 dyn=mod0+(u64)(i64)(i32)gr32(mod0+4);
    u64 symtab=0,strtab=0,jmprel=0,pltsz=0,rela=0,relasz=0;
    for(int i=0;i<256;i++){ u64 tag=gr64(dyn+i*16), val=gr64(dyn+i*16+8); if(!tag) break;
      if(tag==6) symtab=val; else if(tag==5) strtab=val; else if(tag==23) jmprel=val; else if(tag==2) pltsz=val; else if(tag==7) rela=val; else if(tag==8) relasz=val; }
    if(!symtab||!strtab) continue;
    u64 tabs[2][2]={{jmprel,pltsz},{rela,relasz}};
    for(int t=0;t<2;t++){ if(!tabs[t][0]) continue;
      for(u64 o=0;o+24<=tabs[t][1];o+=24){ u64 r=base+tabs[t][0]+o; u64 off=gr64(r), info=gr64(r+8); u32 ty=(u32)info, si=(u32)(info>>32);
        if(!si || (ty!=1026 && ty!=1025 && ty!=257)) continue;
        if(gr64(base+off)!=0) continue;
        u64 s=base+symtab+si*24ull; const char* nm=(const char*)GP(base+strtab+gr32(s)); u8 inf=*(u8*)GP(s+4);
        if(nm[0]=='_' && nm[1]=='_' && (inf>>4)==2) continue;          /* linker symbols */
        if(shown++<80) WARN("  unresolved in %s: %s%s (GOT %llx)\n",g_mod->mods[m].name,nm,(inf>>4)==2?" [weak]":"",(unsigned long long)(base+off)); } } }
  if(shown) WARN("  %d unresolved imports in total\n",shown);
}

static void kernel_dump_code(u64 ra);
void kernel_dump_regs(CPU* c){
  if(c->pc<0x1000 || getenv("SWR_UNRES")) dump_unresolved();
  for(int i=0;i<31;i+=4) WARN("  x%-2d=%016llx x%-2d=%016llx x%-2d=%016llx x%-2d=%016llx\n",i,(unsigned long long)c->x[i],i+1,(unsigned long long)c->x[i+1],i+2,(unsigned long long)c->x[i+2],i+3,(unsigned long long)(i+3<32?c->x[i+3]:0));
  guest_backtrace(c);
  /* code around lr */
  { u64 lr=c->x[30]&~3ull; MemBlock cb; mem_query(lr,&cb);
    if(cb.state!=MS_FREE && lr>0x100) for(u64 base=lr-0xC0; base<lr+0x40; base+=0x40){
      char line[400]; int n=snprintf(line,sizeof line,"  code %llx:",(unsigned long long)base);
      for(int w=0;w<16;w++) n+=snprintf(line+n,sizeof line-n," %08x",gr32(base+w*4));
      WARN("%s\n",line); } }
  /* the functions called just before lr (a bad pointer usually comes back from one of them): their code */
  { u64 lr=c->x[30]&~3ull; MemBlock cb; mem_query(lr,&cb); int nc=0;
    if(cb.state!=MS_FREE && (cb.perm&4) && lr>0x100) for(u64 a=lr-0x40;a<lr && nc<4;a+=4){ if(a<cb.addr) continue; u32 ins=gr32(a);
      if((ins>>26)==0x25){ u64 tgt=a+(u64)((i64)((i32)(ins<<6)>>6)*4); nc++; WARN("  calls %llx (from %llx):\n",(unsigned long long)tgt,(unsigned long long)a); kernel_dump_code(tgt+0x180); } } }
  /* what the regs point at (objects, vtables) */
  for(int r=0;r<29;r++){ u64 a=c->x[r]; if(a<0x10000 || a>=AS_SIZE-64 || (a&7)) continue; MemBlock b; mem_query(a,&b); if(b.state==MS_FREE || b.state==MS_INACCESSIBLE) continue;
    WARN("  mem x%d %llx: %llx %llx %llx %llx\n",r,(unsigned long long)a,(unsigned long long)gr64(a),(unsigned long long)gr64(a+8),(unsigned long long)gr64(a+16),(unsigned long long)gr64(a+24));
    u64 v=gr64(a); if(v>=0x10000 && v<AS_SIZE-64 && !(v&7)){ MemBlock vb; mem_query(v,&vb); if(vb.state!=MS_FREE && vb.state!=MS_INACCESSIBLE){
      { char sl[1200]; int n=0; for(int e=0;e<8;e++){ const char* s=gsym(gr64(v+e*8)); if(s[0]) n+=snprintf(sl+n,sizeof sl-n," [%d]%s",e,s); if(n>1000) break; } if(n) WARN("    vtable:%s\n",sl); }
      WARN("    -> %llx: %llx %llx %llx %llx %llx %llx %llx %llx\n",(unsigned long long)v,(unsigned long long)gr64(v),(unsigned long long)gr64(v+8),(unsigned long long)gr64(v+16),(unsigned long long)gr64(v+24),(unsigned long long)gr64(v+32),(unsigned long long)gr64(v+40),(unsigned long long)gr64(v+48),(unsigned long long)gr64(v+56)); } } }
  WARN("  last SVCs (num args -> result out1, called from):\n");
  for(u32 kn_=g_svc_ring_n, k=kn_>40? kn_-40 : 0; k<kn_; k++){ SvcRec* r=&g_svc_ring[k&63];
    WARN("    %02x %llx %llx %llx %llx -> %x %llx  lr=%llx\n",r->imm,(unsigned long long)r->a[0],(unsigned long long)r->a[1],(unsigned long long)r->a[2],(unsigned long long)r->a[3],r->res,(unsigned long long)r->o1,(unsigned long long)r->lr); }
  extern char g_ipc_ring[32][80]; extern u32 g_ipc_ring_n;
  WARN("  last IPC calls:\n");
  for(u32 kn_=g_ipc_ring_n, k=kn_>32? kn_-32 : 0; k<kn_; k++) WARN("    %s\n",g_ipc_ring[k&31]);
  /* code around the last svcs, usually the check that failed before an abort */
  { u64 seen[6]; int ns=0;
    for(u32 k=g_svc_ring_n; k>0 && k+12>g_svc_ring_n && ns<4; k--){ u64 lr=g_svc_ring[(k-1)&63].lr; int dup=0; for(int j=0;j<ns;j++) if(seen[j]==lr) dup=1; if(dup) continue; seen[ns++]=lr;
      for(u64 base=lr-0x100; base<lr+0x100; base+=0x40){ MemBlock cb; mem_query(base,&cb); if(cb.state==MS_FREE) break;
        char line[400]; int n=snprintf(line,sizeof line,"  code %llx:",(unsigned long long)base);
        for(int w=0;w<16;w++) n+=snprintf(line+n,sizeof line-n," %08x",gr32(base+w*4));
        WARN("%s\n",line); } } }
  /* and around the callers */
  u64 fp=c->x[29];
  for(int i=0;i<8 && fp>=AS_BASE && fp<AS_SIZE && !(fp&7);i++){
    MemBlock b; mem_query(fp,&b); if(b.state==MS_FREE || b.state==MS_INACCESSIBLE) break;
    u64 lr=gr64(fp+8); fp=gr64(fp); MemBlock cb; mem_query(lr-0x60,&cb); if(cb.state==MS_FREE) continue;
    for(u64 base=lr-0x140; base<lr+0x40; base+=0x40){
      char line[400]; int n=snprintf(line,sizeof line,"  code %llx:",(unsigned long long)base);
      for(int w=0;w<16;w++) n+=snprintf(line+n,sizeof line-n," %08x",gr32(base+w*4));
      WARN("%s\n",line); } }
}

extern KShmem* kshmem_new(u64 size, const char* name);

static void swr_svc_(CPU* c, u32 imm);

void swr_svc(CPU* c, u32 imm){
  u64 a0=c->x[0],a1=c->x[1],a2=c->x[2];
  u64 a3=c->x[3];
  swr_svc_(c,imm);
  { KThread* t=kthread_cur(); if(t){ u32 k=t->svc_hist_n;
      if(k && t->svc_hist[(k-1)%24].imm==imm && t->svc_hist[(k-1)%24].lr==c->x[30]) t->svc_hist[(k-1)%24].n++;
      else { typeof(&t->svc_hist[0]) h=&t->svc_hist[k%24]; h->imm=imm; h->lr=c->x[30]; h->a[0]=a0; h->a[1]=a1; h->a[2]=a2; h->a[3]=a3; h->n=1; t->svc_hist_n=k+1;
        /* WaitSynchronization: keep the first handle now, the array lives on the caller's stack */
        h->h0= (imm==0x18 && a2>=1 && a1>=AS_BASE && a1<AS_SIZE)? gr32(a1) : 0; }
      t->svc_hist[(t->svc_hist_n-1)%24].res=(u32)c->x[0]; } }
  if(imm!=0x1E && imm!=0x0B && imm!=0x10){ u32 i=__atomic_fetch_add(&g_svc_ring_n,1,__ATOMIC_RELAXED)&63; SvcRec* r=&g_svc_ring[i];
    r->imm=imm; r->lr=c->x[30]; r->a[0]=a0; r->a[1]=a1; r->a[2]=a2; r->a[3]=a3; r->res=(u32)c->x[0]; r->o1=c->x[1]; }
  static u32 nbad; if((u32)c->x[0]==R_BADHANDLE && imm!=0x16 && (nbad++<20 || !(nbad&0xFFFF))) { WARN("SVC 0x%x with invalid handle (args %llx %llx %llx) pc=%llx lr=%llx\n",imm,(unsigned long long)a0,(unsigned long long)a1,(unsigned long long)a2,(unsigned long long)c->pc,(unsigned long long)c->x[30]);
    if(nbad<=3){ u64 fp=c->x[29]; WARN("  called from:"); for(int i=0;i<12 && fp>=AS_BASE && fp<AS_SIZE && !(fp&7);i++){ MemBlock b; mem_query(fp,&b); if(b.state==MS_FREE) break; WARN(" %llx",(unsigned long long)gr64(fp+8)); fp=gr64(fp); } WARN("\n"); } }
}

static void swr_svc_(CPU* c, u32 imm){
  if(g_nvrm_pend){ static int nsv; MemBlock b; mem_query(g_nvrm_pend,&b); u64 v= b.state!=MS_FREE? gr64(g_nvrm_pend) : 0;
    if(v || ++nsv>=400){ LOG("nvrm: NvRmGpuDeviceOpen's device: %llx (%d svcs later)\n",(unsigned long long)v,nsv); g_nvrm_pend=0; nsv=0; } }
  KThread* t=kthread_cur();
  u64* x=c->x;
  switch(imm){
  case 0x01: { u64 a=mem_heap_set(x[1]);
    if((!a && x[1]) || (g_title_id>>56)==0x04){ static int nl; if(nl<sw2_cap(4)){ nl++; LOG("svc SetHeapSize %llx (%llu MB) -> %s\n",(unsigned long long)x[1],(unsigned long long)(x[1]>>20),(!a && x[1])? "out of memory (the PC couldn't commit it)" : "ok"); } }
    if(!a && x[1]){ x[0]=R_OUTOFMEM; return; } x[0]=0; x[1]=HEAP_BASE; return; }
  case 0x02: mem_set_state(x[0],x[1],0xFFFFFFFFu,(u32)x[2]); x[0]=0; return;
  case 0x03: mem_set_attr(x[0],x[1],(u32)x[2],(u32)x[3]); x[0]=0; return;
  case 0x80: { /* SetGpuMemoryAttribute (Switch 2): the SDK marks memory GPU accessible (attribute 0x20) before it
                 registers it with the GPU, and clears it when it's freed. kept as a memory attribute, nothing else uses it */
    u32 mask=(u32)x[2], attr=(u32)x[3];
    if((x[0]|x[1])&0xFFF || !x[1] || x[0]+x[1]<x[0]){ x[0]= (x[0]&0xFFF)? 0xCC01 : 0xCA01; return; }   /* invalid address / size */
    if((attr&~mask) || ((mask|attr)&~0x20u)){ x[0]=0xE801; return; }                                   /* invalid combination */
    { static int said; if(said<4){ said++; LOG("svc 0x80: GPU memory %llx size %llx attribute %x/%x\n",(unsigned long long)x[0],(unsigned long long)x[1],attr,mask); } }
    mem_set_attr(x[0],x[1],mask,attr); x[0]=0; return; }
  case 0x04: x[0]=svc_map_memory(x[0],x[1],x[2]); return;
  case 0x05: x[0]=svc_unmap_memory(x[0],x[1],x[2]); return;
  case 0x06: x[0]=svc_query(x[0],x[2]); x[1]=0; return;
  case 0x07: process_exit(0); return;
  case 0x08: {
    int prio=(int)(u32)x[4], core=(int)(i32)(u32)x[5];
    if(core==-2) core=default_core();
    KThread* n=kthread_create(x[1],x[2],x[3],prio,core);
    u32 h=h_new(&n->o); x[0]=0; x[1]=h;
    if((g_title_id>>56)==0x04){ static int nl; if(nl<sw2_cap(8)){ nl++; LOG("thread %llu created: entry %llx prio %d core %d (lr %llx)\n",(unsigned long long)n->id,(unsigned long long)n->cpu.pc,prio,core,(unsigned long long)c->x[30]); } }
    else LOGV("CreateThread entry=%llx stack=%llx prio=%d core=%d -> %x\n",(unsigned long long)x[1],(unsigned long long)n->stack_top,prio,core,h);
    return; }
  case 0x09: { KThread* n=(KThread*)h_get_type((u32)x[0],KO_THREAD); if(!n){ x[0]=R_BADHANDLE; return; }
    if((g_title_id>>56)==0x04){ static int nl; if(nl<sw2_cap(8)){ nl++; LOG("thread %llu started (lr %llx)\n",(unsigned long long)n->id,(unsigned long long)c->x[30]); } }
    if(n->state==0) kthread_start(n); x[0]=0; return; }
  case 0x0A: svc_exit_thread(t); return;
  case 0x0B: { i64 ns=(i64)x[0]; t->sleep_lr=x[30]; t->sleep_n++; memcpy(t->sleep_x,x,sizeof t->sleep_x);
    if(ns<=0) plat_yield(); else plat_sleep_ns(ns); return; }
  case 0x0C: { KThread* n=(KThread*)h_get_type((u32)x[1],KO_THREAD); if(!n){ x[0]=R_BADHANDLE; return; } x[0]=0; x[1]=(u32)n->prio; return; }
  case 0x0D: { KThread* n=(KThread*)h_get_type((u32)x[0],KO_THREAD); if(!n){ x[0]=R_BADHANDLE; return; } n->prio=(int)(u32)x[1]; x[0]=0; return; }
  case 0x0E: { KThread* n=(KThread*)h_get_type((u32)x[2],KO_THREAD); if(!n){ x[0]=R_BADHANDLE; return; } x[0]=0; x[1]=(u32)n->ideal; x[2]=n->affinity; return; }
  case 0x0F: { KThread* n=(KThread*)h_get_type((u32)x[0],KO_THREAD); if(!n){ x[0]=R_BADHANDLE; return; }
    /* ideal core -1: none, -2: the process default, -3: keep it. like horizon, the thread moves when the mask
       leaves out the core it's on. games pin threads with -1 and one bit, then use GetCurrentProcessorNumber to
       pick per core data, so if every thread stays on core 0 they deadlock */
    i32 core=(i32)(u32)x[1]; u64 mask=x[2];
    if(core==-2){ core=default_core(); mask=1ull<<core; } else if(core==-3) core=n->ideal;
    if(mask) n->affinity=mask;
    n->ideal=core;
    if(core>=0) n->core=core; else if(!(n->affinity>>n->core&1)) n->core=63-__builtin_clzll(n->affinity);
    x[0]=0; return; }
  case 0x10: x[0]=(u32)(t? t->core : 0); return;
  case 0x11: { KEvent* e=(KEvent*)h_get_type((u32)x[0],KO_EVENT); if(!e){ x[0]=R_BADHANDLE; return; } kevent_signal(e); x[0]=0; return; }
  case 0x12: case 0x17: { KObj* o=h_get((u32)x[0]); if(!o){ x[0]=R_BADHANDLE; return; }
    if(o->type==KO_EVENT){ KEvent* e=(KEvent*)o; pm_lock(&g_klock); int was=e->signaled; e->signaled=0; pm_unlock(&g_klock);
      x[0]= (imm==0x17 && !was)? R_BADSTATE : 0; return; }
    x[0]=0; return; }
  case 0x13: x[0]=svc_map_shm((u32)x[0],x[1],x[2],(u32)x[3]); return;
  case 0x14: x[0]=svc_unmap_shm((u32)x[0],x[1],x[2]); return;
  case 0x15: { KTmem* m=calloc(1,sizeof *m); m->o.type=KO_TMEM; m->o.destroy=tmem_destroy; m->o.name="tmem"; m->addr=x[1]; m->size=x[2]; m->perm=(u32)x[3];
    x[0]=0; x[1]=h_new(&m->o); return; }
  case 0x16: x[0]=((u32)x[0]==H_CUR_THREAD||(u32)x[0]==H_CUR_PROC)? 0 : (u32)h_close((u32)x[0]); return;
  case 0x18: { u32 idx=0; u32 r=svc_wait_sync(t,x[1],(u32)x[2],(i64)x[3],&idx); x[0]=r; x[1]=idx; return; }
  case 0x19: { KThread* n=(KThread*)h_get_type((u32)x[0],KO_THREAD); if(!n){ x[0]=R_BADHANDLE; return; }
    pm_lock(&g_klock); if(n->wait_kind==1) wake(n,R_CANCELLED); n->cancel=1; pm_unlock(&g_klock); x[0]=0; return; }
  case 0x1A: x[0]=svc_arbitrate_lock(t,(u32)x[0],x[1],(u32)x[2]); return;
  case 0x1B: x[0]=svc_arbitrate_unlock(x[0]); return;
  case 0x1C: x[0]=svc_wait_cv(t,x[0],x[1],(u32)x[2],(i64)x[3]); return;
  case 0x1D: x[0]=svc_signal_cv(x[0],(i32)(u32)x[1]); return;
  case 0x1E: x[0]=c->rt->ticks(); return;
  case 0x1F: { char name[16]={0}; memcpy(name,GP(x[1]),12);
    if(!strcmp(name,"sm:")){ SvcObj* o=svc_open("sm:"); x[0]=0; x[1]=session_new(o); return; }
    WARN("ConnectToNamedPort(%s) unknown\n",name); x[0]=R_NOTFOUND; return; }
  case 0x21: ipc_handle(t,(u32)x[0],t->tls); return;
  case 0x22: ipc_handle(t,(u32)x[2],x[0]); return;
  case 0x24: x[0]=0; x[1]=0x51; return;
  case 0x25: { KObj* o=h_get((u32)x[1]); KThread* n=(o&&o->type==KO_THREAD)? (KThread*)o : t; x[0]=0; x[1]=n->id; return; }
  case 0x26: {
    u32 reason=(u32)x[0];
    if(reason&0x80000000u){ LOGV("svcBreak (notice) %x\n",reason); x[0]=0; return; }
    WARN("\n*** The game called svcBreak (reason=%x, info=%llx size=%llx) ***\n",reason,(unsigned long long)x[1],(unsigned long long)x[2]);
    if(x[1] && x[2]>=4 && x[2]<0x1000){ u8 tmp[64]; memcpy(tmp,GP(x[1]),x[2]<64?x[2]:64); WARN("  data: "); for(u64 i=0;i<(x[2]<64?x[2]:64);i++) WARN("%02x",tmp[i]); WARN("\n"); }
    { char mr[200]; mem_report(mr,sizeof mr); WARN("  memory: %s\n",mr); }
    kernel_dump_regs(c);
    /* strings pointed to by regs, often the abort message */
    for(int r=0;r<31;r++){ u64 a=c->x[r]; if(a<0x10000 || a>=AS_SIZE-256) continue; MemBlock b; mem_query(a,&b);
      if(b.state==MS_FREE || b.state==MS_INACCESSIBLE) continue;   /* not committed: reading it would fault */
      u64 room=b.addr+b.size-a; int lim= room<200? (int)room : 200;
      const char* p=(const char*)GP(a); int n=0; while(n<lim && p[n]>=32 && p[n]<127) n++;
      if(n>=4 && (n==200 || (n<lim && p[n]==0))) WARN("  x%d -> \"%.*s\"\n",r,n,p); }
    fatal("The game stopped (svcBreak). See the .log for details.");
    return; }
  case 0x27: { u64 n=x[1]; if(n>4096) n=4096; char buf[4100]; memcpy(buf,GP(x[0]),n); buf[n]=0; LOG("[game] %s%s",buf,(n&&buf[n-1]=='\n')?"":"\n"); x[0]=0; return; }
  case 0x29: { u64 o=0; x[0]=svc_get_info((u32)x[1],(u32)x[2],x[3],&o); x[1]=o; return; }
  case 0x2A: case 0x2B: case 0x5D: case 0x5E: case 0x5F: case 0x36: x[0]=0; return;
  case 0x2C: { u64 a=x[0], s=x[1]; if((a|s)&0xFFF){ x[0]=R_BADADDR; return; }
    /* only map the holes */
    for(u64 p=a;p<a+s;){ MemBlock b; mem_query(p,&b); u64 e=b.addr+b.size; if(e>a+s) e=a+s; if(e<=p) break;
      if(b.state==MS_FREE){ if(mem_map(p,e-p,MS_NORMAL,PERM_RW)){ WARN("svc MapPhysicalMemory %llx size %llx: out of memory (the PC couldn't commit it)\n",(unsigned long long)p,(unsigned long long)(e-p)); x[0]=R_OUTOFMEM; return; } g_phys_mapped+=e-p; } p=e; }
    x[0]=0; return; }
  case 0x2D: { u64 a=x[0], s=x[1];
    for(u64 p=a;p<a+s;){ MemBlock b; mem_query(p,&b); u64 e=b.addr+b.size; if(e>a+s) e=a+s; if(e<=p) break;
      if(b.state==MS_NORMAL){ u64 n=e-p; g_phys_mapped= g_phys_mapped>n? g_phys_mapped-n : 0; } p=e; }
    mem_unmap(a,s); x[0]=0; return; }
  case 0x2E: x[0]=R_NOTFOUND; return;
  case 0x2F: x[0]=R_NOTFOUND; return;
  case 0x30: case 0x37: { u32 which=(u32)x[2]; x[0]=0; x[1]= which==0? mem_total() : which==1? 800 : which==2? 800 : which==3? 256 : 64; return; }
  case 0x31: { u32 which=(u32)x[2]; x[0]=0; x[1]= which==0? used_memory() : which==1? (u64)g_nthreads : 16; return; }
  case 0x32: x[0]=0; return;
  case 0x33: { KThread* n=(KThread*)h_get_type((u32)x[1],KO_THREAD); if(!n){ x[0]=R_BADHANDLE; return; }
    u8* p=GP(x[0]); memset(p,0,0x320); memcpy(p,n->cpu.x,29*8); memcpy(p+29*8,&n->cpu.x[29],8); memcpy(p+30*8,&n->cpu.x[30],8);
    memcpy(p+31*8,&n->cpu.x[31],8); memcpy(p+32*8,&n->cpu.pc,8); memcpy(p+0x110,n->cpu.v,0x200); x[0]=0; return; }
  case 0x34: { u64 a=x[0]; i32 b=(a&3)? 0 : (i32)gr32(a); arb_note('w',t,a,(u32)x[1],(i32)(u32)x[2],(i64)x[3],0,b,0);
    x[0]=svc_wait_addr(t,a,(u32)x[1],(i32)(u32)x[2],(i64)x[3]); arb_note('W',t,a,(u32)x[1],(i32)(u32)x[2],(i64)x[3],(u32)x[0],b,0); return; }
  case 0x35: { u64 a=x[0]; i32 b=(a&3)? 0 : (i32)gr32(a); pm_lock(&g_klock); int nw=wl_count(4,a); pm_unlock(&g_klock);
    x[0]=svc_signal_addr(a,(u32)x[1],(i32)(u32)x[2],(i32)(u32)x[3]); arb_note('S',t,a,(u32)x[1],(i32)(u32)x[2],(i32)(u32)x[3],(u32)x[0],b,nw); return; }
  case 0x45: { KEvent* e=kevent_new("user event",0); u32 w=h_new(&e->o), r=h_new(&e->o); x[0]=0; x[1]=w; x[2]=r; return; }
  case 0x4B: { x[0]=R_NOTIMPL; return; }
  case 0x6F: { /* GetSystemInfo(type, handle, subtype). newer SDKs abort on boot if this returns 0 */
    u32 ty=(u32)x[1]; u64 sub=x[3], o=0;
    if(ty==0) o= sub==0? mem_total() : sub==1? 0x1FB00000ull : sub==2? 0x29D00000ull : 0x6000000ull;   /* pool physical size */
    else if(ty==1) o= sub==0? used_memory() : 0x1000000ull;                                            /* pool used */
    else if(ty==2) o= sub==0? 1 : 0x50;                                                                  /* initial process id range */
    x[0]=0; x[1]=o; return; }
  default:
    WARN("SVC 0x%x not implemented (pc=%llx)\n",imm,(unsigned long long)c->pc);
    x[0]=R_NOTIMPL; return;
  }
}

/* dump code around an address */
static void kernel_dump_code(u64 ra){
  u64 a=(ra&~3ull)-0x180; MemBlock b; mem_query(ra,&b); if(b.state==MS_FREE || b.state==MS_INACCESSIBLE || !(b.perm&1)) return;
  if(a<b.addr) a=b.addr;
  LOG("    code %llx:",(unsigned long long)a);
  for(int i=0;i<0x70 && a+i*4<b.addr+b.size;i++) LOG("%s%08x",(i%16==0)?"\n     ":" ",gr32(a+i*4));
  LOG("\n"); }

/* stall dump: a thread that runs without SVCs (spinning in game code) has no useful state, so we sample where its
   host thread really is: the game function it spins in and that function's code */
static int g_dump_sample;
static int host_to_guest(u64 rip, u64* ga, u64* off){
  static u64 lo=~0ull, hi; static char lomod[64]; if(!g_mod || !g_mod->nentries) return 0;
  if(!hi){ for(u32 i=0;i<g_mod->nentries;i++){ u64 f=(u64)(uintptr_t)g_mod->entry_fn[i]; if(f<lo) lo=f; if(f>hi) hi=f; }
    u64 o; if(!plat_addr_module(lo,lomod,sizeof lomod,&o)) lomod[0]=0; }
  if(rip<lo || rip>hi+0x100000) return 0;
  if(lomod[0]){ char m[64]; u64 o; if(!plat_addr_module(rip,m,sizeof m,&o) || strcmp(m,lomod)) return 0; }
  u64 best=0, g=0; for(u32 i=0;i<g_mod->nentries;i++){ u64 f=(u64)(uintptr_t)g_mod->entry_fn[i]; if(f<=rip && f>best){ best=f; g=g_mod->entry_addr[i]; } }
  if(!best) return 0; *ga=g; *off=rip-best; return 1; }

static void sample_thread(KThread* t){
  { static int off=-1; if(off<0) off=getenv("SWR_NO_SAMPLER")!=NULL; if(off) return; }   /* SWR_NO_SAMPLER=1: stall reports without the pc samples */
  host_lock(); void* h=__atomic_load_n(&t->host,__ATOMIC_ACQUIRE); if(!h){ host_unlock(); return; }
  u64 pcs[64]; int n=0;
  for(int k=0;k<64;k++){ u64 pc; if(plat_thread_pc(h,&pc)) pcs[n++]=pc; plat_sleep_ns(2000000); }
  host_unlock();
  if(!n) return;
  struct { u64 ga, lo, hi; char mod[48]; int c; } H[16]; int nh=0;
  for(int k=0;k<n;k++){ u64 ga=0, off=0; char mod[48]=""; int g=host_to_guest(pcs[k],&ga,&off);
    if(!g){ if(!plat_addr_module(pcs[k],mod,sizeof mod,&off)){ snprintf(mod,sizeof mod,"?"); off=pcs[k]; } off&=~0x3Full; }
    int j; for(j=0;j<nh;j++) if(H[j].ga==ga && !strcmp(H[j].mod,mod) && (g || H[j].lo==off)) break;
    if(j==nh){ if(nh==16) continue; nh++; H[j].ga=ga; H[j].lo=H[j].hi=off; snprintf(H[j].mod,sizeof H[j].mod,"%s",mod); H[j].c=0; }
    H[j].c++; if(off<H[j].lo) H[j].lo=off; if(off>H[j].hi) H[j].hi=off; }
  LOG("    thread %llu: where it runs (%d samples, 2 ms apart):\n",(unsigned long long)t->id,n);
  u64 hot=0; int hc=0;
  for(int r=0;r<nh;r++){ int b=-1; for(int j=0;j<nh;j++) if(H[j].c>0 && (b<0 || H[j].c>H[b].c)) b=j; if(b<0) break;
    if(H[b].mod[0]) LOG("      %3d%%  %s+%llx\n",H[b].c*100/n,H[b].mod,(unsigned long long)H[b].lo);
    else { LOG("      %3d%%  game function %llx (recompiled code +%llx..+%llx)\n",H[b].c*100/n,(unsigned long long)H[b].ga,(unsigned long long)H[b].lo,(unsigned long long)H[b].hi);
      if(H[b].c>hc){ hc=H[b].c; hot=H[b].ga; } }
    H[b].c=-H[b].c; }
  /* registers as last stored (a tight loop may keep some in host registers) */
  LOG("    regs:"); for(int r=0;r<31;r++) LOG("%s x%d=%llx",(r%6==0)?"\n     ":"",r,(unsigned long long)t->cpu.x[r]); LOG("\n");
  if(hot){ MemBlock b; mem_query(hot,&b);
    if(b.state!=MS_FREE && b.state!=MS_INACCESSIBLE && (b.perm&4)){ LOG("    code %llx:",(unsigned long long)hot);
      for(int i=0;i<256 && hot+i*4<b.addr+b.size;i++) LOG("%s%08x",(i%16==0)?"\n     ":" ",gr32(hot+i*4)); LOG("\n"); } } }

/* threads.txt: per-thread state, used when the screen stops changing */
void kernel_dump_threads(void);
void kernel_dump_threads_stall(void){ extern void gpu_gl_stall_report(void); gpu_gl_stall_report(); g_dump_sample=1; kernel_dump_threads(); g_dump_sample=0; }

void kernel_dump_threads(void){
  static const char* kinds[]={"running/in svc","objects","mutex","condvar","address"};
  LOG("---- game thread state ----\n");
  for(int i=0;i<g_nthreads;i++){ KThread* t=g_threads[i]; if(!t || t->state==2) continue;
    int k=t->wait_kind; if(k<0||k>4) k=0;
    LOG("thread %llu '%s' prio %d core %d: %s", (unsigned long long)t->id, t->name, t->prio, t->core, kinds[k]);
    if(k==1) LOG(" [%s%s]", t->wait_name? t->wait_name : "?", t->wait_timeout<0? "" : " with timeout");
    if(k>=2){ u32 wv=gr32(t->wait_addr); LOG(" [addr %llx value %x]", (unsigned long long)t->wait_addr, wv);
      if(k==2){ KObj* ow=h_get(wv&~0x40000000u); if(ow && ow->type==KO_THREAD) LOG(" owner thread %llu", (unsigned long long)((KThread*)ow)->id); } }
    LOG("  lr=%llx pc=%llx sp=%llx\n",(unsigned long long)t->cpu.x[30],(unsigned long long)t->cpu.pc,(unsigned long long)t->cpu.x[31]);
    { u64 fp=t->cpu.x[29]; LOG("    stack:");
      for(int i=0;i<10 && fp>=AS_BASE && fp<AS_SIZE && !(fp&7);i++){ MemBlock b; mem_query(fp,&b); if(b.state==MS_FREE || b.state==MS_INACCESSIBLE) break;
        LOG(" %llx",(unsigned long long)gr64(fp+8)); fp=gr64(fp); }
      LOG("\n"); }
    /* Switch 2: a thread busy in a driver loop (NVN fence waits poll memory) shows its registers, the address it
       polls is usually among them */
    if(k==0 && (g_title_id>>56)==0x04){ LOG("    regs:"); for(int r=0;r<29;r++) LOG(" x%d=%llx",r,(unsigned long long)t->cpu.x[r]); LOG("\n"); }
  }
  /* running threads (main first): sample where they are */
  if(g_dump_sample){ int ns=0;
    if(g_main && g_main->state==1 && g_main->wait_kind==0){ sample_thread(g_main); ns++; }
    for(int i=0;i<g_nthreads && ns<((g_title_id>>56)==0x04? 12 : 4);i++){ KThread* t=g_threads[i]; if(!t || t==g_main || t->state!=1 || t->wait_kind!=0) continue; sample_thread(t); ns++; } }
  /* threads spinning on SleepThread: dump regs + nearby code */
  { {
    for(int i=0;i<g_nthreads;i++){ KThread* t=g_threads[i]; if(!t || t->state==2 || t->wait_kind!=0 || !t->sleep_n) continue;
      LOG("thread %llu looping on SleepThread (%llu times) from lr=%llx\n    regs:",(unsigned long long)t->id,(unsigned long long)t->sleep_n,(unsigned long long)t->sleep_lr);
      for(int r=0;r<31;r++) LOG("%s x%d=%llx",(r%6==0)?"\n     ":"",r,(unsigned long long)t->sleep_x[r]);
      LOG("\n");
      for(int r=0;r<31;r++){ u64 a=t->sleep_x[r]&~7ull; MemBlock b; if(a<AS_BASE || a>=AS_SIZE) continue; mem_query(a,&b);
        if(b.state==MS_FREE || b.state==MS_INACCESSIBLE || !(b.perm&1)) continue;
        /* stay inside the block: this dump runs every 15 s on a healthy game */
        LOG("    mem x%d [%llx]:",r,(unsigned long long)a); for(int j=0;j<8 && a+j*8+8<=b.addr+b.size;j++) LOG(" %llx",(unsigned long long)gr64(a+j*8)); LOG("\n"); }
      /* the object the loop polls is usually in x19..x23, so dump more of it plus one level of the pointers inside
         (the flag the loop waits for tends to live in a member object) */
      for(int r=19;r<=23;r++){ u64 a=t->sleep_x[r]&~7ull; MemBlock b; if(a<AS_BASE || a>=AS_SIZE) continue; mem_query(a,&b);
        if(b.state==MS_FREE || b.state==MS_INACCESSIBLE || !(b.perm&1)) continue;
        LOG("    obj x%d [%llx]:",r,(unsigned long long)a);
        for(int j=0;j<24 && a+j*8+8<=b.addr+b.size;j++) LOG("%s%llx",(j%8==0)?"\n      ":" ",(unsigned long long)gr64(a+j*8));
        LOG("\n");
        if(r!=19) continue;
        for(int j=0;j<12 && a+j*8+8<=b.addr+b.size;j++){ u64 q=gr64(a+j*8)&~7ull; MemBlock qb; if(q<AS_BASE || q>=AS_SIZE) continue; mem_query(q,&qb);
          if(qb.state==MS_FREE || qb.state==MS_INACCESSIBLE || !(qb.perm&1) || (qb.perm&4)) continue;   /* data only, not code */
          LOG("      [x19+%#x] -> %llx:",j*8,(unsigned long long)q);
          for(int k=0;k<44 && q+k*8+8<=qb.addr+qb.size;k++) LOG("%s%llx",(k%8==0)?"\n        ":" ",(unsigned long long)gr64(q+k*8));
          LOG("\n"); } }
      { u32 n=t->svc_hist_n; LOG("    thread %llu own SVCs (oldest first):\n",(unsigned long long)t->id);
        for(u32 k= n>24? n-24 : 0;k<n;k++){ typeof(&t->svc_hist[0]) h=&t->svc_hist[k%24];
          LOG("      %x %llx %llx %llx %llx -> %x  x%u  lr=%llx",h->imm,(unsigned long long)h->a[0],(unsigned long long)h->a[1],(unsigned long long)h->a[2],(unsigned long long)h->a[3],h->res,h->n,(unsigned long long)h->lr);
          /* WaitSynchronization: say what it waits on (a poll with timeout 0 that keeps timing out is waiting for
             an event nobody signals) */
          if(h->imm==0x18 && h->h0){ KObj* ko=h_get(h->h0); LOG("  waits on: %x=%s",h->h0,ko? (ko->name? ko->name : "?") : "(closed)"); }
          /* SendSyncRequest: which session */
          if(h->imm==0x21){ KObj* ko=h_get((u32)h->a[0]); LOG("  session: %s",ko? (ko->name? ko->name : "?") : "(closed)"); }
          LOG("\n"); } }
      /* the functions the loop calls each round (BLs in the 0x80 bytes before the sleep): their code, from the start */
      { u64 lr=t->sleep_lr&~3ull; MemBlock lb; mem_query(lr,&lb);
        if(lb.state!=MS_FREE && (lb.perm&4)) for(u64 a=lr-0x80;a<lr;a+=4){ if(a<lb.addr) continue; u32 ins=gr32(a);
          if((ins>>26)==0x25){ i64 off=(i64)((i32)(ins<<6)>>6)*4; u64 tgt=a+(u64)off; LOG("    loop calls %llx (from %llx)\n",(unsigned long long)tgt,(unsigned long long)a); kernel_dump_code(tgt+0x180); } } }
      u64 fp=t->cpu.x[29], ras[4]; int nra=0; ras[nra++]=t->sleep_lr;
      for(int j=0;j<3 && fp>=AS_BASE && fp<AS_SIZE && !(fp&7);j++){ MemBlock b; mem_query(fp,&b); if(b.state==MS_FREE || b.state==MS_INACCESSIBLE) break; ras[nra++]=gr64(fp+8); fp=gr64(fp); }
      for(int j=0;j<nra;j++) kernel_dump_code(ras[j]); }
    KThread* m=g_main; if(m){ u64 fp=m->cpu.x[29]; for(int j=0;j<4 && fp>=AS_BASE && fp<AS_SIZE && !(fp&7);j++){ MemBlock b; mem_query(fp,&b); if(b.state==MS_FREE || b.state==MS_INACCESSIBLE) break; kernel_dump_code(gr64(fp+8)); fp=gr64(fp); } } } }
  /* address waits: the last arbiter calls on each address (w=wait starts, W=wait returns, S=signal, before/after =
     the word in memory around the call) and the memory around it */
  { u64 seen[64]; int ns=0;
    for(int i=0;i<g_nthreads && ns<64;i++){ KThread* t=g_threads[i]; if(!t || t->state==2 || t->wait_kind!=4) continue;
      u64 a=t->wait_addr; int dup=0; for(int j=0;j<ns;j++) if(seen[j]==a) dup=1; if(dup) continue; seen[ns++]=a;
      pm_lock(&g_arb_lk); ArbSlot* sl=arb_slot(a,0); u32 hits= sl? sl->n : 0;
      LOG("  address %llx (now %x), %u arbiter calls (last 8):\n",(unsigned long long)a,gr32(a),hits);
      for(u32 q= hits>8? hits-8 : 0; q<hits; q++){ ArbRec* r=&sl->r[q&7];
        LOG("    %c thread %llu type %u value %d arg %lld -> %x  mem %d->%d waiters %u  lr=%llx\n",r->op,(unsigned long long)r->tid,r->type,r->value,(long long)r->arg,r->res,r->before,r->after,r->waiters,(unsigned long long)r->lr); }
      pm_unlock(&g_arb_lk);
      /* memory and code only for the interesting waits: main's, its neighbours, and unusual call sites */
      int same_lr=0; for(int j=0;j<g_nthreads;j++){ KThread* u=g_threads[j]; if(u && u->state!=2 && u->wait_kind==4 && u->cpu.x[30]==t->cpu.x[30]) same_lr++; }
      u64 ma= (g_main && g_main->wait_kind==4)? g_main->wait_addr : 0;
      if(!(t==g_main || (ma && (a>ma? a-ma : ma-a)<0x400) || same_lr<=3)) continue;
      { u64 b=(a&~7ull)-0x200; MemBlock mb; mem_query(b,&mb); if(mb.state!=MS_FREE && mb.state!=MS_INACCESSIBLE && b>=mb.addr){
          LOG("    mem [%llx]:",(unsigned long long)b); for(int j=0;j<72;j++) LOG("%s%llx",(j%8==0)?"\n     ":" ",(unsigned long long)gr64(b+j*8)); LOG("\n"); } }
      kernel_dump_code(t->cpu.x[30]);
      for(int j=0;j<g_nthreads;j++){ KThread* u=g_threads[j]; if(!u || u->state==2 || u->wait_kind!=4 || u->wait_addr!=a) continue;
        LOG("    thread %llu last SVCs:\n",(unsigned long long)u->id);
        for(u32 qn_=u->svc_hist_n, q= qn_>24? qn_-24 : 0; q<qn_; q++){ typeof(&u->svc_hist[0]) h=&u->svc_hist[q%24];
          LOG("      %02x %llx %llx %llx %llx -> %x  x%u  lr=%llx\n",h->imm,(unsigned long long)h->a[0],(unsigned long long)h->a[1],(unsigned long long)h->a[2],(unsigned long long)h->a[3],h->res,h->n,(unsigned long long)h->lr); } }
      /* objects around the address: code of their first virtual functions */
      { u64 b=(a&~7ull)-0x200; int nv=0; MemBlock mb; mem_query(b,&mb);
        if(mb.state!=MS_FREE && mb.state!=MS_INACCESSIBLE && b>=mb.addr) for(int j=0;j<72 && nv<2;j++){ u64 v=gr64(b+j*8); if(v<AS_BASE || v>=AS_SIZE || (v&7)) continue;
          MemBlock vb; mem_query(v,&vb); if(vb.state==MS_FREE || vb.state==MS_INACCESSIBLE || (vb.perm&4) || !(vb.perm&1)) continue;
          u64 f0=gr64(v); MemBlock fb; mem_query(f0,&fb); if(fb.state==MS_FREE || !(fb.perm&4)) continue;
          nv++; LOG("    vtable %llx (at %llx):",(unsigned long long)v,(unsigned long long)(b+j*8));
          for(int e=0;e<8;e++) LOG(" %llx",(unsigned long long)gr64(v+e*8)); LOG("\n");
          for(int e=0;e<6;e++){ u64 f=gr64(v+e*8); MemBlock eb; mem_query(f,&eb); if(eb.state==MS_FREE || !(eb.perm&4) || (f&3)) continue;
            LOG("    vfunc %d %llx:",e,(unsigned long long)f); for(int w=0;w<64 && f+w*4<eb.addr+eb.size;w++) LOG("%s%08x",(w%16==0)?"\n     ":" ",gr32(f+w*4)); LOG("\n"); } } }
    } }
  { { extern char g_ipc_ring[32][80]; extern u32 g_ipc_ring_n;
      LOG("  last SVCs:\n");
      for(u32 qn_=g_svc_ring_n, q=qn_>40? qn_-40 : 0; q<qn_; q++){ SvcRec* r=&g_svc_ring[q&63];
        LOG("    %02x %llx %llx %llx %llx -> %x %llx  lr=%llx\n",r->imm,(unsigned long long)r->a[0],(unsigned long long)r->a[1],(unsigned long long)r->a[2],(unsigned long long)r->a[3],r->res,(unsigned long long)r->o1,(unsigned long long)r->lr); }
      LOG("  last IPCs:\n");
      for(u32 qn_=g_ipc_ring_n, q=qn_>32? qn_-32 : 0; q<qn_; q++) LOG("    %s\n",g_ipc_ring[q&31]); } }
  LOG("---------------------------------------\n"); fflush(NULL);
}
