/* Copyright (C) 2021 Omkar Tuppe
 * This file is part of Nidhugg.
 *
 * Nidhugg is free software: you can redistribute it and/or modify it
 * under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * Nidhugg is distributed in the hope that it will be useful, but
 * WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program.  If not, see
 * <http://www.gnu.org/licenses/>.
 */

#include <config.h>
#ifndef __TLCM_TRACE_BUILDER_H__
#define __TLCM_TRACE_BUILDER_H__

#include "TSOPSOTraceBuilder.h"
#include "VClock.h"
#include "SymEv.h"
#include "WakeupTrees.h"
#include "Option.h"
#include "PrefixHeuristic.h"
#include "TLCMSchedules.h"

#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <set>
#include <queue>
#include <memory>



#include <boost/container/flat_map.hpp>
#include <llvm/ExecutionEngine/GenericValue.h>
#include <llvm/IR/Type.h>
#if defined(HAVE_LLVM_IR_DATALAYOUT_H)
#include <llvm/IR/DataLayout.h>
#elif defined(HAVE_LLVM_DATALAYOUT_H)
#include <llvm/DataLayout.h>
#endif
#include <llvm/ExecutionEngine/ExecutionEngine.h>

class TLCMTraceBuilder final : public TSOPSOTraceBuilder{
public:
  TLCMTraceBuilder(const Configuration &conf = Configuration::default_conf);
  virtual ~TLCMTraceBuilder() override;
  virtual bool schedule(int *proc, int *aux, int *alt, bool *dryrun) override;
  virtual void refuse_schedule() override;
  virtual void mark_available(int proc, int aux = -1) override;
  virtual void mark_unavailable(int proc, int aux = -1) override;
  virtual void cancel_replay() override;
  virtual bool is_replaying() const override;
  virtual void metadata(const llvm::MDNode *md) override;
  virtual bool sleepset_is_empty() const override;
  virtual bool check_for_cycles() override;
  virtual Trace *get_trace() const override;
  virtual bool reset() override;
  virtual IID<CPid> get_iid() const override;
	
		
	virtual int performWrite(void *ptr, llvm::GenericValue val, int typ) override;
  virtual int performRead(void *ptr, int typ) override;
  virtual void beginEvent(int tid) override;

  virtual void debug_print() const override;
  virtual bool cond_branch(bool cnd) override { return true; }

  virtual NODISCARD bool spawn() override;
  virtual NODISCARD bool store(const SymData &ml) override;
  virtual NODISCARD bool atomic_store(const SymData &ml) override;
  virtual NODISCARD bool atomic_rmw(const SymData &ml,RmwAction action) override;
  virtual NODISCARD bool compare_exchange
  (const SymData &sd, const SymData::block_type expected, bool success) override;
  virtual NODISCARD bool load(const SymAddrSize &ml) override;
  virtual NODISCARD bool full_memory_conflict() override;
  virtual NODISCARD bool fence() override;
  virtual NODISCARD bool join(int tgt_proc) override;
  virtual NODISCARD bool mutex_lock(const SymAddrSize &ml) override {return true;};
  virtual NODISCARD bool mutex_lock_fail(const SymAddrSize &ml) override{return true;};
  virtual NODISCARD bool mutex_trylock(const SymAddrSize &ml) override{return true;};
  virtual NODISCARD bool mutex_unlock(const SymAddrSize &ml) override{return true;};
  virtual NODISCARD bool mutex_init(const SymAddrSize &ml) override{return true;};
  virtual NODISCARD bool mutex_destroy(const SymAddrSize &ml) override{return true;};
  virtual NODISCARD bool cond_init(const SymAddrSize &ml) override{return true;};
  virtual NODISCARD bool cond_signal(const SymAddrSize &ml) override{return true;};
  virtual NODISCARD bool cond_broadcast(const SymAddrSize &ml) override{return true;};
  virtual NODISCARD bool cond_wait(const SymAddrSize &cond_ml,
                         const SymAddrSize &mutex_ml) override{return true;};
  virtual NODISCARD bool cond_awake(const SymAddrSize &cond_ml,
                          const SymAddrSize &mutex_ml) override{return true;};
  virtual NODISCARD int cond_destroy(const SymAddrSize &ml) override{return true;};
  virtual NODISCARD bool register_alternatives(int alt_count) override{return true;};
  virtual long double estimate_trace_count() const override;


  uint64_t tracecount();
  int total_tasks() const { return tasks_created;};

protected:
  /* An identifier for a thread. An index into this->threads.
   *
   * Even indexes are for real threads. Odd indexes i are for
   * auxiliary threads corresponding to the real thread at index i-1.
   */
  typedef int IPid;

  typedef unsigned Tid;

  /* An Access is a pair (tp,ml) representing an access to
   * memory. Accesses come in two varieties:
   *
   * (W_ALL_MEMORY,0) is considered as a store access to all memory.
   *
   * (tp,ml) with tp in {R,W}, is a Read or Write access to the byte
   * indicated by the pointer ml.
   */
  class Access{
  public:
    /* The type of memory access. */
    enum Type {R, W, W_ALL_MEMORY, NA} type;
    /* The accessed byte. */
    const void *ml;
    bool operator<(const Access &a) const{
      return type < a.type || (type == a.type && ml < a.ml);
    };
    bool operator==(const Access &a) const{
      return type == a.type && (type == NA || ml == a.ml);
    };
    Access() : type(NA), ml(0) {};
    Access(Type t, const void *m) : type(t), ml(m) {};
  };

  /* Various information about a thread in the current execution. */
  class Thread{
  public:
    Thread(const CPid &cpid, int spawn_event)
      : cpid(cpid), available(true), spawn_event(spawn_event) {};
    CPid cpid;
    /* Is the thread available for scheduling? */
    bool available;
    /* The index of the spawn event that created this thread, or -1 if
     * this is the main thread or one of its auxiliaries.
     */
    int spawn_event;
    /* Indices in prefix of the events of this process.
     */
    std::vector<unsigned> event_indices;
    
    std::vector<unsigned> rwevent_indices;//

    /* The iid-index of the last event of this thread, or 0 if it has not
     * executed any events yet.
     */
    int last_event_index() const { return event_indices.size(); }
    int last_rwevent_index() const { return rwevent_indices.size(); }
  };


  /* The threads in the current execution, in the order they were
   * created. Threads on even indexes are real, threads on odd indexes
   * i are the auxiliary threads corresponding to the real threads at
   * index i-1.
   */
  std::vector<Thread> threads;

  Option<unsigned> po_predecessor(unsigned i) const{
    if (prefix[i].iid.get_index() == 1) return nullptr;
    return find_process_event(prefix[i].iid.get_pid(), prefix[i].iid.get_index()-1);
  }

  /* The CPids of threads in the current execution. */
  CPidSystem CPS;

  /* A ByteInfo object contains information about one byte in
   * memory. In particular, it recalls which events have recently
   * accessed that byte.
   */
  class ByteInfo{
  public:
    ByteInfo() : last_update(-1) {};
    /* An index into prefix, to the latest update that accessed this
     * byte. last_update == -1 if there has been no update to this
     * byte.
     */
    int last_update;
  };
  std::map<SymAddr,ByteInfo> mem;
  /* Index into prefix pointing to the latest full memory conflict.
   * -1 if there has been no full memory conflict.
   */
  int last_full_memory_conflict;

  /* A Mutex represents a pthread_mutex_t object.
   */
  class Mutex{
  public:
    Mutex() : last_access(-1), last_lock(-1), locked(false) {};
    Mutex(int lacc) : last_access(lacc), last_lock(-1), locked(false) {};
    int last_access;
    int last_lock;
    bool locked;
  };
  /* A map containing all pthread mutex objects in the current
   * execution. The key is the position in memory of the actual
   * pthread_mutex_t object.
   */
  std::map<SymAddr,Mutex> mutexes;

  /* A CondVar represents a pthread_cond_t object. */
  class CondVar{
  public:
    CondVar() : last_signal(-1) {};
    CondVar(int init_idx) : last_signal(init_idx) {};
    /* Index in prefix of the latest call to either of
     * pthread_cond_init, pthread_cond_signal, or
     * pthread_cond_broadcast for this condition variable.
     *
     * -1 if there has been no such call.
     */
    int last_signal;
    /* For each thread which is currently waiting for this condition
     * variable, waiters contains the index into prefix of the event
     * where the thread called pthread_cond_wait and started waiting.
     */
    std::vector<int> waiters;
  };
  /* A map containing all pthread condition variable objects in the
   * current execution. The key is the position in memory of the
   * actual pthread_cond_t object.
   */
  std::map<SymAddr,CondVar> cond_vars;

  /* All currently deadlocked threads */
  boost::container::flat_map<SymAddr, std::vector<IPid>> mutex_deadlocks;
  
  
  
	
  /* Information about a (short) sequence of consecutive events by the
   * same thread. At most one event in the sequence may have conflicts
   * with other events, and if the sequence has a conflicting event,
   * it must be th
   */

  class Event{
  public:
    Event(const IID<IPid> &iid, int alt = 0, SymEv sym = {})
      : alt(0), size(1),iid(iid), pinned(false), origin_iid(iid), md(0), may_conflict(false),
        sym(std::move(sym)), tid(0), sleep_branch_trace_count(0), depth(0) {};
    /* Some instructions may execute in several alternative ways
     * nondeterministically. (E.g. malloc may succeed or fail
     * nondeterministically if Configuration::malloy_may_fail is set.)
     * Branch::alt is the index of the alternative for the first event
     * in this event sequence. The default execution alternative has
     * index 0. All events in this sequence, except the first, are
     * assumed to run their default execution alternative.
     */
    int alt;
    /* The number of events in this sequence. */
    int size;
    /* If this event should have its read-from preserved. */
    bool pinned;
    /* The identifier for the first event in this event sequence. */
    IID<IPid> iid;
    /* The IID of the program instruction which is the origin of this
     * event. For updates, this is the IID of the corresponding store
     * instruction. For other instructions origin_iid == iid.
     */
    IID<IPid> origin_iid;
    /* Metadata corresponding to the first event in this sequence. */
    const llvm::MDNode *md;
    /* The clock of the first event in this sequence. Only computed
     * after a full execution sequence has been explored.
     * above_clock excludes reversible incoming edges, and below_clock
     * encodes happens-before rather than happens-after.
     */
    VClock<IPid> clock, above_clock;
    /* Indices into prefix of events that happen before this one. */
    std::vector<unsigned> happens_after;
    /* Is it possible for any event in this sequence to have a
     * conflict with another event?
     */
    bool may_conflict;

    int read_from;
    
    
    /* Tid of Transaction */
    Tid tid;
    
    std::vector<int> can_read_from;
    std::map<int,bool> possible_reads; 
    std::set<int> happens_before;

    std::shared_ptr<CMSchedule> new_schedules;
    
    bool localread = false;
    
    bool swappable = true;

    bool current = false;

    int depth;

    const void * var;
    /* Symbolic representation of the globally visible operation of this event.
     * Empty iff !may_conflict
     */
    SymEv sym;
    /* For each previous IID that has been explored at this position
     * with the exact same prefix, some number of traces (both sleep
     * set blocked and otherwise) have been
     * explored. sleep_branch_trace_count is the total number of such
     * explored traces.
     */
   int sleep_branch_trace_count;
    
  };

  /* The fixed prefix of events in the current execution. This may be
   * either the complete sequence of events executed thus far in the
   * execution, or the events executed followed by the subsequent
   * events that are determined in advance to be executed.
   */
  std::vector<Event> prefix;
  VClockVec below_clocks;
  
  //TODO
  class RWEvent{
    public:
    RWEvent(IPid pid, Tid tid, unsigned eindex):pid(pid), tid(tid) , eindex(eindex) {};
  	
  	IPid pid;
  	Tid tid;
  	unsigned eindex;

    VClock<IPid> clock, above_clock;

    std::vector<Tid> happens_after;
    
    int read_from;
    std::unordered_map<const void *, llvm::GenericValue> global_variables;
    std::map<const void * , std::set<int>> hb_writes;
    std::unordered_map<int , std::unordered_set<Tid>> modification_order; // co //////////////////////////////////
    
    //std::vector<Tid> modification_order;
    std::unordered_map<int,VClock<IPid>> pi_clocks; // per process observed order

    SymEv eventType;
    const void * readVar;
    int prefix_index; // for reads
    //std::vector<std::pair<SymEv, Tid>> current_reads_vector; //SymEv

    //

    int get_pid() const{
      return pid;
    }

    int get_tid() const{
      return tid;
    }

    unsigned get_index() const{
      return eindex;
    }



  };
  std::vector<RWEvent> events;
  int event_idx;

  /* The index into prefix corresponding to the last event that was
   * scheduled. Has the value -1 when no events have been scheduled.
   */
  int prefix_idx;

  /* Whether the currently replaying event has had its sym set. */
  bool seen_effect;

  /* Are we currently replaying the events given in prefix from the
   * previous execution? Or are we executing new events by arbitrary
   * scheduling?
   */
  bool replay;

  /* Is the execution cancelled? If so, we must reset before anything
   * else can be executed.
   */
  bool cancelled;

  /* The number of events that were or are going to be replayed in the
   * current computation.
   */
  int replay_point;

  /* The latest value passed to this->metadata(). */
  const llvm::MDNode *last_md;

  IPid ipid(int proc, int aux) const {
    assert(aux == -1);
    assert(proc < int(threads.size()));
    return proc;
  };

  Event &curev() {
    assert(0 <= prefix_idx);
    assert(prefix_idx < int(prefix.size()));
    return prefix[prefix_idx];
  };

  const Event &curev() const {
    assert(0 <= prefix_idx);
    assert(prefix_idx < int(prefix.size()));
    return prefix[prefix_idx];
  };

  /* Perform the logic of atomic_store(), aside from recording a
   * symbolic event.
   */
  void do_atomic_store(const SymData &ml);
  /* Perform the logic of load(), aside from recording a symbolic
   * event.
   */
  void do_load(const SymAddrSize &ml);

  /* Finds the index in prefix of the event of process pid that has iid-index
   * index.
   */
  Option<unsigned> try_find_process_event(IPid pid, int index) const;
  unsigned find_process_event(IPid pid, int index) const;
  /* Pretty-prints the iid of prefix[pos]. */
  std::string iid_string(std::size_t pos) const;
  /* Pretty-prints the iid of event. */
  std::string iid_string(const Event &event) const;
  /* Pretty-prints an iid. */
  std::string iid_string(IID<IPid> iid) const;
  /* Adds a reversible co-enabled happens-before edge between the
   * current event and event.
   */
  void add_noblock_race(int event);
  /* Adds an observed race between first and second that is observed by
   * the current event.
   */
  void add_observed_race(int first, int second);
  /* Computes a mapping between IPid and current local clock value
   * (index) of that process after executing the prefix [0,event).
   */
  std::vector<int> iid_map_at(int event) const;
  /* Plays an iid_map forward by one event. */
  void iid_map_step(std::vector<int> &iid_map, const Event &event) const;
  /* Reverses an iid_map by one event. */
  void iid_map_step_rev(std::vector<int> &iid_map, const Event &event) const;
  /* Adds a non-reversible happens-before edge between first and
   * second.
   */
  void add_happens_after(unsigned second, unsigned first);
  /* Adds a non-reversible happens-before edge between the last event
   * executed by thread (if there is such an event), and second.
   */
  void add_happens_after_thread(unsigned second, IPid thread);
  /* Computes the vector clocks of all events in a complete execution
   * sequence from happens_after and race edges.
   */
  void compute_vclocks();
  int compute_above_clock(unsigned event);

  /* Checks whether an event is included in a vector clock. */
  bool happens_before(const RWEvent &e, const VClock<IPid> &c) const;
  
  bool NODISCARD record_symbolic(SymEv event);
  /* Estimate the total number of traces that have the same prefix as
   * the current one, up to the first idx events.
   */
  long double estimate_trace_count(int idx) const;

  bool is_load(unsigned idx) const;
  bool is_store(unsigned idx) const;
  bool is_store_when_reading_from(unsigned idx, int read_from) const;
  bool is_minit(unsigned idx) const;
  bool is_mdelete(unsigned idx) const;

  SymAddrSize get_addr(unsigned idx) const;
  SymData get_data(int idx, const SymAddrSize &addr) const;
  
  //TODO:

  int tasks_created = 0;
  int temp = 1;
  int tp = 100;
  std::vector<Event> replay_events;
  //std::vector<Transaction> replay_transactions;

  std::vector<std::pair<int,int>> record_replays_for_events;

  TLCMSchedules ccvschedules;
  std::unordered_map<int,std::shared_ptr<CMSEvent>> current_schedules; // depth->CMSEvent

  //unsigned find_process_transaction(IPid pid, int index) const;
  //bool is_begin(unsigned idx) const;
  //bool is_end(unsigned idx) const;
  bool has_store_on_var(const void *ptr, unsigned i) const;
  //bool transaction_happens_before(const Transaction &t, const VClock<int> &clock) const;
  //void add_transaction_happens_after(Tid second, Tid first);
  //void add_transaction_happens_after_thread(Tid second, IPid thread);
  void createSchedules(int tid, void *ptr) { return;};
  void createSchedule(int tid);
  void record_replay(int eindex , int tindex);
  bool is_equivalent(std::vector<std::vector<CMSEvent>> &schedules , std::vector<CMSEvent> this_schedule);
  void add_to_queue();
  void append_replay_events(std::vector<CMSEvent> &events_before, std::vector<Event> &new_prefix);

  
			 //void endTransaction(int tid);
			 //void createNextEvent();
			
};

#endif
