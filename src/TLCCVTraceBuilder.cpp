/* Copyright (C) 2021 Omkar Tuppe 
 *
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

#include "Debug.h"
#include "TLCCVTraceBuilder.h"
#include "PrefixHeuristic.h"
#include "Timing.h"
#include "TraceUtil.h"
#include "Interpreter.h"
#include <sstream>
#include <stdexcept>
#include <set>
#include <iterator>

#define ANSIRed "\x1b[91m"
#define ANSIRst "\x1b[m"

#ifndef NDEBUG
#  define IFDEBUG(X) X
#else
#  define IFDEBUG(X)
#endif

static Timing::Context analysis_context("analysis");
static Timing::Context vclocks_context("vclocks");
static Timing::Context unfolding_context("unfolding");
static Timing::Context neighbours_context("neighbours");
static Timing::Context try_read_from_context("try_read_from");
static Timing::Context ponder_mutex_context("ponder_mutex");

TLCCVTraceBuilder::TLCCVTraceBuilder(const Configuration &conf)
    : TSOPSOTraceBuilder(conf) {
    threads.push_back(Thread(CPid(), -1));
    prefix_idx = -1;
    event_idx  = -1;
    replay = false;
    cancelled = false;
    last_full_memory_conflict = -1;
    last_md = 0;
    replay_point = 0;
    tasks_created = 0;
}

TLCCVTraceBuilder::~TLCCVTraceBuilder(){
}

bool TLCCVTraceBuilder::schedule(int *proc, int *aux, int *alt, bool *dryrun){
  if (cancelled) {
    assert(!std::any_of(threads.begin(), threads.end(), [](const Thread &t) {
                                                          return t.available;
                                                        }));
    return false;
  }
  *dryrun = false;
  *alt = 0;
  *aux = -1; /* No auxilliary threads in TLCCV */
  if(replay){
     if (0 <= prefix_idx && threads[curev().iid.get_pid()].last_event_index() <
        curev().iid.get_index() + curev().size - 1) {
      //Continue executing the current Event 
      IPid pid = curev().iid.get_pid();
      *proc = pid;
      *alt = 0;
      if(!(threads[pid].available)) {
        llvm::dbgs() << "Trying to play process " << threads[pid].cpid << ", but it is blocked\n";
        llvm::dbgs() << "At replay step " << prefix_idx << ", iid "
                     << iid_string(IID<IPid>(pid, threads[curev().iid.get_pid()].last_event_index()))
                     << "\n";

        abort();
      }
      threads[pid].event_indices.push_back(prefix_idx);
      return true;
     }
    else if(prefix_idx + 1 == int(prefix.size())){
        replay = false;
      }
     else{
      // Go to the next event. 
      assert(prefix_idx < 0 || prefix_idx < prefix.size());
      seen_effect = false;
      ++prefix_idx;
      IPid pid = curev().iid.get_pid();
      *proc = pid;
      *alt = curev().alt;
      assert(threads[pid].available);
      threads[pid].event_indices.push_back(prefix_idx);
      return true;
    }
  }

  assert(!replay);
  /* Create a new Event */

  // TEMP: Until we have a SymEv for store()
  // assert(prefix_idx < 0 || !!curev().sym.size() == curev().may_conflict);

  /* Should we merge the last two events? */
  if(prefix.size() > 1 &&
     prefix[prefix.size()-1].iid.get_pid()
     == prefix[prefix.size()-2].iid.get_pid() &&
     !prefix[prefix.size()-1].may_conflict){
    assert(curev().sym.empty()); // Would need to be copied 
    assert(curev().sym.empty()); // Can't happen 
    prefix.pop_back();
    --prefix_idx;
    ++curev().size;
    assert(int(threads[curev().iid.get_pid()].event_indices.back()) == prefix_idx + 1);
    threads[curev().iid.get_pid()].event_indices.back() = prefix_idx;
  }


  /* Find an available thread. */
  for(unsigned p = 0; p < threads.size(); ++p){ // Loop through real threads
    if(threads[p].available &&
       (conf.max_search_depth < 0 || threads[p].last_event_index() < conf.max_search_depth)){
      /* Create a new Event */
      seen_effect = false;
      ++prefix_idx;
      assert(prefix_idx == int(prefix.size()));
      threads[p].event_indices.push_back(prefix_idx);
      prefix.emplace_back(IID<IPid>(IPid(p),threads[p].last_event_index()));
      *proc = p;
      return true;
    }
  }

  return false; // No available threads
}

void TLCCVTraceBuilder::refuse_schedule(){
  assert(prefix_idx == int(prefix.size())-1);
  assert(curev().size == 1);
  assert(!curev().may_conflict);
  IPid last_pid = curev().iid.get_pid();
  prefix.pop_back();
  assert(int(threads[last_pid].event_indices.back()) == prefix_idx);
  threads[last_pid].event_indices.pop_back();
  --prefix_idx;
  mark_unavailable(last_pid);
}

void TLCCVTraceBuilder::mark_available(int proc, int aux){
  threads[ipid(proc,aux)].available = true;
}

void TLCCVTraceBuilder::mark_unavailable(int proc, int aux){
  threads[ipid(proc,aux)].available = false;
}

bool TLCCVTraceBuilder::is_replaying() const {
  return prefix_idx < replay_point;
}

void TLCCVTraceBuilder::cancel_replay(){
  assert(replay == is_replaying());
  cancelled = true;
  replay = false;
}

void TLCCVTraceBuilder::metadata(const llvm::MDNode *md){
  if(curev().md == 0){
    curev().md = md;
  }
  last_md = md;
}

bool TLCCVTraceBuilder::sleepset_is_empty() const{
  return true;
}

Trace *TLCCVTraceBuilder::get_trace() const{
  std::vector<IID<CPid> > cmp;
  SrcLocVectorBuilder cmp_md;
  //TIDSeqTraceBuilder cmp_trns;
  std::vector<Error*> errs;
  for(unsigned i = 0; i < prefix.size(); ++i) {
    cmp.push_back(IID<CPid>(threads[prefix[i].iid.get_pid()].cpid,prefix[i].iid.get_index()));
    cmp_md.push_from(prefix[i].md);
  }
  
  for(unsigned i = 0; i < errors.size(); ++i){
    errs.push_back(errors[i]->clone());
  }
  Trace *t = new IIDSeqTrace(cmp,cmp_md.build(),errs);
  t->set_blocked(!sleepset_is_empty());
  return t;
}

void TLCCVTraceBuilder::append_replay_events(std::vector<SEvent> &events_before, std::vector<Event> &new_prefix){
  // earlier events for replay 
  for( int i =0 ; i < events_before.size() ; i++){
    const SEvent &se = events_before[i];
    int pid = se.iid.get_pid();
    int index = se.iid.get_index();
    IID<IPid> iid(pid, index);
    new_prefix.emplace_back(iid);
    new_prefix.back().size = se.size;
    new_prefix.back().sym = se.sym;
    new_prefix.back().pinned = se.pinned;
    new_prefix.back().read_from = se.read_from;
    new_prefix.back().swappable = se.swappable;
    new_prefix.back().depth = se.depth;
    //new_prefix.back().tid = se.tid; 
    new_prefix.back().new_schedules = se.new_schedules;
  }
}
bool TLCCVTraceBuilder::reset(){

  if( prefix.size() <= 0)
    return false;

  if(!record_replays_for_events.empty()){
    for(auto event: record_replays_for_events){
      record_replay(event.first,event.second);
    }
  }
  //temp = ccvschedules.scheduler.top()->depth;
  int cur_events = -1;
  int tidx=0;
  std::vector<Event> new_prefix;
  //////////////////////////////////////////////////////////////////////////////////////////////////
  while(true){
    if(!ccvschedules.scheduler.top()->new_read_from.empty() || !ccvschedules.scheduler.top()->new_schedules->scheduled_events.empty()){
      break;
    }
    else{
      current_schedules.erase(ccvschedules.scheduler.top()->depth);
      ccvschedules.scheduler.pop();
    }
  }
  if(!ccvschedules.scheduler.top()->new_read_from.empty() || !ccvschedules.scheduler.top()->new_schedules->scheduled_events.empty()) {
    if(!ccvschedules.scheduler.top()->new_read_from.empty()) { //New read source
      cur_events = ccvschedules.scheduler.top()->depth;

      int new_read = ccvschedules.scheduler.top()->new_read_from.back();
      ccvschedules.scheduler.top()->read_from = new_read;
      ccvschedules.scheduler.top()->new_read_from.pop_back();//remove this read
      ccvschedules.scheduler.top()->new_schedules->new_read_from.pop_back();

      //add earlier events for replay
      append_replay_events(ccvschedules.scheduler.top()->new_schedules->events_before, new_prefix);

      //add current event to replay
      {
        int pid = ccvschedules.scheduler.top()->iid.get_pid();
        int index = ccvschedules.scheduler.top()->iid.get_index();
        IID<IPid> eiid(pid, index);
        new_prefix.emplace_back(eiid);
        new_prefix.back().size = ccvschedules.scheduler.top()->size;
        new_prefix.back().sym = ccvschedules.scheduler.top()->sym;
        new_prefix.back().pinned = ccvschedules.scheduler.top()->pinned;
        new_prefix.back().read_from = new_read;
        new_prefix.back().swappable = ccvschedules.scheduler.top()->swappable;
        new_prefix.back().depth = ccvschedules.scheduler.top()->depth;
        //new_prefix.back().tid = ccvschedules.scheduler.top()->tid; 
        new_prefix.back().new_schedules = ccvschedules.scheduler.top()->new_schedules;
      }
    }
    //*****Create Schedules for postponed writes
    else{
      //add earlier events for replay
      append_replay_events(ccvschedules.scheduler.top()->new_schedules->events_before, new_prefix);

      int read_tid;
      std::vector<SEvent> &schedule = ccvschedules.scheduler.top()->new_schedules->scheduled_rwevents.back();
      for(unsigned i=0 ; i < schedule.size() ; i++) {
        read_tid = schedule[i].tid;
      }
      //update read source
      ccvschedules.scheduler.top()->read_from = read_tid - 1; // RWEvent index in vector events
      {
        //add the scheduled events to reply
        std::vector<SEvent> &scheduled_events = ccvschedules.scheduler.top()->new_schedules->scheduled_events.back();
        for( int i =0 ; i < scheduled_events.size() ; i++) {
          SEvent &se = scheduled_events[i];
          int pid = se.iid.get_pid();
          int index = se.iid.get_index();
          IID<IPid> iid(pid, index);
          new_prefix.emplace_back(iid);
          new_prefix.back().size = se.size;
          new_prefix.back().sym = se.sym;
          new_prefix.back().pinned = se.pinned;
          new_prefix.back().read_from = se.read_from;
          new_prefix.back().swappable = false;
          new_prefix.back().depth = se.depth;
          //new_prefix.back().tid = se.tid; 
          new_prefix.back().new_schedules = se.new_schedules;
        }

        //Remove this schedule form this event
        ccvschedules.scheduler.top()->new_schedules->scheduled_events.pop_back();
        ccvschedules.scheduler.top()->new_schedules->scheduled_rwevents.pop_back();

        //Add this read event to the replay
        int pid = ccvschedules.scheduler.top()->iid.get_pid();
        int index = ccvschedules.scheduler.top()->iid.get_index();
        IID<IPid> eiid(pid, index);
        new_prefix.emplace_back(eiid);
        new_prefix.back().size = ccvschedules.scheduler.top()->size;
        new_prefix.back().sym = ccvschedules.scheduler.top()->sym;
        new_prefix.back().pinned = ccvschedules.scheduler.top()->pinned;
        new_prefix.back().read_from = read_tid - 1;//ccvschedules.scheduler.top()->read_from;//updated read
        new_prefix.back().swappable = false;
        new_prefix.back().new_schedules = ccvschedules.scheduler.top()->new_schedules;
      }
        
      cur_events = new_prefix.size();
    }
  }

  if(ccvschedules.scheduler.top()->new_read_from.empty() && ccvschedules.scheduler.top()->new_schedules->scheduled_events.empty()) {
    current_schedules.erase(ccvschedules.scheduler.top()->depth);
    ccvschedules.scheduler.pop();
  }
///////////////////////////////////////////////////////////////////////////////////////////////////
  
  prefix = std::move(new_prefix);

  event_idx = -1;
  prefix_idx = -1;
  events.clear();
  record_replays_for_events.clear();
  replay = true;
  //replay = false; 
  replay_point = cur_events+1;
  //replay_point = 0;
  tasks_created = 0;


  CPS = CPidSystem();
  threads.clear();
  threads.push_back(Thread(CPid(),-1));
  mutexes.clear();
  cond_vars.clear();
  mem.clear();
  mutex_deadlocks.clear();
  last_full_memory_conflict = -1;
  
  cancelled = false;
  last_md = 0;  
  reset_cond_branch_log();

  return true;
}

IID<CPid> TLCCVTraceBuilder::get_iid() const{
  IPid pid = curev().iid.get_pid();
  int idx = curev().iid.get_index();
  return IID<CPid>(threads[pid].cpid,idx);
}

static std::string rpad(std::string s, int n){
  while(int(s.size()) < n) s += " ";
  return s;
}

static std::string lpad(const std::string &s, int n){
  return std::string(std::max(0, n - int(s.size())), ' ') + s;
}

std::string TLCCVTraceBuilder::iid_string(std::size_t pos) const{
  return iid_string(prefix[pos]);
}

std::string TLCCVTraceBuilder::iid_string(const Event &event) const{
  IPid pid = event.iid.get_pid();
  int index = event.iid.get_index();
  std::stringstream ss;
  ss << "(" << threads[pid].cpid << "," << index;
  if(event.size > 1){
    ss << "-" << index + event.size - 1;
  }
  ss << ")";
  if(event.alt != 0){
    ss << "-alt:" << event.alt;
  }
  return ss.str();
}

std::string TLCCVTraceBuilder::iid_string(IID<IPid> iid) const{
  return iid_string(find_process_event(iid.get_pid(), iid.get_index()));
}

void TLCCVTraceBuilder::debug_print() const {
  llvm::dbgs() << "TLCCVTraceBuilder (debug print, replay until " << replay_point << "):\n";
  int idx_offs = 0;
  int iid_offs = 0;
  int rf_offs = 0;
  int clock_offs = 0;
  std::vector<std::string> lines(prefix.size(), "");

  for(unsigned i = 0; i < prefix.size(); ++i){
    IPid ipid = prefix[i].iid.get_pid();
    idx_offs = std::max(idx_offs,int(std::to_string(i).size()));
    iid_offs = std::max(iid_offs,2*ipid+int(iid_string(i).size()));
    rf_offs = std::max(rf_offs,prefix[i].read_from ?
                       int(std::to_string(prefix[i].read_from).size())
                       : 1);
    clock_offs = std::max(clock_offs,int(prefix[i].clock.to_string().size()));
    lines[i] = prefix[i].sym.to_string();
  }

  for(unsigned i = 0; i < prefix.size(); ++i){
    IPid ipid = prefix[i].iid.get_pid();
    llvm::dbgs() << " " << lpad(std::to_string(i),idx_offs)
                 << rpad("",1+ipid*2)
                 << rpad(iid_string(i),iid_offs-ipid*2)
                 << " " << lpad((prefix[i].pinned ? "*" : ""),rf_offs)
                 << " " << lpad(prefix[i].read_from ? std::to_string(prefix[i].read_from) : "-",rf_offs)
                 << " " << rpad(prefix[i].clock.to_string(),clock_offs)
                 << " " << lines[i] << "\n";
  }
  for (unsigned i = prefix.size(); i < lines.size(); ++i){
    llvm::dbgs() << std::string(2+iid_offs + 1+clock_offs, ' ') << lines[i] << "\n";
  }
  if(errors.size()){
    llvm::dbgs() << "Errors:\n";
    for(unsigned i = 0; i < errors.size(); ++i){
      llvm::dbgs() << "  Error #" << i+1 << ": "
                   << errors[i]->to_string() << "\n";
    }
  } 
}

bool TLCCVTraceBuilder::spawn(){
  IPid parent_ipid = curev().iid.get_pid();
  CPid child_cpid = CPS.spawn(threads[parent_ipid].cpid);
  threads.push_back(Thread(child_cpid,prefix_idx));
  curev().may_conflict = true;
  bool res = record_symbolic(SymEv::Spawn(threads.size() - 1));
  return res;
}

bool TLCCVTraceBuilder::store(const SymData &sd){
  assert(false && "Cannot happen");
  abort();
  return true;
}

bool TLCCVTraceBuilder::atomic_store(const SymData &sd){
  if (!record_symbolic(SymEv::Store(sd))) return false;
  if(!events.empty() && curev().iid.get_pid() == events.back().get_pid()) 
    curev().tid = events[event_idx].tid;
  //do_atomic_store(sd);
  events.back().eventType = curev().sym;
  return true;
}

void TLCCVTraceBuilder::do_atomic_store(const SymData &sd){
  const SymAddrSize &ml = sd.get_ref();
  curev().may_conflict = true;

  /* See previous updates reads to ml */
  for(SymAddr b : ml){
    ByteInfo &bi = mem[b];

    /* Register in memory */
    bi.last_update = prefix_idx;
  }
}

bool TLCCVTraceBuilder::atomic_rmw(const SymData &sd ,  RmwAction action){
  return true;
}

bool TLCCVTraceBuilder::load(const SymAddrSize &ml){
  if (!record_symbolic(SymEv::Load(ml))) return false;
  if(!events.empty() && curev().iid.get_pid() == events.back().get_pid()) 
    curev().tid = events[event_idx].tid;
  //do_load(ml);
  events.back().eventType = curev().sym;
  events.back().prefix_index = prefix_idx;
  return true;
}

void TLCCVTraceBuilder::do_load(const SymAddrSize &ml){
  curev().may_conflict = true;
  int lu = mem[ml.addr].last_update;
  curev().read_from = lu;

  assert(lu == -1 || get_addr(lu) == ml);
  assert(std::all_of(ml.begin(), ml.end(), [lu,this](SymAddr b) {
             return mem[b].last_update == lu;
           }));
}

bool TLCCVTraceBuilder::compare_exchange
(const SymData &sd, const SymData::block_type expected, bool success){
  if(success){
    if (!record_symbolic(SymEv::CmpXhg(sd, expected))) return false;
    do_load(sd.get_ref());
    do_atomic_store(sd);
  }else{
    if (!record_symbolic(SymEv::CmpXhgFail(sd, expected))) return false;
    do_load(sd.get_ref());
  }
  return true;
}

bool TLCCVTraceBuilder::full_memory_conflict(){
  invalid_input_error("TLCCV does not support black-box functions with memory effects");
  return false;
  if (!record_symbolic(SymEv::Fullmem())) return false;
  curev().may_conflict = true;

  // /* See all pervious memory accesses */
  // for(auto it = mem.begin(); it != mem.end(); ++it){
  //   do_load(it->second);
  // }
  // last_full_memory_conflict = prefix_idx;

  // /* No later access can have a conflict with any earlier access */
  // mem.clear();
  return true;
}

bool TLCCVTraceBuilder::fence(){
  return true;
}

bool TLCCVTraceBuilder::join(int tgt_proc){
  bool r = record_symbolic(SymEv::Join(tgt_proc));
  if(!r)  return false;
  curev().may_conflict = true;
  add_happens_after_thread(prefix_idx, tgt_proc);
  return true;
}


template <class Iter>
static void rev_recompute_data
(SymData &data, VecSet<SymAddr> &needed, Iter end, Iter begin){
  for (auto pi = end; !needed.empty() && (pi != begin);){
    const SymEv &p = *(--pi);
    switch(p.kind){
    case SymEv::STORE:
    case SymEv::UNOBS_STORE:
    case SymEv::RMW:
    case SymEv::CMPXHG:
      if (data.get_ref().overlaps(p.addr())) {
        for (SymAddr a : p.addr()) {
          if (needed.erase(a)) {
            data[a] = p.data()[a];
          }
        }
      }
      break;
    default:
      break;
    }
  }
}

void TLCCVTraceBuilder::add_happens_after(unsigned second, unsigned first){
  assert(first != ~0u);
  assert(second != ~0u);
  assert(first != second);
  assert(first < second);
  assert((long long)second <= prefix_idx);

  std::vector<unsigned> &vec = prefix[second].happens_after;
  if (vec.size() && vec.back() == first) return;

  vec.push_back(first);
}

void TLCCVTraceBuilder::add_happens_after_thread(unsigned second, IPid thread){
  assert((int)second == prefix_idx);
  if (threads[thread].event_indices.empty()) return;
  add_happens_after(second, threads[thread].event_indices.back());
}

/* Filter the sequence first..last from all elements that are less than
 * any other item. The sequence is modified in place and an iterator to
 * the position beyond the last included element is returned.
 *
 * Assumes less is transitive and asymetric (a strict partial order)
 */
template< class It, class LessFn >
static It frontier_filter(It first, It last, LessFn less){
  It fill = first;
  for (It current = first; current != last; ++current){
    bool include = true;
    for (It check = first; include && check != fill;){
      if (less(*current, *check)){
        include = false;
        break;
      }
      if (less(*check, *current)){
        /* Drop check from fill set */
        --fill;
        std::swap(*check, *fill);
      }else{
        ++check;
      }
    }
    if (include){
      /* Add current to fill set */
      if (fill != current) std::swap(*fill, *current);
      ++fill;
    }
  }
  return fill;
}



bool TLCCVTraceBuilder::record_symbolic(SymEv event){
  if (!replay) {
    assert(!seen_effect);
    /* New event */
    curev().sym = std::move(event);
    seen_effect = true;
  } else {
    /* Replay. SymEv::set() asserts that this is the same event as last time. */
    SymEv &last = curev().sym;
    assert(!seen_effect);
    if (!last.is_compatible_with(event)) {
      auto pid_str = [this](IPid p) { return threads[p].cpid.to_string(); };
      nondeterminism_error("Event with effect " + last.to_string(pid_str)
                           + " became " + event.to_string(pid_str)
                           + " when replayed");
      return false;
    }
    last = event;
    seen_effect = true;
  }
  return true;
}


bool TLCCVTraceBuilder::is_load(unsigned i) const {
  const SymEv &e = prefix[i].sym;
  return e.kind == SymEv::LOAD;
}

bool TLCCVTraceBuilder::is_minit(unsigned i) const {
  return prefix[i].sym.kind == SymEv::M_INIT;
}

bool TLCCVTraceBuilder::is_mdelete(unsigned i) const {
  return prefix[i].sym.kind == SymEv::M_DELETE;
}


bool TLCCVTraceBuilder::is_store(unsigned i) const {
  const SymEv &e = prefix[i].sym;
  return e.kind == SymEv::STORE;
}


bool TLCCVTraceBuilder::is_store_when_reading_from(unsigned i, int read_from) const {
  const SymEv &e = prefix[i].sym;
  if (e.kind == SymEv::STORE || e.kind == SymEv::RMW)
    return true;
  if (e.kind != SymEv::CMPXHG && e.kind != SymEv::CMPXHGFAIL) return false;
  SymData expected = e.expected();
  SymData actual = get_data(read_from, e.addr());
  assert(e.addr() == actual.get_ref());
  return memcmp(expected.get_block(), actual.get_block(), e.addr().size) == 0;
}

SymAddrSize TLCCVTraceBuilder::get_addr(unsigned i) const {
  const SymEv &e = prefix[i].sym;
  if (e.has_addr()) {
    return e.addr();
  }
  abort();
}

SymData TLCCVTraceBuilder::get_data(int i, const SymAddrSize &addr) const {
  if (i == -1) {
    SymData ret(addr, addr.size);
    memset(ret.get_block(), 0, addr.size);
    return ret;
  }
  const SymEv &e = prefix[i].sym;
  assert(e.has_data());
  assert(e.addr() == addr);
  return e.data();
}


bool TLCCVTraceBuilder::happens_before(const RWEvent &e,
                                     const VClock<int> &c) const {
  IID<IPid> eiid(e.get_pid(),e.get_index());
  return c.includes(eiid);
}



std::vector<int> TLCCVTraceBuilder::iid_map_at(int event) const{
  std::vector<int> map(threads.size(), 1);
  for (int i = 0; i < event; ++i) {
    iid_map_step(map, prefix[i]);
  }
  return map;
}

void TLCCVTraceBuilder::iid_map_step(std::vector<int> &iid_map, const Event &event) const{
  if (iid_map.size() <= unsigned(event.iid.get_pid())) iid_map.resize(event.iid.get_pid()+1, 1);
  iid_map[event.iid.get_pid()] += event.size;
}

void TLCCVTraceBuilder::iid_map_step_rev(std::vector<int> &iid_map, const Event &event) const{
  iid_map[event.iid.get_pid()] -= event.size;
}

inline Option<unsigned> TLCCVTraceBuilder::try_find_process_event(IPid pid, int index) const{
  assert(pid >= 0 && pid < int(threads.size()));
  assert(index >= 1);
  if (index > int(threads[pid].event_indices.size())){
    return nullptr;
  }

  unsigned k = threads[pid].event_indices[index-1];
  assert(k < prefix.size());
  assert(prefix[k].size > 0);
  assert(prefix[k].iid.get_pid() == pid
         && prefix[k].iid.get_index() <= index
         && (prefix[k].iid.get_index() + prefix[k].size) > index);

  return k;
}

inline unsigned TLCCVTraceBuilder::find_process_event(IPid pid, int index) const{
  assert(pid >= 0 && pid < int(threads.size()));
  assert(index >= 1 && index <= int(threads[pid].rwevent_indices.size()));
  unsigned k = threads[pid].rwevent_indices[index-1];
  assert(k < events.size());
  assert(events[k].get_pid() == pid
         && events[k].get_index() == index);

  return k;
}



long double TLCCVTraceBuilder::estimate_trace_count() const{
  return estimate_trace_count(0);
}

bool TLCCVTraceBuilder::check_for_cycles() {
  return false;
}

long double TLCCVTraceBuilder::estimate_trace_count(int idx) const{
  if(idx > int(prefix.size())) return 0;
  if(idx == int(prefix.size())) return 1;

  long double count = 42;
  for(int i = int(prefix.size())-1; idx <= i; --i){
    count += prefix[i].sleep_branch_trace_count;
    // count += std::max(0, int(prefix.children_after(i)))
    //   * (count / (1 + prefix[i].sleep.size()));
  }

  return count;
}

/////////////////////////////////////////////////////////////....................................
void TLCCVTraceBuilder::beginEvent(int tid){
  assert(tid > 0);
  IPid pid = curev().iid.get_pid();
  ++event_idx;
  assert(event_idx == int(events.size()));
  threads[pid].rwevent_indices.emplace_back(event_idx);
  unsigned tidx = threads[pid].last_rwevent_index();
  RWEvent e(pid,tid,tidx);
  events.emplace_back(e);
  if(!events.empty() && curev().iid.get_pid() == events.back().pid) 
    curev().tid = events.back().tid;
  curev().may_conflict = true;

  compute_above_clock(event_idx);
  if(replay) events.back().read_from = curev().read_from;
    //compute_vclocks();
  //if(tid > 1000) tp++;
} 

int TLCCVTraceBuilder::compute_above_clock(unsigned i) {
  int last = -1;
  IPid ipid = events[i].get_pid();
  int tidx = events[i].get_index();

  if (tidx > 1) {
    last = find_process_event(ipid, tidx-1);
    events[i].clock = events[last].clock;
    events[i].above_clock = events[last].above_clock;
  } else {
    events[i].clock = VClock<IPid>();
    events[i].above_clock = VClock<IPid>();
  }
  events[i].clock[ipid] = tidx;
  events[i].above_clock[ipid] = tidx;
  
  return last;
}

void TLCCVTraceBuilder::compute_vclocks(){
  /* The first event of a thread happens after the spawn event that
   * created it.
   */
  for (int i = 0; i < event_idx; i++){
    /* First add the non-reversible edges */
    int last = compute_above_clock(i);
   
  // Then add read-from 
  if(events[i].eventType.kind ==SymEv::LOAD && events[i].read_from != -1) {
        events[i].clock += events[events[i].read_from].clock;
        events[i].above_clock += events[events[i].read_from].above_clock;
      }// [po U rf ]* 

  if(!events[i].modification_order.empty()){
    for(unsigned j = 0; j < events[i].modification_order.size() ; ++j){
        if (events[i].modification_order[j] != -1) {
          events[i].clock += events[events[i].modification_order[j]].clock;
        }
      }
    }
  } // [po U rf U co]* 

}


bool TLCCVTraceBuilder::has_store_on_var(const void *ptr, unsigned i) const {
  const RWEvent &e = events[i];
  if(e.global_variables.count(ptr)){
    return true;
  }
  return false;
}


int TLCCVTraceBuilder:: performWrite(void *ptr, llvm::GenericValue val , int typ){
  if(!typ)
    return -1;
  curev().may_conflict = true;

  IPid pid = curev().iid.get_pid();
  RWEvent &e = events[event_idx];
  if(!events.empty() && curev().iid.get_pid() == e.get_pid()){
    if(e.global_variables.count(ptr)){
      e.global_variables[ptr] = val;
    }
    else{
      e.global_variables.insert({ptr,val});
    }
    if(!replay)createSchedule(e.tid);
    return event_idx;
  }
  else
    return -1;
}

void TLCCVTraceBuilder::record_replay(int eindex , int teindex){

    std::vector<SEvent> &events_before = prefix[eindex].new_schedules->events_before;
    for(int i = 0; i < eindex ; i++){ // Add read_from for this read event in replay  
      const Event &e = prefix[i];
      int pid = e.iid.get_pid();
      int index = e.iid.get_index();
      IID<IPid> iid(pid, index);
      events_before.emplace_back(iid);
      events_before.back().size = e.size;
      events_before.back().sym = e.sym;
      events_before.back().pinned = e.pinned;
      events_before.back().read_from = e.read_from;
      
      events_before.back().new_schedules = e.new_schedules;
      events_before.back().swappable = e.swappable;
      //events_before.back().tid = e.tid;
      events_before.back().depth = e.depth;

    }

}

int TLCCVTraceBuilder::performRead(void *ptr , int typ) {
  if(!typ)
    return -1;
  if(!events.empty() && curev().iid.get_pid() == events[event_idx].get_pid()) 
    curev().tid = events[event_idx].tid;
  curev().may_conflict = true;

  compute_vclocks();

  //Replay. Add current_reads part
  if(replay){
    int tid = curev().tid;
    int read_from = curev().read_from;


    if(read_from!= -1) {
      //Add co edge to event[reads_from] form event we \in [po U rf] 
      std::set<int> &hb_before = curev().happens_before;
      std::vector<int> writes;
      std::vector<int> readable_vec;
      std::vector<int> visible_vec;
      hb_before.clear();
      for (int j = 0; j < event_idx; ++j) {
        if (has_store_on_var(ptr,j)){
          writes.emplace_back(j);
          if(happens_before(events[j],events[event_idx].above_clock)) {
            hb_before.insert(j);
          }
        }
      }

      std::set<int> latest_hb_writes;
      for(auto j : hb_before){
        int readable = true;
        for( auto k : hb_before){
          if(j!= k && happens_before(events[j] , events[k].clock)){
            readable = false;
          }
        }
        if(readable){
          latest_hb_writes.insert(j);
        }
      }

      events[event_idx].hb_writes[ptr] = latest_hb_writes;////

      //std::vector<std::pair<const void *, int>> &cur_reads = events[event_idx].vec_current_reads;
      for(auto j: writes){
        bool readable = true;;
        for(auto k: hb_before){
          if( j!= k && happens_before(events[j],events[k].clock)) {
            readable = false;
            break;
          }
        }
        if(readable){
          readable_vec.emplace_back(j);
          //curev().possible_reads.insert({j,false});
        } 
      }

      //rf edge
      events[event_idx].clock += events[read_from].clock;
      events[event_idx].above_clock += events[read_from].above_clock;

      //co edges
      for(auto we : readable_vec){
        if(hb_before.count(we)){
          visible_vec.emplace_back(we);
        }
      }
      for(auto j : visible_vec) {
          if( j!= read_from){
            events[read_from].modification_order.push_back(j);
            events[read_from].clock += events[j].clock; // co edge
          }
      }
    }
    curev().var = ptr;
    events[event_idx].readVar = ptr;
    return read_from;
  }

  // Not Replay

  int tid = curev().tid;
  RWEvent &cur_event = events[event_idx];
  
  //*** Return -1, if no event has a write on this variable, i.e read from init
  {
    bool flag = false;
    for(int i = 0; i < event_idx ; i++ ){
      if(events[i].global_variables.count(ptr))
        flag = true;
    }
    if(!flag){
      curev().read_from = -1;
      cur_event.read_from = -1;
      curev().var = ptr;
      events[event_idx].readVar = ptr;
      curev().depth = prefix_idx;
      std::shared_ptr<Schedule> pt(new Schedule(prefix_idx));
      curev().new_schedules = pt;
      record_replays_for_events.emplace_back(std::make_pair(prefix_idx,event_idx)); // Record the replay events if scheduled by a postponed write
      add_to_queue();
      return -1;
    }
  }

  //compute_vclocks(); // computes [po U rf]* and [po U rf U co]*

  std::vector<int> writes;
  std::set<int> &hb_before = curev().happens_before;
  hb_before.clear();
  for (int j = 0; j < event_idx ; ++j) {
    if (has_store_on_var(ptr,j)){
      writes.push_back(j);
      if(happens_before(events[j],cur_event.above_clock)) {
        hb_before.insert(j);
      }
    }
  }


  // Check if, it can read from init and .
  if(hb_before.empty() && curev().iid.get_pid() !=0 /*not main*/){
    curev().can_read_from.emplace_back(-1);
  }

  std::set<int> latest_hb_writes;
  for(auto j : hb_before){
    int readable = true;
    for( auto k : hb_before){
      if(j!= k && happens_before(events[j] , events[k].clock)){
        readable = false;
      }
    }
    if(readable){
      latest_hb_writes.insert(j);
    }
  }
  events[event_idx].hb_writes[ptr] = latest_hb_writes;//// store readable writes 
    for(auto j: writes){
      bool readable = true;;
      for(auto k: hb_before){
        if( j!= k && happens_before(events[j],events[k].clock)) {
          readable = false;
          break;
        }
      }
      if(readable){
        curev().can_read_from.emplace_back(j);
        //curev().possible_reads.insert({j,false});
      } 
    }
  

  if(!curev().can_read_from.empty()) {

    std::vector<int> &readable_vec = curev().can_read_from;
    std::vector<int> visible_vec;
    for(auto we : readable_vec){
      if(hb_before.count(we)){
        visible_vec.emplace_back(we);
      }
    }
    int reads_from = curev().can_read_from.back();
    curev().can_read_from.pop_back();
    
    //Add rf edge
    if(reads_from != -1) {
      events[event_idx].clock += events[reads_from].clock; // make rf visible in vector clocks
      events[event_idx].above_clock += events[reads_from].above_clock;
    }

    //Add co edge to event[reads_from] form we \in [po U rf] 
    if( reads_from != -1){        //Ensures that it is not init
      for(auto we : visible_vec){
        if(we != reads_from){
            events[reads_from].modification_order.emplace_back(we);
            events[reads_from].clock += events[we].clock; // make co edge visible in vector clock
        }
      }
    }

    curev().read_from = reads_from;
    cur_event.read_from = reads_from;
    tasks_created = tasks_created + curev().can_read_from.size();
    temp = temp + curev().can_read_from.size();

    curev().var = ptr;
    events[event_idx].readVar = ptr;
    curev().depth = prefix_idx;

    std::shared_ptr<Schedule> pt(new Schedule(prefix_idx));
    curev().new_schedules = pt;

    // Record replay and add event to queue
    record_replays_for_events.emplace_back(std::make_pair(prefix_idx,event_idx));
    add_to_queue();
    return reads_from;
  }  
  return -1;
}

void TLCCVTraceBuilder::add_to_queue(){
  const Event &e = prefix[prefix_idx];// this event
  int pid = e.iid.get_pid();
  int idx = e.iid.get_index();
  IID<IPid> iid(pid,idx);
  std::shared_ptr<SEvent> sevent(new SEvent(iid));
  sevent->size = e.size;
  sevent->sym = e.sym;
  sevent->pinned = e.pinned;
  sevent->read_from = e.read_from;
  if(!e.can_read_from.empty())
    sevent->new_read_from = e.can_read_from;
    //sevent->new_read_from.insert( sevent->new_read_from.begin() , e.can_read_from.begin() , e.can_read_from.end());
  sevent->new_schedules = e.new_schedules;
  sevent->swappable = e.swappable;
  //sevent->tid = e.tid;
  sevent->depth = prefix_idx; //this event depth
  
  //sevent->new_schedules->new_read_from = e.can_read_from;
  //Add event to queue
  ccvschedules.scheduler.push(sevent);
  current_schedules.insert({sevent->depth , sevent}); //Added to umap for fast look up
}

void TLCCVTraceBuilder::createSchedule(int tid){
  IPid pid = curev().iid.get_pid();
  RWEvent &e = events[event_idx];

  if(!e.global_variables.empty()){
    for(auto ptr : e.global_variables) {
      for(int i = event_idx-1 ; i >= 0 ; i--){
        
          if(events[i].eventType.kind == SymEv::LOAD && events[i].readVar == ptr.first && 
                !happens_before(events[i],e.above_clock) && prefix[events[i].prefix_index].swappable == true) {
            bool possible = true;
            //*** re[i] [hb] e[j] AND e[j] [hb] this ew....This violates ccv - as cycle is formed
            if(possible){
              for(int j= i+1 ; j < event_idx ; j++){
                if(happens_before(events[i] , events[j].above_clock) 
                        && happens_before(events[j],e.above_clock))
                  possible = false;
                  break;
              }
            }
            if(possible){
              std::unordered_map<int,int> tids; // old and new ewtid
              std::unordered_set<int> pids;
              std::vector<SEvent> rwevents_schedule;
              std::vector<SEvent> events_schedule;

              int cur_tid = events[i].tid-1;
               //*** Create schedule starting from write event etid.
              for( int j = i+1 ; j <= event_idx; j++){
                if(happens_before(events[j],e.above_clock)){
                  SEvent rwe(events[j].get_pid(), ++cur_tid , events[j].get_index());
                  tids.insert({events[j].get_tid(),cur_tid});
                  if(!pids.count(events[j].get_pid()))
                    pids.insert(events[j].get_pid());
                  rwevents_schedule.emplace_back(rwe);
                  rwevents_schedule.back().clock = events[j].clock;
                  rwevents_schedule.back().above_clock = events[j].above_clock;
                }
              }
              //Check the happened before events using tids
              int j = prefix_idx;
              for( ; ; j--){
                if(prefix[j].tid == events[i].get_tid()){
                  break;
                }
                else if(tids.count(prefix[j].tid)) {
                  //////////////////////////////////////////
                  {
                    const Event &e = prefix[j];
                    int pid = e.iid.get_pid();
                    int index = e.iid.get_index();
                    IID<IPid> iid(pid, index);
                    SEvent sevent(iid);
                    /*if(tids.count(e.tid))
                      sevent.tid = tids[e.tid];
                    else
                      sevent.tid = e.tid;*/

                    sevent.sym = e.sym;
                    //SymEv &sym = sevent.sym;
                    
                    int e_read_from = e.read_from;
                    if(is_load(j) && e_read_from != -1 && tids.count(events[e_read_from].get_tid()))
                      sevent.read_from = tids[events[e_read_from].get_tid()] - 1; // tid - 1 is index in events vector
                    else
                      sevent.read_from = e_read_from;

                    //if(e.read_from > 100) tp = events[i].tid - 1;
                    sevent.swappable = false;
                    sevent.size = e.size;
                    sevent.pinned = e.pinned;
                    sevent.depth = e.depth;

                    events_schedule.insert(events_schedule.begin() , sevent);
                  }
                }
              }
              {
                
                  //Add this schedule if equivalent schedule does not exist
                  if(!is_equivalent(prefix[j].new_schedules->scheduled_rwevents , rwevents_schedule)) {
                    prefix[j].new_schedules->scheduled_rwevents.insert(prefix[j].new_schedules->scheduled_rwevents.begin() , rwevents_schedule);
                    prefix[j].new_schedules->scheduled_events.insert(prefix[j].new_schedules->scheduled_events.begin() , events_schedule);
                    //temp = prefix[j].new_schedules->scheduled_events.size();
                    tasks_created = tasks_created + 1; // new task crerated
                    temp = temp + 1;
                  }
                
              }

            }
          }
        
      } 
    }
  }
}

bool TLCCVTraceBuilder::is_equivalent(std::vector<std::vector<SEvent>> &schedules , std::vector<SEvent> this_schedule) {
  if(schedules.empty())
    return false;
  bool res = false;
  for(int i=0 ; i < schedules.size() ; i++){
    std::vector<SEvent> &schedule = schedules[i];
    int count = 0;
      for( int j = 0 ; j < this_schedule.size() ; j++){
        bool found = false;
        for(int k = 0 ; k < schedule.size() ; k++){
          if(this_schedule[j].above_clock == schedule[k].above_clock){
            found = true;
            count++;
            break;
          }
        }
        if(!found){
          break;
        }
      }
    if(count == this_schedule.size()) {
      res = true;
      break;
    }
  }
  return res;
}

uint64_t TLCCVTraceBuilder::tracecount(){
  uint64_t t = 0;
  int64_t value = 0;
  t = temp;
  //t = tp;
  return t;
}