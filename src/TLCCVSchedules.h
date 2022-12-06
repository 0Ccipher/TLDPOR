/* Copyright (C) 2022 Omkar Tuppe
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
#ifndef __TLCCV_SCEDULES_H__
#define __TLCCV_SCEDULES_H__
#endif

#include <queue>
#include <memory>
#include "SymEv.h"
#include "vector"
#include "IID.h"
#include "VClock.h"

typedef int IPid;
typedef int Tid;

struct Schedule;
  
struct SEvent{
 public:
    SEvent(const IID<IPid> &iid, SymEv sym = {})
      : iid(iid), origin_iid(iid),sym(std::move(sym)) {}
    SEvent(IPid pid, Tid tid , int eindex)
      : pid(pid), tid(tid) , eindex(eindex) {}
    int alt;
    int size;
    bool pinned;
    
    IID<IPid> iid;
    IID<IPid> origin_iid;

    int read_from;
    
    Tid tid;
    IPid pid;
    int eindex;
    
    std::vector<int> new_read_from;

    std::shared_ptr<Schedule> new_schedules;
    
    bool localread = false;
    
    bool swappable = true;

    bool current = false;

    SymEv sym;

    int depth;

    VClock<IPid> clock, above_clock;
};

struct Schedule{
  public:
    Schedule(int depth) {
      this->depth = depth;
    }
    int depth;
    std::vector<SEvent> events_before;
    std::vector<int> new_read_from;
    std::vector<std::vector<SEvent>> scheduled_events;
    std::vector<std::vector<SEvent>> scheduled_rwevents;
    
  };

  class DepthCompare {
  public:
    bool operator()(const std::shared_ptr<SEvent> &a,
                  const std::shared_ptr<SEvent> &b) const {
      return a->depth < b->depth;
    }
  };
/*class DepthCompare {
public:
  bool operator()(const SEvent &a,
                const SEvent &b) const {
    return a.depth < b.depth;
  }
};*/

class TLCCVSchedules {
 public:
 	std::priority_queue<std::shared_ptr<SEvent>, std::vector<std::shared_ptr<SEvent>>, DepthCompare> scheduler;
  //std::priority_queue<SEvent, std::vector<SEvent>, DepthCompare> scheduler;

  SEvent create_event();
};
