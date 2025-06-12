use crate::protocol::common::upper_bound::*;
use crate::protocol::RSL::broadcast::*;
use crate::protocol::RSL::configuration::*;
use crate::protocol::RSL::constants::*;
use crate::protocol::RSL::environment::*;
use crate::protocol::RSL::message::*;
use crate::protocol::RSL::types::*;
use builtin::*;
use builtin_macros::*;
use vstd::{map::*, modes::*, prelude::*, seq::*, seq_lib::*, *};
use vstd::{set::*, set_lib::*};

verus! {
    pub struct ElectionState {
        pub constants:LReplicaConstants,
        pub current_view:Ballot,
        pub current_view_suspectors:Set<int>,
        pub epoch_end_time:int,
        pub epoch_length:int,
        pub requests_received_this_epoch:Seq<Request>,
        pub requests_received_prev_epochs:Seq<Request>,
    }

    pub open spec fn ComputeSuccessorView(b:Ballot, c:LConstants) -> Ballot
    {
        if b.proposer_id + 1 < c.config.replica_ids.len() {
            Ballot {
                seqno: b.seqno,
                proposer_id: b.proposer_id + 1
            }
        }else{
            Ballot {
                seqno: b.seqno,
                proposer_id: 0
            }
        }
    }

    pub open spec fn BoundRequestSequence(s:Seq<Request>, lengthBound:UpperBound) -> Seq<Request>
    {
        if lengthBound is UpperBoundFinite && 0 <= lengthBound->n < s.len() {
            s.subrange(0, lengthBound->n)
        } else {
            s
        }
    }

    pub open spec fn RequestsMatch(r1:Request, r2:Request) -> bool
    {
        r1 is Request && r2 is Request && r1.client == r2.client && r1.seqno == r2.seqno
    }

    pub open spec fn RequestSatisfiedBy(r1:Request, r2:Request) -> bool
    {
        r1 is Request && r2 is Request && r1.client == r2.client && r1.seqno <= r2.seqno
    }

    pub open spec fn RemoveAllSatisfiedRequestsInSequence(s:Seq<Request>, r:Request) -> Seq<Request>
        decreases s.len()
    {
        if s.len() == 0 {
            seq![]
        }else if RequestSatisfiedBy(s[0], r){
            RemoveAllSatisfiedRequestsInSequence(s.subrange(1, s.len() as int), r)
        }else{
            seq![s.index(0)].add(RemoveAllSatisfiedRequestsInSequence(s.subrange(1, s.len() as int), r))
        }
    }

    pub open spec fn ElectionStateInit(
        es:ElectionState,
        c:LReplicaConstants
    ) -> bool
        recommends 
            c.all.config.replica_ids.len() > 0 
    {
        es.constants == c
        && es.current_view == Ballot {
            seqno: 1,
            proposer_id: 0
        }
        && es.current_view_suspectors.is_empty()
        && es.epoch_end_time == 0
        && es.epoch_length == c.all.params.baseline_view_timeout_period
        && es.requests_received_this_epoch.len() == 0
        && es.requests_received_prev_epochs.len() == 0
    }

    pub open spec fn ElectionStateProcessHeartbeat(
        es:ElectionState,
        es_:ElectionState,
        p:RslPacket,
        clock:int
    ) -> bool
        recommends 
            p.msg is RslMessageHeartbeat
    {
        if !es.constants.all.config.replica_ids.contains(p.src) {
            es_ == es
        } else {
            let sender_index = GetReplicaIndex(p.src, es.constants.all.config);
            if p.msg->bal_heartbeat == es.current_view && p.msg->suspicious {
                es_ == ElectionState {
                    current_view_suspectors: es.current_view_suspectors.insert(sender_index),
                    ..es
                }
            } else if BalLt(es.current_view, p.msg->bal_heartbeat){
                let new_epoch_length = UpperBoundedAddition(es.epoch_length, es.epoch_length, es.constants.all.params.max_integer_val);
                es_ == ElectionState {
                        current_view: p.msg->bal_heartbeat,
                        current_view_suspectors: if p.msg->suspicious {set![sender_index]} else {set![]},
                        epoch_length: new_epoch_length,
                        epoch_end_time: UpperBoundedAddition(clock, new_epoch_length, es.constants.all.params.max_integer_val),
                        requests_received_prev_epochs: BoundRequestSequence(es.requests_received_prev_epochs + es.requests_received_this_epoch, es.constants.all.params.max_integer_val),
                        requests_received_this_epoch: seq![],
                        ..es
                    }
            }
            else {
                es_ == es
            }
        } 
        
    }

    pub open spec fn ElectionStateCheckForViewTimeout(
        es:ElectionState,
        es_:ElectionState,
        clock:int
    ) -> bool 
    {
        if clock < es.epoch_end_time {
            es_ == es
        } else if es.requests_received_prev_epochs.len() == 0 {
            let new_epoch_length = es.constants.all.params.baseline_view_timeout_period;
            es_ == ElectionState {
                epoch_length: new_epoch_length,
                epoch_end_time: UpperBoundedAddition(clock, new_epoch_length, es.constants.all.params.max_integer_val),
                requests_received_prev_epochs: es.requests_received_this_epoch,
                requests_received_this_epoch: seq![],
                ..es
            }
        } else {
            es_ == ElectionState {
                epoch_end_time: UpperBoundedAddition(clock, es.epoch_length, es.constants.all.params.max_integer_val),
                requests_received_prev_epochs: BoundRequestSequence(es.requests_received_prev_epochs + es.requests_received_this_epoch, es.constants.all.params.max_integer_val),
                requests_received_this_epoch: seq![],
                ..es
            }
        }
    }

    pub open spec fn ElectionStateCheckForQuorumOfViewSuspicions(
        es:ElectionState,
        es_:ElectionState,
        clock:int
    ) -> bool 
    {
        if (es.current_view_suspectors.len() < LMinQuorumSize(es.constants.all.config)) || !LtUpperBound(es.current_view.seqno, es.constants.all.params.max_integer_val) {
            es_ == es
        } else {
            let new_epoch_length = UpperBoundedAddition(es.epoch_length, es.epoch_length, es.constants.all.params.max_integer_val);
            es_ ==  ElectionState {
                current_view: ComputeSuccessorView(es.current_view, es.constants.all),
                current_view_suspectors: set![],
                epoch_length: new_epoch_length,
                epoch_end_time: UpperBoundedAddition(clock, new_epoch_length, es.constants.all.params.max_integer_val),
                requests_received_prev_epochs: BoundRequestSequence(es.requests_received_prev_epochs + es.requests_received_this_epoch, es.constants.all.params.max_integer_val),
                requests_received_this_epoch: seq![],
                ..es
            }
        }
    }

    pub open spec fn ElectionStateReflectReceivedRequest(
        es:ElectionState,
        es_:ElectionState,
        req:Request
    ) -> bool 
    {
        if es.requests_received_prev_epochs.contains(req)
            || es.requests_received_this_epoch.contains(req){
                es_ == es
        } else {
            es_ == ElectionState {
                requests_received_this_epoch: BoundRequestSequence(es.requests_received_this_epoch.push(req), es.constants.all.params.max_integer_val),
                ..es
            }
        }
    }

    pub open spec fn RemoveExecutedRequestBatch(reqs:Seq<Request>, batch:RequestBatch) -> Seq<Request>
        decreases batch.len()
    {
       if batch.len() == 0 {
            reqs
       } else {
            RemoveExecutedRequestBatch(RemoveAllSatisfiedRequestsInSequence(reqs, batch.index(0)), batch.subrange(1, batch.len() as int))
       }
    }

    pub open spec fn ElectionStateReflectExecutedRequestBatch(
        es:ElectionState,
        es_:ElectionState,
        batch:RequestBatch
    ) -> bool 
    {
        es_ == ElectionState {
            requests_received_prev_epochs: RemoveExecutedRequestBatch(es.requests_received_prev_epochs, batch),
            requests_received_this_epoch: RemoveExecutedRequestBatch(es.requests_received_this_epoch, batch),
            ..es
        }
    }
}