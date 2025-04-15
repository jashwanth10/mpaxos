use builtin::*;
use builtin_macros::*;
use vstd::{map::*, modes::*, prelude::*, seq::*, seq_lib::*, *};
use vstd::{set::*, set_lib::*};
use crate::protocol::RSL::configuration::*;
use crate::protocol::RSL::constants::*;
use crate::protocol::RSL::broadcast::*;
use crate::protocol::RSL::environment::*;
use crate::protocol::RSL::types::*;
use crate::protocol::RSL::message::*;
use crate::protocol::common::upper_bound::*;

verus!{
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
        
    }

    pub open spec fn RequestSatisfiedBy(r1:Request, r2:Request) -> bool
    {
       
    }

    pub open spec fn RemoveAllSatisfiedRequestsInSequence(s:Seq<Request>, r:Request) -> Seq<Request>
        decreases s.len()
    {
        
    }

    pub open spec fn ElectionStateInit(
        es:ElectionState,
        c:LReplicaConstants
    ) -> bool
        recommends 
            c.all.config.replica_ids.len() > 0 
    {
        
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
        
    }

    pub open spec fn ElectionStateCheckForViewTimeout(
        es:ElectionState,
        es_:ElectionState,
        clock:int
    ) -> bool 
    {
        
    }

    pub open spec fn ElectionStateCheckForQuorumOfViewSuspicions(
        es:ElectionState,
        es_:ElectionState,
        clock:int
    ) -> bool 
    {
        
    }

    pub open spec fn ElectionStateReflectReceivedRequest(
        es:ElectionState,
        es_:ElectionState,
        req:Request
    ) -> bool 
    {
        
    }

    pub open spec fn RemoveExecutedRequestBatch(reqs:Seq<Request>, batch:RequestBatch) -> Seq<Request>
        decreases batch.len()
    {
       
    }

    pub open spec fn ElectionStateReflectExecutedRequestBatch(
        es:ElectionState,
        es_:ElectionState,
        batch:RequestBatch
    ) -> bool 
    {
        
    }
}