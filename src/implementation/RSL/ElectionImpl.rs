use crate::common::collections::seq_is_unique_v::*;
use crate::common::collections::vecs::*;
use crate::implementation::common::{generic_refinement::*, upper_bound::*, upper_bound_i::*};
use crate::implementation::RSL::{cconfiguration::*, cconstants::*, cmessage::*, types_i::*};
use crate::protocol::common::upper_bound::*;
use crate::protocol::RSL::{
    configuration::*, constants::*, election::*, environment::*, message::*, types::*,
};
use builtin::*;
use builtin_macros::*;
use std::collections::*;
use vstd::{map::*, prelude::*, seq::*, set::*};

verus! {

#[derive(Clone)]
pub struct CElectionState {
    pub constants: CReplicaConstants,
    pub current_view: CBallot,
    pub current_view_suspectors: HashSet<u64>,
    pub epoch_end_time: u64,
    pub epoch_length: u64,
    pub requests_received_this_epoch: Vec<CRequest>,
    pub requests_received_prev_epochs: Vec<CRequest>,
}

impl CElectionState{
    pub open spec fn abstractable(self) -> bool {
        &&& self.constants.abstractable()
        &&& self.current_view.abstractable()
        &&& (forall |i:int| 0 <= i < self.requests_received_this_epoch@.len() ==> self.requests_received_this_epoch@[i].abstractable())
        &&& (forall |i:int| 0 <= i < self.requests_received_prev_epochs@.len() ==> self.requests_received_prev_epochs@[i].abstractable())
    }

    pub open spec fn valid(self) -> bool {
        &&& self.abstractable()
        &&& self.constants.valid()
        &&& self.current_view.valid()
        &&& (forall |i:int| 0 <= i < self.requests_received_this_epoch@.len() ==> self.requests_received_this_epoch@[i].valid())
        &&& (forall |i:int| 0 <= i < self.requests_received_prev_epochs@.len() ==> self.requests_received_prev_epochs@[i].valid())
    }

    pub open spec fn view(self) -> ElectionState
        recommends self.abstractable()
    {
        ElectionState{
            constants: self.constants@,
            current_view: self.current_view@,
            current_view_suspectors: self.current_view_suspectors@.map(|x:u64| x as int),
            epoch_end_time: self.epoch_end_time as int,
            epoch_length: self.epoch_length as int,
            requests_received_this_epoch: self.requests_received_this_epoch@.map(|i, r:CRequest| r@),
            requests_received_prev_epochs: self.requests_received_prev_epochs@.map(|i, r:CRequest| r@)
        }
    }

    pub fn CComputeSuccessorView(b:CBallot, c:CConstants) -> (rc:CBallot)
        requires
            b.valid(),
            c.valid(),
            b.seqno < 0xFFFF_FFFF_FFFF_FFFF
        ensures
            rc.valid(),
            rc@ == ComputeSuccessorView(b@, c@),
    {
        if b.proposer_id + 1 < c.config.replica_ids.len() as u64 {
            CBallot{seqno:b.seqno, proposer_id:b.proposer_id+1}
        } else {
            CBallot{seqno:b.seqno+1, proposer_id:0}
        }
    }

    pub fn CBoundRequestSequence(s: Vec<CRequest>, lengthBound: u64) -> (rc: Vec<CRequest>)
        requires
            s@.len() < 0x1_0000_0000_0000_0000,
            forall |i: int| 0 <= i < s@.len() ==> s@[i].valid(),
        ensures
            forall |i: int| 0 <= i < rc@.len() ==> rc@[i].valid(),
            rc@.map(|i, r: CRequest| r@) == BoundRequestSequence(s@.map(|i, r: CRequest| r@), UpperBound::UpperBoundFinite{n: lengthBound as int}),
    {
        let s_len = s.len() as u64;
        assert(s_len == s@.len() as u64);
        if 0 <= lengthBound && lengthBound < s_len {
            let rc = truncate_vec(&s, 0, lengthBound as usize);
            assert(rc@.map(|i, r: CRequest| r@) == BoundRequestSequence(s@.map(|i, r: CRequest| r@), UpperBound::UpperBoundFinite{n: lengthBound as int}));
            rc
        } else {
            let rc = s;
            assert(rc@.map(|i, r: CRequest| r@) == BoundRequestSequence(s@.map(|i, r: CRequest| r@), UpperBound::UpperBoundFinite{n: lengthBound as int}));
            rc
        }
    }

    pub fn CRequestsMatch(r1:CRequest, r2:CRequest) -> (r:bool)
        requires
            r1.valid(),
            r2.valid(),
        ensures
            r == RequestsMatch(r1@, r2@)
    {
        do_end_points_match(&r1.client, &r2.client) && r1.seqno == r2.seqno
    }

    pub fn CRequestSatisfiedBy(r1:CRequest, r2:CRequest) -> (r:bool)
        requires
            r1.valid(),
            r2.valid(),
        ensures
            r == RequestSatisfiedBy(r1@, r2@)
    {
        do_end_points_match(&r1.client, &r2.client) && r1.seqno <= r2.seqno
    }

    #[verifier(external_body)]
    pub fn CRemoveAllSatisfiedRequestsInSequence(s:&Vec<CRequest>, r:&CRequest) -> (rc: Vec<CRequest>)
        where CRequest: Clone
        requires
            forall |i: int| 0 <= i < s@.len() ==> s@[i].valid(),
            r.valid(),
        ensures
            forall |i: int| 0 <= i < rc@.len() ==> rc@[i].valid(),
            rc@.map(|i, req:CRequest| req@) == RemoveAllSatisfiedRequestsInSequence(s@.map(|i, req: CRequest| req@), r@),
    {
        
    }

    // #[verifier(external_body)]
    pub fn CElectionStateInit(c:CReplicaConstants) -> (rc:Self)
        requires
            c.valid(),
            c.all.config.replica_ids.len() > 0
        ensures
            rc.valid(),
            ElectionStateInit(rc@, c@),
    {
        
    }

    // #[verifier(external_body)]
    pub fn CElectionStateProcessHeartbeat(
        &mut self,
        p:CPacket,
        clock:u64
    )
        requires
            old(self).valid(),
            p.msg is CMessageHeartbeat,
            p.valid(),
        ensures
            self.valid(),
            ElectionStateProcessHeartbeat(old(self)@, self@, p@, clock as int)
    {
        
    }


    // #[verifier(external_body)]
    pub fn CElectionStateCheckForViewTimeout(
        &mut self,
        clock:u64
    )
        requires
            old(self).valid(),
        ensures
            self.valid(),
            ElectionStateCheckForViewTimeout(old(self)@, self@, clock as int)
    {

    }

    // #[verifier(external_body)]
    pub fn CElectionStateCheckForQuorumOfViewSuspicions(
        &mut self,
        clock:u64
    )
        requires
            old(self).valid(),
        ensures
            self.valid(),
            ElectionStateCheckForQuorumOfViewSuspicions(old(self)@, self@, clock as int)
    {
        
    }


    // #[verifier(external_body)]
    pub fn CElectionStateReflectReceivedRequest(
        &mut self,
        req:CRequest
    )
        requires
            old(self).valid(),
            req.valid(),
        ensures
            self.valid(),
            ElectionStateReflectReceivedRequest(old(self)@, self@, req@)
    {
        
    }

    // #[verifier(external_body)]
    pub fn CRemoveExecutedRequestBatch(reqs: Vec<CRequest>, batch: CRequestBatch) -> (r: Vec<CRequest>)
        requires
            (forall |i: int| 0 <= i < reqs@.len() ==> reqs@[i].valid()),
            crequestbatch_is_valid(batch),
        ensures
            (forall |i: int| 0 <= i < r@.len() ==> r@[i].valid()),
            r@.map(|i, req:CRequest| req@) == RemoveExecutedRequestBatch(reqs@.map(|i, req:CRequest| req@), abstractify_crequestbatch(batch)),
    {
       
    }

    // #[verifier(external_body)]
    pub fn ElectionStateReflectExecutedRequestBatch(
        &mut self,
        batch:CRequestBatch
    )
        requires
            old(self).valid(),
            crequestbatch_is_valid(batch),
        ensures
            self.valid(),
            ElectionStateReflectExecutedRequestBatch(old(self)@, self@, abstractify_crequestbatch(batch))
    {
        
    }
}

} // verus!
