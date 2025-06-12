use crate::common::collections::helper::contains_vec;
use crate::common::collections::helper::get_cloned;

use crate::common::collections::seq_is_unique_v::*;
use crate::common::collections::sets::*;
use crate::common::collections::vecs::*;
use crate::implementation::common::{generic_refinement::*, upper_bound::*, upper_bound_i::*};
use crate::implementation::RSL::{cconfiguration::*, cconstants::*, cmessage::*, types_i::*};
use crate::protocol::common::upper_bound::*;
use crate::protocol::RSL::{
    configuration::*, constants::*, election::*, environment::*, message::*, types::*,
};
use crate::common::native::io_s::EndPoint;

use builtin::*;
use builtin_macros::*;
use std::collections::hash_set::Iter;
use std::collections::HashSet;
use std::collections::*;
use std::result;

use vstd::hash_set::HashSetWithView;
use vstd::invariant;
use vstd::std_specs::hash::*;
use vstd::{hash_map::*, map::*, prelude::*, seq::*, set::*};

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


#[verifier(external_body)]
pub fn get_cloned_replica_constants(r: &CReplicaConstants) -> (res: CReplicaConstants)
    requires
        r.valid()
    ensures
        res@ == r@,
        res.valid()
{
    r.clone()
}



#[verifier(external_body)]
pub fn set_insert_u64(inp: &mut HashSet<u64>, val: u64)
    ensures
        inp@.map(|t: u64| t as int) =~= old(inp)@.map(|t: u64| t as int) + set![val as int]
{
    inp.insert(val);
}

#[verifier(external_body)]
pub fn is_present_crequest(vec: &Vec<CRequest>, val: &CRequest) -> (res: bool)
    ensures
        res == vec@.map(|i, t:CRequest| t@).contains(val@) &&
        forall|i: int| 0<= i < vec.len() ==> vec[i].valid()
{
    vec.contains(val)
}

#[verifier(external_body)]
pub fn get_len_set(ss: &HashSet<u64>) -> (ret: usize)
    ensures(ss@.map(|t: u64| t as int).len() == ret)
{
    let mut res = 0;
    for key in ss.iter() {
        res += 1
    }
    res
}

#[verifier(external_body)]
pub fn get_bound_request_sequence(s: &Vec<CRequest>, lengthBound: u64) -> (res: Vec<CRequest>)
    ensures 
        res@.map(|i, t: CRequest| t@) == BoundRequestSequence(s@.map(|i, t: CRequest| t@), UpperBound::UpperBoundFinite { n: (lengthBound as int) }),
        forall |i: int| 0 <= i < res.len() ==> res[i].valid()
{
    if lengthBound < s.len() as u64 && lengthBound >= 0 {
        truncate_vec(s, 0, lengthBound as usize)
    } else {
        s.clone()
    }
}

#[verifier(external_body)]
pub fn get_cloned_requests(vec: &Vec<CRequest>) -> (res: Vec<CRequest>)
    ensures
        forall |i: int| 0 <= i < res.len() ==> res[i].valid(),
        res@.map(|i, t:CRequest| t@)==vec@.map(|i, t: CRequest| t@)
{
    vec.clone()
}

#[verifier(external_body)]
pub fn insert_into_set(s: &mut HashSet<u64>, val: u64)
    ensures
        s@.map(|t:u64| t as int)==old(s)@.map(|t: u64| t as int).insert(val as int)
{
    s.insert(val);
}

#[verifier(external_body)]
pub fn get_cloned_replicas(vec: &Vec<EndPoint>) -> (res: Vec<EndPoint>)
    ensures
        res@==vec@
{
    vec.clone()
}

#[verifier(external_body)]
pub fn clone_hashset_u64(s: &HashSet<u64>) -> (res: HashSet<u64>)
ensures
    res == s,
    res@ == s@
{
    let mut cloned = HashSet::new();
    for &val in s {
        cloned.insert(val);
    }
    cloned
}

#[verifier(external_body)]
pub fn clone_vec_crequest(v: &Vec<CRequest>) -> (res: Vec<CRequest>)
    requires
        forall |i: int| 0 <= i < v.len() ==> v[i].valid()
    ensures
        res==v,
        res@ == v@,
        res.len() == v.len(),
        forall |i: int| 0 <= i < res.len() ==> res[i].valid(),
        forall |i: int| 0 <= i < res.len() ==> res@[i] == v@[i]
{
    let mut result:Vec<CRequest> = Vec::new();
    let mut i = 0;
    while i < v.len()
        invariant
            0 <= i <= v.len(),
            result.len() == i,
            forall |j: int| 0 <= j < i ==> result[j].valid(),
            result@ == v@.subrange(0, i as int),
            forall |j: int| 0 <= j < i ==> result@[j] == v@[j]
    {
        let item = v[i].clone_up_to_view();
        result.push(item);
        i += 1;
        assert(result@ == v@.subrange(0, i as int));
    }

    result
}


impl CElectionState{
    #[verifier(external_body)]
    pub fn clone_up_to_view(&self) -> (result:Self)
        ensures
            self==result,
            self@ == result@,
    {
        CElectionState {
            constants: self.constants.clone_up_to_view(),
            current_view: self.current_view.clone_up_to_view(),
            current_view_suspectors: clone_hashset_u64(&self.current_view_suspectors),
            epoch_end_time: self.epoch_end_time,
            epoch_length: self.epoch_length,
            requests_received_this_epoch: clone_request_batch_up_to_view(&self.requests_received_this_epoch),
            requests_received_prev_epochs: clone_request_batch_up_to_view(&self.requests_received_prev_epochs),
        }
    }

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

    pub fn CComputeSuccessorView(b:&CBallot, c:&CConstants) -> (rc:CBallot)
        requires
            b.valid(),
            c.valid(),
            b.seqno < 0xFFFF_FFFF_FFFF_FFFF
        ensures
            rc.valid(),
            rc@ == ComputeSuccessorView(b@, c@),
    {
        let mut ret = CBallot {
            seqno: 0,
            proposer_id: 0
        };
        assert(ret.valid());
        if b.proposer_id + 1 < c.config.replica_ids.len() as u64 {
            ret = CBallot{seqno:b.seqno, proposer_id:b.proposer_id+1};
            assert(ret.valid());
        } else {
            ret = CBallot{seqno:b.seqno, proposer_id:0};
            assert(ret.valid());
        }
        ret
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
        if s.len() == 0 {
            let res = vec![];
            assert(res@.map(|i, t: CRequest| t@) == RemoveAllSatisfiedRequestsInSequence(s@.map(|i, req: CRequest| req@), r@));
            res
        }else if Self::CRequestSatisfiedBy(get_cloned(&s[0]), get_cloned(r)){
            let sub_s: Vec<CRequest> = truncate_vec(s, 1, s.len());
            Self::CRemoveAllSatisfiedRequestsInSequence(&sub_s, r)
        }else{
            let sub_s: Vec<CRequest> = truncate_vec(s, 1, s.len());
            let mut res = vec![get_cloned(&s[0])];
            assert(res@.map(|i, t: CRequest| t@) == seq![s[0]@]);
            let mut tail = Self::CRemoveAllSatisfiedRequestsInSequence(&sub_s, r);
            res.append(&mut tail);
            assert(res@.map(|i, t: CRequest| t@) == RemoveAllSatisfiedRequestsInSequence(s@.map(|i, req: CRequest| req@), r@));
            res
        }
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
        let ret = CElectionState{
            constants: get_cloned_replica_constants(&c),
            current_view_suspectors: HashSet::<u64>::new(),
            current_view: CBallot{
                seqno: 1,
                proposer_id: 0
            },
            epoch_end_time: 0,
            epoch_length: get_cloned_replica_constants(&c).all.params.baseline_view_timeout_period,
            requests_received_prev_epochs: vec![],
            requests_received_this_epoch: vec![]
        };
        proof {
            assert(ret.valid());
            assert(ret@.constants == c@);
            assert(ret@.current_view == Ballot {
                seqno: 1,
                proposer_id: 0
            });
            assert(ret@.current_view_suspectors == Set::<int>::empty());
            assert(ret@.current_view_suspectors.is_empty());
            assert(ret@.epoch_end_time == 0);
            assert(ret@.epoch_length == c@.all.params.baseline_view_timeout_period);
            assert(ret@.requests_received_this_epoch.len() == 0);
            assert(ret@.requests_received_prev_epochs.len() == 0);
        }
        ret
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
        let replica_ids = get_cloned_replicas(&self.constants.all.config.replica_ids);
        if contains_vec(&replica_ids, &p.src) {
            let (found, sender_index) = self.constants.all.config.CGetReplicaIndex(&p.src);
            assert(sender_index as int == GetReplicaIndex(p@.src, self@.constants.all.config));
            match p.msg {
                CMessage::CMessageHeartbeat { bal_heartbeat, suspicious, opn_ckpt } => {
                    if CBalEq(&bal_heartbeat, &self.current_view) && suspicious {
                        assert(bal_heartbeat@ == self@.current_view);
                        insert_into_set(&mut self.current_view_suspectors, sender_index as u64);
                        proof {
                            assert(self.valid());
                            assert(self@.current_view_suspectors == old(self)@.current_view_suspectors.insert(sender_index as int));
                            assert(self@.constants == old(self)@.constants);
                            assert(self@.current_view == old(self)@.current_view);
                            assert(self@.epoch_end_time == old(self)@.epoch_end_time);
                            assert(self@.epoch_length == old(self)@.epoch_length);
                            assert(self@.requests_received_this_epoch == old(self)@.requests_received_this_epoch);
                            assert(self@.requests_received_prev_epochs == old(self)@.requests_received_prev_epochs);
                   
                        }
                    }else if CBalLt(&self.current_view, &bal_heartbeat){
                        let new_epoch_length = CUpperBoundedAddition(self.epoch_length, self.epoch_length, self.constants.all.params.max_integer_val);
                        self.current_view = bal_heartbeat;
                        if suspicious {
                            let mut ss = HashSet::<u64>::new();
                            assert(ss@.map(|t: u64| t as int) == Set::<int>::empty());
                            insert_into_set(&mut ss, sender_index as u64);
                            self.current_view_suspectors = ss;
                            assert(self@.current_view_suspectors.len() == 1);
                            assert(self@.current_view_suspectors.contains(sender_index as int));
                        } else{
                            let mut ss = HashSet::<u64>::new();
                            assert(ss@.map(|t: u64| t as int) == Set::<int>::empty());
                            self.current_view_suspectors = ss;
                            assert(self@.current_view_suspectors.is_empty());
                        }
                        self.epoch_length = new_epoch_length;
                        self.epoch_end_time = CUpperBoundedAddition(clock, new_epoch_length, self.constants.all.params.max_integer_val);
                        let total_epochs = concat_vecs(&self.requests_received_prev_epochs, &self.requests_received_this_epoch);
                        assert(total_epochs.len() < 0x1_0000_0000_0000_0000);
                        self.requests_received_prev_epochs = Self::CBoundRequestSequence(total_epochs,self.constants.all.params.max_integer_val);
                        self.requests_received_this_epoch = vec![];
                        proof {
                            assert(self@.epoch_end_time==UpperBoundedAddition(clock as int, self@.epoch_length, self@.constants.all.params.max_integer_val));
                            assert(self@.requests_received_prev_epochs==BoundRequestSequence(
                                    old(self)@.requests_received_prev_epochs + old(self)@.requests_received_this_epoch,
                                    self@.constants.all.params.max_integer_val
                                ));
                            assert(self@.requests_received_this_epoch == Seq::<Request>::empty());
                        }
                        
                    }
                },
                _ => {
                    assert(false);
                }
            }
        }
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
        let new_epoch_length = self.constants.all.params.baseline_view_timeout_period;

        if clock < self.epoch_end_time {

        } else if self.requests_received_prev_epochs.len() == 0 {
            self.epoch_length = new_epoch_length;
            self.epoch_end_time = CUpperBoundedAddition(clock, new_epoch_length, self.constants.all.params.max_integer_val);
            self.requests_received_prev_epochs = get_cloned_requests(&self.requests_received_this_epoch); 
            self.requests_received_this_epoch = vec![];
            proof {
                assert(self.valid());
                assert(self@.epoch_length == new_epoch_length as int);
                assert(self@.epoch_end_time == UpperBoundedAddition(clock as int, new_epoch_length as int, self@.constants.all.params.max_integer_val));
                assert(self@.requests_received_prev_epochs == old(self)@.requests_received_this_epoch);
                assert(self@.requests_received_this_epoch == Seq::<Request>::empty());
            }
           
        } else {
            let total_epochs = concat_vecs(&self.requests_received_prev_epochs, &self.requests_received_this_epoch);
            assert(total_epochs@.map(|_i,t:CRequest| t@) == self@.requests_received_prev_epochs + self@.requests_received_this_epoch); // Use es (old state)
            assert(total_epochs.len() < 0x1_0000_0000_0000_0000);
            
            self.epoch_end_time = CUpperBoundedAddition(clock, self.epoch_length, self.constants.all.params.max_integer_val);
            self.requests_received_prev_epochs = get_bound_request_sequence(&total_epochs, self.constants.all.params.max_integer_val);
            self.requests_received_this_epoch = vec![];
            proof {
                assert(self.valid());
                assert(self@.epoch_end_time == UpperBoundedAddition(clock as int, self.epoch_length as int, self@.constants.all.params.max_integer_val));
                assert(self@.requests_received_prev_epochs == BoundRequestSequence(total_epochs@.map(|i, t: CRequest| t@), self@.constants.all.params.max_integer_val));
                assert(self@.requests_received_this_epoch == Seq::<Request>::empty());
            }
        }
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
        let cmp = self.current_view.seqno >= self.constants.all.params.max_integer_val;
        assert(self.valid());
        let sus_len = get_len_set(&self.current_view_suspectors);
        assert(sus_len as int == self@.current_view_suspectors.len());
        assert(cmp == !LtUpperBound(self@.current_view.seqno, self@.constants.all.params.max_integer_val));
        if (sus_len < CConfiguration::CMinQuorumSize(&self.constants.all.config)) || cmp
        {
            assert(self.valid());
            assert(self@ == old(self)@);
        } else {
            let new_epoch_length = CUpperBoundedAddition(self.epoch_length, self.epoch_length, self.constants.all.params.max_integer_val);
            assert(new_epoch_length@==UpperBoundedAddition(self@.epoch_length, self@.epoch_length, self@.constants.all.params.max_integer_val));
            let total_epochs = concat_vecs(&self.requests_received_prev_epochs, &self.requests_received_this_epoch);
            assert(total_epochs@.map(|_i,t:CRequest| t@) == self@.requests_received_prev_epochs + self@.requests_received_this_epoch); // Use es (old state)
            assert(total_epochs.len() < 0x1_0000_0000_0000_0000);
            let bounded = Self::CBoundRequestSequence(total_epochs, self.constants.all.params.max_integer_val);
            assert(bounded@.map(|i,t:CRequest| t@)==BoundRequestSequence(total_epochs@.map(|i,t:CRequest| t@),self@.constants.all.params.max_integer_val));
            let current_view = Self::CComputeSuccessorView(&self.current_view, &self.constants.all);
            assert(current_view@==ComputeSuccessorView((self)@.current_view, self@.constants.all));
            self.current_view = current_view;
            self.current_view_suspectors = HashSet::new();
            self.epoch_length = new_epoch_length;
            self.epoch_end_time = CUpperBoundedAddition(clock, new_epoch_length, self.constants.all.params.max_integer_val);
            self.requests_received_prev_epochs = bounded;
            self.requests_received_this_epoch = vec![];
            proof {
                assert(self.valid());
                assert(self@.current_view==ComputeSuccessorView(old(self)@.current_view, self@.constants.all));
                assert(self@.current_view_suspectors == Set::<int>::empty());
                assert(self@.epoch_length==UpperBoundedAddition(old(self)@.epoch_length, old(self)@.epoch_length, self@.constants.all.params.max_integer_val));
                assert(self@.epoch_end_time==UpperBoundedAddition(clock as int, self@.epoch_length, self@.constants.all.params.max_integer_val));
                assert(self@.requests_received_prev_epochs==BoundRequestSequence(
                        old(self)@.requests_received_prev_epochs + old(self)@.requests_received_this_epoch,
                        self@.constants.all.params.max_integer_val
                    ));
                assert(self.requests_received_this_epoch@.map(|i, t:CRequest| t@) == Seq::<Request>::empty());
                assert(ElectionStateCheckForQuorumOfViewSuspicions(old(self)@, self@, clock as int));
            }
           
        }
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
        if is_present_crequest(&self.requests_received_prev_epochs, &req) || is_present_crequest(&self.requests_received_this_epoch, &req)   
        {
            assert(self.valid());
            assert(old(self)@==self@);
        } 
        else {
            let new_req = vec![req];
            let total_epochs = concat_vecs(&self.requests_received_this_epoch, &new_req);
            assert(total_epochs.len()<0x1_0000_0000_0000_0000);
            self.requests_received_this_epoch = Self::CBoundRequestSequence(total_epochs, self.constants.all.params.max_integer_val);
            proof {
                assert(
                    self@.requests_received_this_epoch==BoundRequestSequence(
                        old(self)@.requests_received_this_epoch.push(req@),
                        self@.constants.all.params.max_integer_val
                    )); 
                assert(self@.constants==old(self)@.constants);
                assert(self@.current_view_suspectors==old(self)@.current_view_suspectors);
                assert(self@.epoch_end_time==old(self)@.epoch_end_time);
                assert(self@.epoch_length==old(self)@.epoch_length);
                assert(self@.requests_received_prev_epochs==old(self)@.requests_received_prev_epochs);
                assert(self@.current_view==old(self)@.current_view);
            }
            
        }   
    }

    // #[verifier(external_body)]
    pub fn CRemoveExecutedRequestBatch(reqs: Vec<CRequest>, batch: CRequestBatch) -> (r: Vec<CRequest>)
        requires
            (forall |i: int| 0 <= i < reqs@.len() ==> reqs@[i].valid()),
            crequestbatch_is_valid(&batch),
        ensures
            (forall |i: int| 0 <= i < r@.len() ==> r@[i].valid()),
            r@.map(|i, req:CRequest| req@) == RemoveExecutedRequestBatch(reqs@.map(|i, req:CRequest| req@), abstractify_crequestbatch(&batch)),
    {
        let mut res = vec![];
        if batch.len()==0 {
            res = reqs;
            assert(res@.map(|i, req:CRequest| req@) == RemoveExecutedRequestBatch(reqs@.map(|i, req:CRequest| req@), abstractify_crequestbatch(&batch)));
        } else {
            res = Self::CRemoveExecutedRequestBatch(Self::CRemoveAllSatisfiedRequestsInSequence(&clone_request_batch_up_to_view(&reqs), &batch[0]), truncate_vec(&batch, 1, batch.len()));
            assert(res@.map(|i, req:CRequest| req@) == RemoveExecutedRequestBatch(reqs@.map(|i, req:CRequest| req@), abstractify_crequestbatch(&batch)));
        }
        res
    }

    // #[verifier(external_body)]
    pub fn CElectionStateReflectExecutedRequestBatch(
        &mut self,
        batch:&CRequestBatch
    )
        requires
            old(self).valid(),
            crequestbatch_is_valid(&batch),
        ensures
            self.valid(),
            ElectionStateReflectExecutedRequestBatch(old(self)@, self@, abstractify_crequestbatch(&batch))
    {
        self.requests_received_prev_epochs = Self::CRemoveExecutedRequestBatch(clone_request_batch_up_to_view(&self.requests_received_prev_epochs), clone_request_batch_up_to_view(&batch));
        self.requests_received_this_epoch = Self::CRemoveExecutedRequestBatch(clone_request_batch_up_to_view(&self.requests_received_this_epoch), clone_request_batch_up_to_view(&batch));
    }
}



#[verifier(external_body)]
pub proof fn lemma_hashset_len_concrete_eq_implies_spec_eq(s1: &HashSet<u64>, s2: &HashSet<u64>)
ensures
    s1.len() as int == s2@.map(|i : u64| i as int).len(),
{}

#[verifier(external_body)]
pub proof fn lemma_requests_received_this_epoch_matches_spec(
    new_seq: Seq<Request>,
    old_seq: Seq<Request>,
    new_req: Request,
    bound: int,
)
ensures
    new_seq == BoundRequestSequence(old_seq + seq![new_req],UpperBound::UpperBoundFinite { n: bound as int }),
{}


#[verifier(external_body)]
pub proof fn lemma_seq_concat_len_bound<T>(s1: Seq<T>, s2: Seq<T>)
ensures
    (s1 + s2).len() < 0x1_0000_0000_0000_0000,
{}

} // verus!
