use builtin::*;
use builtin_macros::*;
use std::collections::*;
use vstd::{map::*, modes::*, prelude::*, seq::*, seq_lib::*, *};
use vstd::{set::*, set_lib::*};
// use std::collections::Vector;
// use crate::protocol::RSL::configuration::*;
// use crate::protocol::RSL::constants::*;
// use crate::protocol::RSL::broadcast::*;
// use crate::protocol::RSL::environment::*;
use crate::common::framework::environment_s::*;
use crate::common::native::io_s::*;
use crate::implementation::common::marshalling::*;
use crate::implementation::RSL::appinterface::*;

use crate::protocol::RSL::types::*;
use crate::services::RSL::app_state_machine::*;
verus! {
    pub type COperationNumber = u64;

    // pub fn clone_coperationnumber_up_to_view(opn: &COperationNumber) -> (res: COperationNumber)
    // ensures res@ == opn@
    // {
    //     *opn
    // }

    pub open spec fn AbstractifyCOperationNumberToOperationNumber(s:COperationNumber) -> int
        recommends
            COperationNumberIsAbstractable(s)
    {
        s as int
    }

    pub open spec fn COperationNumberIsAbstractable(s:COperationNumber) -> bool {
        true
    }

    pub open spec fn COperationNumberIsValid(s:COperationNumber) -> bool {
        COperationNumberIsAbstractable(s)
    }

    define_struct_and_derive_marshalable!{
        #[derive(Clone, Copy, PartialEq)]
        pub struct CBallot {
            pub seqno : u64,
            pub proposer_id : u64,
        }
    }

    pub fn CBalLt(ba:&CBallot, bb:&CBallot) -> (r:bool)
        requires
            ba.valid(),
            bb.valid(),
        ensures r == BalLt(ba@, bb@)
    {
        ba.seqno < bb.seqno
        || (ba.seqno == bb.seqno && ba.proposer_id < bb.proposer_id)
    }

    pub fn CBalLeq(ba:&CBallot, bb:&CBallot) -> (r:bool)
        requires
            ba.valid(),
            bb.valid(),
        ensures r == BalLeq(ba@, bb@)
    {
        ba.seqno < bb.seqno
        || (ba.seqno == bb.seqno && ba.proposer_id <= bb.proposer_id)
    }

    impl CBallot {

        pub fn clone_up_to_view(&self) -> (res: CBallot)
        ensures res@ == self@
        {
            CBallot {
                seqno: self.seqno,
                proposer_id: self.proposer_id,
            }
        }

        pub open spec fn abstractable(self) -> bool
        {
            self.proposer_id < 0xFFFF_FFFF_FFFF_FFFF
        }

        pub open spec fn valid(self) -> bool
        {
            self.abstractable()
        }

        pub open spec fn view(self) -> Ballot
            recommends self.abstractable()
        {
            Ballot{seqno:self.seqno as int, proposer_id:self.proposer_id as int}
        }
    }

    define_struct_and_derive_marshalable!{
        #[derive(Clone, PartialEq)]
        pub struct CRequest {
            pub client : EndPoint,
            pub seqno : u64,
            pub request : CAppMessage,
        }
    }

    impl View for CRequest {
        type V = Request;
        open spec fn view(&self) -> Request
        {
            Request{
                client : self.client@,
                seqno : self.seqno as int,
                request : self.request@,
            }
        }
    }

    impl CRequest {

    pub fn clone_up_to_view(&self) -> (res: CRequest)
        ensures res@ == self@
        {
            CRequest {
                client: self.client.clone_up_to_view(),
                seqno: self.seqno,
                request: self.request.clone_up_to_view()
            }
        }

        pub open spec fn abstractable(self) -> bool {
            &&& self.client.abstractable()
            &&& self.request.abstractable()
        }

        pub open spec fn valid(self) -> bool {
            &&& self.abstractable()
            // &&&
            &&& self.request.valid()
        }

        // pub open spec fn view(self) -> Request
        //     recommends self.abstractable()
        // {
        //     Request{
        //         client : self.client@,
        //         seqno : self.seqno as int,
        //         request : self.request@,
        //     }
        // }
    }

    define_struct_and_derive_marshalable!{
        #[derive(Clone)]
        pub struct CReply {
            pub client : EndPoint,
            pub seqno : u64,
            pub reply : CAppMessage,
        }
    }

    impl CReply {

        pub fn clone_up_to_view(&self) -> (res: CReply)
        ensures res@ == self@
    {
        CReply {
            client: self.client.clone_up_to_view(),
            seqno: self.seqno,
            reply: self.reply.clone_up_to_view(),
            }
        }

        pub open spec fn abstractable(self) -> bool {
            &&& self.client.abstractable()
            &&& self.reply.abstractable()
        }

        pub open spec fn valid(self) -> bool {
            &&& self.abstractable()
            // &&&
            &&& self.reply.valid()
        }

        pub open spec fn view(self) -> Reply
            recommends self.abstractable()
        {
            Reply{
                client : self.client@,
                seqno : self.seqno as int,
                reply : self.reply@,
            }
        }
    }

    pub type CRequestBatch = Vec<CRequest>;

    #[verifier(external_body)]
    pub fn clone_request_batch_up_to_view(batch: &CRequestBatch) -> (res: CRequestBatch)
    ensures
        res@ == batch@,
        forall |i: int| 0 <= i < batch.len() ==> res[i]@ == batch[i]@
{
    let mut cloned:Vec<CRequest> = Vec::new();
    let mut i = 0;
    while i < batch.len()
        invariant
            cloned.len() == i,
            forall |j: int| 0 <= j < i ==> cloned[j]@ == batch[j]@
    {
        assert (forall |i: int| 0 <= i < cloned.len() ==> cloned[i]@ == batch[i]@);
        cloned.push(batch[i].clone_up_to_view());
        i += 1;
    }
    cloned
}


    pub open spec fn crequestbatch_is_abstractable(s:CRequestBatch) -> bool {
        forall |i:int| #![auto] 0 <= i < s.len() ==> s[i].abstractable()
    }

    pub open spec fn crequestbatch_is_valid(s:CRequestBatch) -> bool {
        &&& crequestbatch_is_abstractable(s)
        &&& (forall |i:int| #![auto] 0 <= i < s.len() ==> s[i].valid())
    }

    pub open spec fn abstractify_crequestbatch(s:CRequestBatch) -> RequestBatch
        recommends crequestbatch_is_abstractable(s)
    {
        s@.map(|i, r:CRequest| r@)
    }

    // pub open spec fn view(self) -> RequestBatch
    // recommends crequestbatch_is_abstractable(s)
    // {
    //     s@.map(|i, r:CRequest| r@)
    // }

    pub open spec fn RequestBatchSizeLimit() -> int { 1000 }

    pub type CReplyCache = HashMap<EndPoint, CReply>;

    #[verifier(external_body)]
    pub fn clone_creply_cache_up_to_view(cache: &CReplyCache) -> (res: CReplyCache)
        ensures
            res@ == cache@,
            forall |k| cache@.contains_key(k) ==> res@.contains_key(k),
            forall |k| res@.contains_key(k) ==> cache@.contains_key(k),
            forall |k| res@.contains_key(k) ==> res@[k] == cache@[k]
    {
        let mut cloned:HashMap<EndPoint, CReply> = HashMap::new();

        // Manually collect keys to avoid iterator issues
        let mut keys: Vec<EndPoint> = Vec::new();
        let mut i = 0;

    for k in cache.keys() {
        keys.push(k.clone_up_to_view());
    }

    let mut j = 0;
    while j < keys.len()
        invariant
            0 <= j <= keys.len(),
            forall |k: int| 0 <= k < j ==> cloned.contains_key(&keys[k]) && cloned@[keys[k]] == cache@[keys[k]]
    {
        let key = keys[j].clone_up_to_view();
        let val = cache.get(&key).unwrap();
        cloned.insert(key, val.clone_up_to_view());
        j += 1;
    }

        cloned
    }


    pub open spec fn creplycache_is_abstractable(m:CReplyCache) -> bool {
        forall |i| #![auto] m@.contains_key(i) ==> i.abstractable() && m@[i].abstractable()
    }

    pub open spec fn creplycache_is_valid(m:CReplyCache) -> bool {
        &&& creplycache_is_abstractable(m)
        &&& (forall |i| #![auto] m@.contains_key(i) ==> m@[i].valid())
    }

    pub open spec fn abstractify_creplycache(m:CReplyCache) -> ReplyCache
        recommends creplycache_is_abstractable(m)
    {
        Map::new(
            |ak: AbstractEndPoint| exists |k:EndPoint| m@.contains_key(k) && k@ == ak, // m@.contains_key(k) k@,
            |ak: AbstractEndPoint| {
                let k = choose |k: EndPoint| m@.contains_key(k) && k@ == ak;
                m@[k]@
            }
        )
    }

    define_struct_and_derive_marshalable!{
        #[derive(Clone)]
        pub struct CVote {
            pub max_value_bal : CBallot,
            pub max_val : CRequestBatch,
        }
    }

    impl CVote{

        pub fn clone_up_to_view(&self) -> (res: CVote)
        ensures res@ == self@
        {
            CVote {
                max_value_bal: self.max_value_bal.clone_up_to_view(),
                max_val: clone_request_batch_up_to_view(&self.max_val),
            }
        }

        pub open spec fn abstractable(self) -> bool{
            &&& self.max_value_bal.abstractable()
            &&& crequestbatch_is_abstractable(self.max_val)
        }

        pub open spec fn valid(self) -> bool{
            &&& self.abstractable()
            &&& self.max_value_bal.valid()
            &&& crequestbatch_is_valid(self.max_val)
        }

        pub open spec fn view(self) -> Vote
            recommends self.abstractable()
        {
            Vote{
                max_value_bal : self.max_value_bal@,
                max_val : abstractify_crequestbatch(self.max_val),
            }
        }
    }

    pub type CVotes = HashMap<COperationNumber, CVote>;

    #[verifier(external_body)]
    pub fn clone_cvotes_up_to_view(votes: &CVotes) -> (res: CVotes)
    ensures
        res@ == votes@,
        forall |k| votes@.contains_key(k) ==> res@.contains_key(k),
        forall |k| res@.contains_key(k) ==> votes@.contains_key(k),
        forall |k| res@.contains_key(k) ==> res@.index(k) == votes@.index(k)
{
    let mut cloned:HashMap<COperationNumber, CVote> = HashMap::new();

    // Avoid borrow issues by collecting keys separately
    let mut keys: Vec<COperationNumber> = Vec::new();
    for &k in votes.keys() {
        keys.push(k);
    }

    let mut i = 0;
    while i < keys.len()
        invariant
            i <= keys.len(),
            forall |j: int| 0 <= j < i ==> {
                let k = keys[j];
                cloned.contains_key(&k) && cloned@.index(k) == votes@.index(k)
            }
    {
        let k = keys[i];
        let v = votes.get(&k).unwrap();
        cloned.insert(k, v.clone_up_to_view());
        i += 1;
    }
    cloned
}


    pub open spec fn cvotes_is_abstractable(m:CVotes) -> bool {
        forall |i| #![auto] m@.contains_key(i) ==> COperationNumberIsAbstractable(i) && m@[i].abstractable()
    }

    pub open spec fn cvotes_is_valid(m:CVotes) -> bool {
        &&& cvotes_is_abstractable(m)
        &&& (forall |i| #![auto] m@.contains_key(i) ==> COperationNumberIsValid(i) && m@[i].valid())
    }

    pub open spec fn abstractify_cvotes(m:CVotes) -> Votes
        recommends cvotes_is_abstractable(m)
    {
        Map::new(
            |ak: int| exists |k: u64| m@.contains_key(k) && k@ == ak,
            |ak: int| {
                let k = choose |k: u64| m@.contains_key(k) && k@ == ak;
                m@[k]@
            }
        )
    }

    pub open spec fn max_votes_len() -> int{1001}

    #[derive(Clone)]
    pub struct CLearnerTuple {
        pub received_2b_message_senders:HashSet<EndPoint>,
        pub candidate_learned_value:CRequestBatch,
    }


    impl CLearnerTuple{
        pub open spec fn abstractable(self) -> bool{
            &&& (forall |p| self.received_2b_message_senders@.contains(p) ==> p.abstractable())
            &&& crequestbatch_is_abstractable(self.candidate_learned_value)
        }

        pub open spec fn valid(self) -> bool{
            &&& self.abstractable()
            // &&& (forall |p| self.received_2b_message_senders@.contains(p) ==> p.valid())
            &&& crequestbatch_is_valid(self.candidate_learned_value)
        }

        pub open spec fn view(self) -> LearnerTuple
        {
            LearnerTuple{
                received_2b_message_senders:self.received_2b_message_senders@.map(|i:EndPoint| i@),
                candidate_learned_value:abstractify_crequestbatch(self.candidate_learned_value),
            }
        }
    }

    pub type CLearnerState = HashMap<COperationNumber, CLearnerTuple>;

    pub open spec fn clearnerstate_is_abstractable(m:CLearnerState) -> bool {
        forall |i| #![auto] m@.contains_key(i) ==> COperationNumberIsAbstractable(i) && m@[i].abstractable()
    }

    pub open spec fn clearnerstate_is_valid(m:CLearnerState) -> bool {
        &&& clearnerstate_is_abstractable(m)
        &&& (forall |i| #![auto] m@.contains_key(i) ==> COperationNumberIsValid(i) && m@[i].valid())
    }

    pub open spec fn abstractify_clearnerstate(m:CLearnerState) -> LearnerState
        recommends clearnerstate_is_abstractable(m)
    {
        Map::new(
            |ak: int| exists |k: u64| m@.contains_key(k) && k@ == ak,
            |ak: int| {
                let k = choose |k: u64| m@.contains_key(k) && k@ == ak;
                m@[k]@
            }
        )
    }

}
