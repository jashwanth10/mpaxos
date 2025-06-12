use super::types_i::COperationNumber;
use crate::common::collections::sets::*;
use builtin::*;
use builtin_macros::*;
use std::collections::HashMap;

// use std::iter::Map;
use std::hash::RandomState;
use std::result;
use vstd::std_specs::hash::*;
use vstd::{map::*, prelude::*, seq::*, set_lib::set_int_range};

use crate::common::collections::{count_matches::*, maps::*, vecs::*, helper::*};
use crate::implementation::RSL::types_i::CBalLt;

use crate::common::{collections::maps::*, native::io_s::EndPoint};
use crate::implementation::common::{generic_refinement::*, upper_bound::*, upper_bound_i::*};
use crate::implementation::RSL::{
    cbroadcast::*, cconfiguration::*, cconstants::*, cmessage::*, types_i::*,
};
use crate::protocol::RSL::{
    acceptor::*, broadcast::*, configuration::*, constants::*, environment::*, message::*, types::*,
};

verus! {

    // Datatype for CAcceptor
    #[derive(Clone)]
    pub struct CAcceptor {
        pub constants: CReplicaConstants,
        pub max_bal: CBallot,
        pub votes: CVotes,
        pub last_checkpointed_operation: Vec<COperationNumber>,
        pub log_truncation_point: COperationNumber,
    }

    #[verifier::external_body]
    fn collect_cloned(
        v: &CVotes,
    ) -> (keys:Vec<COperationNumber>)
        requires
            cvotes_is_abstractable(v)
        ensures
        ({
            let ss = abstractify_cvotes(v);
            forall |k: OperationNumber| keys@.map(|u, t: u64| t as int).contains(k) <==> ss.dom().contains(k)
        }) 
    {
        v.keys().cloned().collect()
    }

    #[verifier::external_body]
    fn get_val(
        v: &CVotes, key: &COperationNumber
    ) -> (val: CVote)
         requires 
            COperationNumberIsValid(*key),
            cvotes_is_valid(v)
         ensures cvotes_is_valid(v) && ({
            let ss = abstractify_cvotes(v);
            ss[*key as int] == val.view()
            && val.valid()
         })
    {
        v.get(key).unwrap().clone()
    }

    #[verifier(external_body)]
    pub fn insert_vote(votes: &mut CVotes, key: COperationNumber, val: CVote)
        requires
            COperationNumberIsValid(key),
            cvotes_is_valid(old(votes)),
            val.valid()
        ensures 
            cvotes_is_valid(votes) &&
            votes@.contains_key(key) &&
            votes@[key] == val
    {
        votes.insert(key, val); // body is ignored by Verus
    }

    impl CAcceptor{
        pub open spec fn abstractable(self) -> bool
        {
            &&& self.constants.abstractable()
            &&& self.max_bal.abstractable()
            &&& cvotes_is_abstractable(&self.votes)
            &&& (forall |i:int| 0 <= i < self.last_checkpointed_operation.len() ==> COperationNumberIsAbstractable(self.last_checkpointed_operation[i]))
            &&& COperationNumberIsAbstractable(self.log_truncation_point)
        }

        // Predicate to check if CAcceptor is valid
        pub open spec fn valid(self) -> bool {
            &&& self.abstractable()
            &&& self.constants.valid()
            &&& self.max_bal.valid()
            &&& cvotes_is_valid(&self.votes)
            &&& (forall |i:int| 0 <= i < self.last_checkpointed_operation.len() ==> COperationNumberIsValid(self.last_checkpointed_operation[i]))
            &&& COperationNumberIsValid(self.log_truncation_point)
            &&& self.last_checkpointed_operation.len() == self.constants.all.config.replica_ids.len()
        }

        // Function to abstractify CAcceptor to LAcceptor
        pub open spec fn view(self) -> LAcceptor
            recommends self.abstractable()
        {
            LAcceptor {
                constants: self.constants.view(),
                max_bal: self.max_bal.view(),
                votes: abstractify_cvotes(&self.votes),
                last_checkpointed_operation:self.last_checkpointed_operation@.map(|i,c:COperationNumber| AbstractifyCOperationNumberToOperationNumber(c)),
                log_truncation_point: AbstractifyCOperationNumberToOperationNumber(self.log_truncation_point),
            }
        }

        // #[verifier(external_body)]
        pub fn CCountLargerInSeq(s:&Vec<u64>, target:u64) -> (res:u64)
        ensures 
        ({
            let ss = s@.map(|i, t:u64| t as int);
            && res < 0xffff_ffff_ffff_ffff
            && res as int == CountMatchesInSeq(ss, |x:int| x > target as int)
        })
        {
            let ghost ss = s@.map(|i, t:u64| t as int);
            if s.len() == 0 {
                assert(ss.len() == 0);
                assert(CountMatchesInSeq(ss, |x:int| x > target as int) == 0);
                0
            } else {
                let rest = truncate_vecu64(s, 1, s.len());
                assert(rest@.map(|i, t:u64| t as int) == ss.subrange(1, ss.len() as int));
                let temp = Self::CCountLargerInSeq(&rest, target);
                assert(temp == CountMatchesInSeq(ss.subrange(1, ss.len() as int), |x:int| x > target as int));
                if s[0] > target {
                    assume(temp + 1 < 0xffff_ffff_ffff_ffff);
                    temp + 1
                } else 
                {
                    temp
                }
            }
        }

        fn CCountLargerOrEqualInSeq(s:&Vec<u64>, target:u64) -> (res:u64)
            ensures 
            ({
                let ss = s@.map(|i, t:u64| t as int);
                && res < 0xffff_ffff_ffff_ffff
                && res as int == CountMatchesInSeq(ss, |x:int| x >= target as int)
            })
        {
            let ghost ss = s@.map(|i, t:u64| t as int);
            if s.len() == 0 {
                assert(ss.len() == 0);
                assert(CountMatchesInSeq(ss, |x:int| x > target as int) == 0);
                0
            } else {
                let rest = truncate_vecu64(s, 1, s.len());
                let temp = Self::CCountLargerOrEqualInSeq(&rest, target);
                assert(temp == CountMatchesInSeq(ss.subrange(1, ss.len() as int), |x:int| x >= target as int)); 
                if s[0] >= target {
                    assume(temp + 1 < 0xffff_ffff_ffff_ffff);
                    temp + 1
                } else 
                {
                    temp
                }
            }
        }

        fn CIsNthHighestValueInSequence(v:u64, s:&Vec<u64>, n:u64) -> (res:bool)
            ensures
            ({
                let ss = s@.map(|i, t:u64| t as int);
                && res == IsNthHighestValueInSequence(v as int, ss, n as int)
            })
        {
            let ghost ss = s@.map(|i, t:u64| t as int);
            let len = s.len();
            let b1 = (0 < n) && (n < len as u64);
            assert(b1 == (0 < n < ss.len()));
            let b2 = contains_u64(s, &v);
            assert(b2 == ss.contains(v as int));
            let b3 = Self::CCountLargerInSeq(s, v) < n;
            assert(b3 == (CountMatchesInSeq(ss, |x:int| x > v) < n as int));
            let b4 = Self::CCountLargerOrEqualInSeq(s, v) >= n;
            assert(b4 == (CountMatchesInSeq(ss, |x:int| x >= v) >= n));
            b1 && b2 && b3 && b4
        }


        // #[verifier(external_body)]
        pub fn CIsLogTruncationPointValid(log_truncation_point: COperationNumber, last_checkpointed_operation: &Vec<COperationNumber>, config: &CConfiguration) -> (isValid :bool)
            requires
                COperationNumberIsValid(log_truncation_point),
                forall|i:int| 0<=i<=last_checkpointed_operation.len() | last_checkpointed_operation[i] as usize ==> COperationNumberIsValid(last_checkpointed_operation[i]),
                config.valid()
            ensures
                isValid == IsLogTruncationPointValid(AbstractifyCOperationNumberToOperationNumber(log_truncation_point),
                last_checkpointed_operation@.map(|i,c:COperationNumber| AbstractifyCOperationNumberToOperationNumber(c)),
                config.view())
        {
            let quorum_size = CConfiguration::CMinQuorumSize(&config) as u64;
            assert(last_checkpointed_operation@.map(|i,c:COperationNumber| AbstractifyCOperationNumberToOperationNumber(c)) == last_checkpointed_operation@.map(|i, t: u64| t as int));
            Self::CIsNthHighestValueInSequence(log_truncation_point, &last_checkpointed_operation, quorum_size)
        }

        #[verifier(external_body)]
        pub fn CRemoveVotesBeforeLogTruncationPoint(votes: CVotes, log_truncation_point: COperationNumber) -> (cvotes:CVotes)
            requires
                cvotes_is_valid(&votes),
                COperationNumberIsValid(log_truncation_point),
            ensures
            cvotes_is_valid(&cvotes) && RemoveVotesBeforeLogTruncationPoint(abstractify_cvotes(&cvotes), abstractify_cvotes(&votes), AbstractifyCOperationNumberToOperationNumber(log_truncation_point))
        {
            let mut cvotes: CVotes = CVotes::new();
            assert(cvotes_is_valid(&votes));
            assert(cvotes_is_abstractable(&cvotes));
            assert(cvotes_is_valid(&cvotes));
            let ghost pt: OperationNumber = log_truncation_point as int;

            let keys: Vec<COperationNumber> = collect_cloned(&votes);
            let mut i = 0;
            while i < keys.len()
                invariant
                    cvotes_is_valid(&votes),
                    cvotes_is_valid(&cvotes),
                    forall |j: int| 0<=j<i ==> COperationNumberIsValid(keys[j]),
                    forall |j: int| 0<=j<i ==> votes@.dom().contains(keys[j]),
                    forall |j: int| 0<=j<i && cvotes@.dom().contains(keys[j]) ==> keys[j] >= log_truncation_point

            {
                if keys[i] >= log_truncation_point {
                    let value = get_val(&votes, &keys[i]);
                    assert(COperationNumberIsValid(keys[i as int]));
                    assert(value.valid());
                    insert_vote(&mut cvotes, keys[i], value);
                    assert(votes@.contains_key(keys[i as int]));
                    assert(cvotes@.contains_key(keys[i as int]));
                    assert(cvotes_is_valid(&cvotes));
                }
                i = i + 1;
            }        

            // assert(RemoveVotesBeforeLogTruncationPoint(abstractify_cvotes(cvotes), abstractify_cvotes(votes), AbstractifyCOperationNumberToOperationNumber(log_truncation_point)));
            cvotes
        }

        #[verifier(external_body)]
        pub fn CAddVoteAndRemoveOldOnes(votes: CVotes, new_opn: COperationNumber, new_vote: CVote, log_truncation_point: COperationNumber) -> (cvotes_2:CVotes)
            requires
                cvotes_is_valid(&votes),
                COperationNumberIsValid(new_opn),
                new_vote.valid(),
                COperationNumberIsValid(log_truncation_point),
            ensures
                cvotes_is_valid(&cvotes_2) && LAddVoteAndRemoveOldOnes(abstractify_cvotes(&votes), abstractify_cvotes(&cvotes_2), AbstractifyCOperationNumberToOperationNumber(new_opn), new_vote.view(), AbstractifyCOperationNumberToOperationNumber(log_truncation_point))
        {
            let mut result: CVotes = CVotes::new();
            assert(cvotes_is_valid(&result));
            
            let keys: Vec<COperationNumber> = collect_cloned(&votes);
            let mut i = 0;

            while i < keys.len()
                invariant
                    0 <= i <= keys.len(),
                    forall |j: int| 0 <= j < i ==> {
                        let k = keys[j];
                        if k >= log_truncation_point as int {
                            result@.contains_key(k)
                            && result@[k] == votes@[k]
                        } else {
                            !result@.contains_key(k)
                        }
                    },
                    forall |k| result@.contains_key(k) ==> k >= log_truncation_point
            {
                let k = keys[i];
                if k >= log_truncation_point {
                    let v = get_val(&votes, &k);
                    result.insert(k, v);
                }
                i = i + 1;
            }

            assert(COperationNumberIsValid(new_opn));
            assert(new_vote.valid());

            result.insert(new_opn, new_vote);
            assert(cvotes_is_valid(&result));


            assert(LAddVoteAndRemoveOldOnes(abstractify_cvotes(&votes), abstractify_cvotes(&result), AbstractifyCOperationNumberToOperationNumber(new_opn), new_vote.view(), AbstractifyCOperationNumberToOperationNumber(log_truncation_point)));
            result
        }


        pub fn CAcceptorInit(c: CReplicaConstants) -> (rc:Self)
            requires c.valid()
            ensures
                rc.valid(),
                LAcceptorInit(
                    rc@, /* used to convert the implementation type to protocol type */
                    c@
                ) /* refinement condition */
        {
            let t2 = CBallot{
                seqno: 0,
                proposer_id: 0,
            };
            let t3: HashMap<COperationNumber,CVote> = HashMap::new();

            let len = c.all.config.replica_ids.len();
            let mut t4: Vec<u64> = Vec::new();
            let mut i = 0;
            while i < len
                invariant
                    i <= len,
                    t4.len() == i,
                    forall |j:int| 0 <= j < i ==> t4[j] == 0,
            {
                t4.push(0);
                i = i + 1;
            }

            assert(t4.len() == len);
            assert(forall |idx:int| 0 <= idx < t4.len() ==> t4[idx] == 0);

            let t5 = 0;

            let s = CAcceptor{constants:c, max_bal:t2, votes:t3, last_checkpointed_operation:t4, log_truncation_point:t5};

            let ghost ss = s@;
            let ghost sc = c@;

            assert(ss.constants == sc);
            assert(ss.max_bal == Ballot{seqno:0,proposer_id:0});
            assert(ss.votes == Map::<OperationNumber, Vote>::empty());
            assert(ss.last_checkpointed_operation.len() == sc.all.config.replica_ids.len());
            assert(forall |idx:int| 0 <= idx < ss.last_checkpointed_operation.len() ==> ss.last_checkpointed_operation[idx] == 0);
            assert(ss.log_truncation_point == 0);

            s
        }

         // #[verifier(external_body)]
        pub fn CReplicaConstantsValid(c: &CReplicaConstants) -> (res: bool) 
        ensures
            res == LReplicaConstantsValid(c@)
        {
            0 <= c.my_index && c.my_index < c.all.config.replica_ids.len() as u64
        }

        // #[verifier(external_body)]
        pub fn CAcceptorProcess1a(&mut self, inp: CPacket) -> (sent: OutboundPackets)
            requires
                old(self).valid(),
                inp.valid(),
                inp.msg is CMessage1a
            ensures
                self.valid(),
                sent.valid(),
                LAcceptorProcess1a(old(self)@, self@, inp@, sent@) /* this is the refinement obligation */
        {
            let replica_ids = get_cloned(&self.constants.all.config.replica_ids);
            let mut my_index: usize = self.constants.my_index as usize;
            let my_id = Self::get_endpoint(&replica_ids, my_index);
            proof {
                lemma_AbstractifyEndpoints_properties(replica_ids);
            }
            
            let mut packets_sent = OutboundPackets::PacketSequence { s: Vec::new() };
            match inp.msg {
                CMessage::CMessage1a { bal_1a } => {
                    let ballot = bal_1a;
                    assert(ballot@ == inp@.msg->bal_1a);
                    if !CBalLt(&self.max_bal, &ballot) {
                        assert(old(self)@ == self@);
                        assert(packets_sent->s@.map(|i, t:CPacket| t@) == Seq::<RslPacket>::empty());
                        return packets_sent;
                    }
        
                    if !(contains_vec(&replica_ids, &inp.src)) {
                        assert(old(self)@ == self@);
                        assert(packets_sent->s@.map(|i, t:CPacket| t@) == Seq::<RslPacket>::empty());
                        return packets_sent;
                    }

                    if !(Self::CReplicaConstantsValid(&self.constants)) {
                        assert(old(self)@ == self@);
                        assert(packets_sent->s@.map(|i, t:CPacket| t@) == Seq::<RslPacket>::empty());
                        return packets_sent;
                    }
        
                    let out_msg = CMessage::CMessage1b {
                        bal_1b: ballot,
                        log_truncation_point: self.log_truncation_point,
                        votes: get_cloned(&self.votes),
                    };
        
                    assert(out_msg.valid());
        
                    packets_sent = OutboundPackets::PacketSequence { 
                        s: vec![CPacket{
                            src: my_id,
                            dst: inp.src,
                            msg: out_msg,
                        }] 
                    };
                    self.max_bal = ballot;
                    proof {
                        assert(packets_sent.valid());
                        assert(packets_sent@ == seq![
                            RslPacket {
                                src: self@.constants.all.config.replica_ids.index(self@.constants.my_index),
                                dst: inp@.src,
                                msg: RslMessage::RslMessage1b {
                                    bal_1b: ballot@,
                                    log_truncation_point: self@.log_truncation_point,
                                    votes: self@.votes,
                                }
                            }]);
                        assert(self@.last_checkpointed_operation == old(self)@.last_checkpointed_operation);
                        assert(self@.constants == old(self)@.constants);
                        assert(self@.max_bal == ballot@);
                        assert(self@.votes == old(self)@.votes);
                        assert(self@.log_truncation_point == old(self)@.log_truncation_point);
                        assert(self.valid());
                    }
                    
                },
                _ => {
                    assert(false);
                }
            };
            packets_sent
        }



        // #[verifier(external_body)]
        pub fn CAcceptorProcess2a(&mut self, inp:CPacket) -> (sent:OutboundPackets)
            requires
                old(self).valid(),
                inp.valid(),
                inp.msg is CMessage2a,
            ensures
                self.valid(),
                LAcceptorProcess2a(old(self)@, self@, inp@, sent@)
        {
            let mut packets_sent = OutboundPackets::PacketSequence { s: Vec::new() };

            match inp.msg {
                CMessage::CMessage2a { bal_2a, opn_2a, val_2a } => {
                    let opn = get_cloned(&opn_2a);
                    let bal = bal_2a.clone_up_to_view();
                    let val = get_cloned(&val_2a);
                    assume(self.constants.all.params.max_log_length >= 1);
                    let max_log_length_minus1 = self.constants.all.params.max_log_length - 1;
                    let mut new_log_truncation_point = self.log_truncation_point;

                    if opn >= max_log_length_minus1 {
                        if opn >= new_log_truncation_point {
                            let potential_new_truncation_point = opn - max_log_length_minus1;
                            assert(0 <= potential_new_truncation_point@ <= 0xffff_ffff_ffff_ffff);
                            if potential_new_truncation_point > self.log_truncation_point {
                                new_log_truncation_point = potential_new_truncation_point;
                            }
                            else{
                                assert(new_log_truncation_point@ == self.log_truncation_point@);
                            }
                        }else{
                            assert(new_log_truncation_point@ == self.log_truncation_point@);
                        }
                    } else {
                        assert(new_log_truncation_point@ == self.log_truncation_point@);
                    }
                    let out_msg = CMessage::CMessage2b {
                        bal_2b: bal_2a.clone_up_to_view(),
                        opn_2b: get_cloned(&opn_2a),
                        val_2b: get_cloned(&val_2a)
                    };

                    let config_clone = Self::get_cloned_config(&self.constants.all.config);
                    assume(ReplicaIndexValid(self.constants.my_index, config_clone));
                    let broadcast = CBroadcast::BuildBroadcastToEveryone(config_clone, self.constants.my_index, out_msg);

                    proof {
                        assert(opn@ == inp@.msg->opn_2a);
                        assert(bal@ == inp@.msg->bal_2a);
                        assert(val_2a@.map(|i, t: CRequest| t@) == inp@.msg->val_2a);
                        assert(self.constants.all.config.valid());
                        assert(broadcast.valid());
                    }

                    match broadcast {
                        CBroadcast::CBroadcast { src, dsts, msg } => {
                            packets_sent = OutboundPackets::PacketSequence { 
                                s: CBroadcast::BuildCBroadcast(src, dsts, msg)
                            };
                            assert(LBroadcastToEveryone(self@.constants.all.config, self@.constants.my_index, out_msg@, packets_sent@));
        
                            self.max_bal = bal_2a.clone_up_to_view();
                            self.log_truncation_point = new_log_truncation_point;
        
                            let mut votes_ = get_cloned(&self.votes);
                            let new_vote = CVote {
                                max_value_bal : bal_2a.clone_up_to_view(),
                                max_val : get_cloned(&val_2a),
                            };
                            if self.log_truncation_point <= opn {
                                votes_ = Self::CAddVoteAndRemoveOldOnes(votes_, opn, new_vote, new_log_truncation_point)
                            }
                            self.votes = votes_;
        
                        },
                        _ => {
                            assert(false);
                        }
                    }
                },
                _ => {
                    assert(false);
                }
            };
            packets_sent
        }


        // #[verifier(external_body)]
        pub fn CAcceptorProcessHeartbeat(&mut self, inp: CPacket)
            requires
                old(self).valid(),
                inp.valid(),
                inp.msg is CMessageHeartbeat,
            ensures
                self.valid(),
                LAcceptorProcessHeartbeat(old(self)@, self@, inp@)
        {
            let replica_ids = get_cloned(&self.constants.all.config.replica_ids);
            let mut opns = get_cloned(&self.last_checkpointed_operation);
            if contains_vec(&replica_ids, &inp.src) {
                let (found, sender_index) = self.constants.all.config.CGetReplicaIndex(&inp.src);
                assert(sender_index as int == GetReplicaIndex(inp@.src, self@.constants.all.config));
                if found {
                    let msg = inp.msg.clone_up_to_view();
                    match msg {
                        CMessage::CMessageHeartbeat { bal_heartbeat, suspicious, opn_ckpt } => {
                            assert(opn_ckpt as int == inp@.msg->opn_ckpt);
                            let curr_opn = Self::get_log_index(&self.last_checkpointed_operation, sender_index);
                            if opn_ckpt > curr_opn {
                                Self::update_log_index(&mut opns, sender_index, opn_ckpt);
                                assert(opns@.map(|i, t:u64| t as int) == self@.last_checkpointed_operation.update(sender_index as int, opn_ckpt as int));
                                self.last_checkpointed_operation = opns;
                                proof {
                                    assert(self@.last_checkpointed_operation == opns@.map(|i, t:u64| t as int));
                                    assert(self@.constants == old(self)@.constants);
                                    assert(self@.max_bal == old(self)@.max_bal);
                                    assert(self@.votes == old(self)@.votes);
                                    assert(self@.log_truncation_point == old(self)@.log_truncation_point);
                                }
                            } else{
                                assert(self@ == old(self)@);
                            }
                        }
                        _ => {
                            assert(false);
                        }
                    }
                } else {
                    assert(self@ == old(self)@);
                }
            } else {
                assert(self@ == old(self)@);
            }
        }

        #[verifier(external_body)]
        pub fn CAcceptorTruncateLog(&mut self, opn: COperationNumber)
            requires
                old(self).valid(),
                COperationNumberIsValid(opn)
            ensures
                self.valid(),
                LAcceptorTruncateLog(old(self)@, self@, AbstractifyCOperationNumberToOperationNumber(opn))
        {
            if opn > self.log_truncation_point {
                let cloned_votes = get_cloned(&self.votes);
                let new_votes = Self::CRemoveVotesBeforeLogTruncationPoint(cloned_votes, opn);
                self.log_truncation_point = opn;
                self.votes = new_votes;
            } else {
                assert(old(self)@ == self@)
            }
        }

        #[verifier(external_body)]
        pub fn get_endpoint(vec: &Vec<EndPoint>, index: usize) -> (ep: EndPoint)
            ensures
                vec@.map(|i, t:EndPoint| t@).contains(ep@),
                vec@.map(|i, t:EndPoint| t@)[index as int] == ep@
        {
            vec[index].clone()
        }

        #[verifier(external_body)]
        pub fn update_log_index(vec: &mut Vec<COperationNumber>, index: usize, opn_cpkt: COperationNumber)
            ensures
                vec@.len() == old(vec)@.len() &&
                vec@[index as int]==opn_cpkt@ && 
                ({
                    let ss = old(vec)@.map(|i, t: COperationNumber| t as int);
                    vec@.map(|i, t: u64| t as int) == ss.update(index as int, opn_cpkt as int)
                })
        {
            vec[index] = opn_cpkt;
        }

        #[verifier(external_body)]
        pub fn get_log_index(vec: &Vec<COperationNumber>, index: usize) -> (ret: COperationNumber) 
            ensures
                vec@[index as int] == ret@
        {
            vec[index].clone()
        }

      

        #[verifier(external_body)]
        fn get_cloned_config (elem: &CConfiguration) -> (res: CConfiguration)
            ensures
                res@ == elem@,
                res.valid()
        {
            elem.clone()
        }
    }
}
