use crate::common::collections::sets::*;
use crate::common::collections::vecs::*;
use crate::common::collections::helper::*;
use crate::common::native::io_s::*;
use crate::implementation::common::generic_refinement::*;
use crate::implementation::common::upper_bound::*;
use crate::implementation::RSL::{
    cbroadcast::*, cconfiguration::*, cconstants::*, cmessage::*, types_i::*, ElectionImpl::*,
};
use crate::protocol::common::upper_bound::UpperBoundedAddition;
use crate::protocol::common::upper_bound::LtUpperBound;
use crate::protocol::common::upper_bound::UpperBound;


use crate::protocol::RSL::broadcast::*;
use crate::protocol::RSL::election::*;
use crate::protocol::RSL::environment::*;
use crate::protocol::RSL::message::*;
use crate::protocol::RSL::types::*;
use crate::protocol::RSL::{configuration::*, proposer::*};
use builtin::*;
use builtin_macros::*;
use std::collections::hash_set::Iter;
use std::collections::HashSet;
use std::collections::*;
use vstd::hash_set::HashSetWithView;
use vstd::invariant;
use vstd::std_specs::hash::*;
use vstd::{hash_map::*, map::*, prelude::*, seq::*, set::*};

verus! {

#[derive(Clone)]
pub enum CIncompleteBatchTimer{
    CIncompleteBatchTimerOn {when:u64},
    CIncompleteBatchTimerOff,
}

impl CIncompleteBatchTimer{

    pub open spec fn abstractable(self) -> bool {
        match self {
            CIncompleteBatchTimer::CIncompleteBatchTimerOn {when} => true,
            CIncompleteBatchTimer::CIncompleteBatchTimerOff => true,
        }
    }

    pub open spec fn valid(self) -> bool {
        match self {
            CIncompleteBatchTimer::CIncompleteBatchTimerOn {when} => self.abstractable(),
            CIncompleteBatchTimer::CIncompleteBatchTimerOff => self.abstractable(),
        }
    }

    pub open spec fn view(self) -> IncompleteBatchTimer
        recommends
        self.abstractable(),
    {
        match self {
            CIncompleteBatchTimer::CIncompleteBatchTimerOn {when} => IncompleteBatchTimer::IncompleteBatchTimerOn {when:when as int},
            CIncompleteBatchTimer::CIncompleteBatchTimerOff => IncompleteBatchTimer::IncompleteBatchTimerOff{},
        }
    }

}

#[derive(Clone)]

pub struct CProposer {
    pub constants: CReplicaConstants,
    pub current_state: u64,
    pub request_queue: Vec<CRequest>,
    pub max_ballot_i_sent_1a: CBallot,
    pub next_operation_number_to_propose: u64,
    pub received_1b_packets: HashSet<CPacket>,
    pub highest_seqno_requested_by_client_this_view: HashMap<EndPoint, u64>,
    pub incomplete_batch_timer: CIncompleteBatchTimer,
    pub election_state: CElectionState,
}

#[verifier(external_body)]
pub fn get_cloned_election_state(s: &CElectionState) -> (res: CElectionState)
    ensures
        s@ == res@,
        res.valid()
{
    s.clone()
}

impl CProposer{

    pub open spec fn abstractable(self) -> bool {
        &&& self.constants.abstractable()
        &&& (forall |i:int| 0 <= i < self.request_queue@.len() ==> self.request_queue@[i].abstractable())
        &&& self.max_ballot_i_sent_1a.abstractable()
        &&& (forall |p:CPacket| self.received_1b_packets@.contains(p) ==> p.abstractable())
        &&& (forall |k:EndPoint| self.highest_seqno_requested_by_client_this_view@.contains_key(k) ==> k.abstractable())
        &&& self.incomplete_batch_timer.abstractable()
        &&& self.election_state.abstractable()
    }

    pub open spec fn valid(self) -> bool {
        &&& self.abstractable()
        &&& self.constants.valid()
        &&& (forall |i:int| 0 <= i < self.request_queue@.len() ==> self.request_queue@[i].valid())
        &&& self.max_ballot_i_sent_1a.valid()
        &&& (forall |p:CPacket| self.received_1b_packets@.contains(p) ==> p.valid())
        &&& (forall |k:EndPoint| self.highest_seqno_requested_by_client_this_view@.contains_key(k) ==> k.valid_public_key())
        &&& self.incomplete_batch_timer.valid()
        &&& self.election_state.valid()
    }

    pub open spec fn view(self) -> LProposer
    recommends self.valid(),
    {
        LProposer{
            constants: self.constants.view(),
            current_state: self.current_state as int,
            request_queue: self.request_queue@.map(|i, r:CRequest| r.view()),
            max_ballot_i_sent_1a: self.max_ballot_i_sent_1a.view(),
            next_operation_number_to_propose: self.next_operation_number_to_propose as int,
            received_1b_packets: self.received_1b_packets@.map(|p:CPacket| p.view()),
            highest_seqno_requested_by_client_this_view: Map::new(
                |ak: AbstractEndPoint| exists |k:EndPoint| self.highest_seqno_requested_by_client_this_view@.contains_key(k) && k@ == ak,
                |ak: AbstractEndPoint| {
                    let k = choose |k: EndPoint| self.highest_seqno_requested_by_client_this_view@.contains_key(k) && k@ == ak;
                    self.highest_seqno_requested_by_client_this_view@[k] as int
                }
            ),
            incomplete_batch_timer: self.incomplete_batch_timer.view(),
            election_state: self.election_state.view(),
        }
    }

    #[verifier(external_body)]
    pub fn get_val_map(&mut self, k: &EndPoint) -> (res: u64)
        ensures
            self@.highest_seqno_requested_by_client_this_view[k@] == res@,
            self.valid(),
            self@ == old(self)@

    {
        self.highest_seqno_requested_by_client_this_view.get(k).unwrap().clone()
    }

    #[verifier(external_body)]
    pub fn dom_contains(&mut self, k: &EndPoint) -> (res: bool)
        ensures
            res == self@.highest_seqno_requested_by_client_this_view.contains_key(k@),
            self.valid(),
            self@ == old(self)@
    {
        self.highest_seqno_requested_by_client_this_view.contains_key(k)
    }

    #[verifier(external_body)]
    pub fn insert_kv(&mut self, k: &EndPoint, v: u64) 
        ensures
            self.valid(),
            self@.highest_seqno_requested_by_client_this_view == old(self)@.highest_seqno_requested_by_client_this_view.insert(k@, v as int),
            self@.highest_seqno_requested_by_client_this_view[k@] == v@,
            self@.request_queue == old(self)@.request_queue,
            self@.election_state == old(self)@.election_state
    {
        self.highest_seqno_requested_by_client_this_view.insert(k.clone(), v);
    }

    #[verifier(external_body)]
    pub fn CIsAfterLogTruncationPoint(opn:COperationNumber, S:&HashSet<CPacket>) -> (res:bool)
    ensures
        ({
            let lr = LIsAfterLogTruncationPoint(opn as int, S@.map(|p:CPacket| p@));
            res == lr
        })
    {
        true
    }

    #[verifier(external_body)]
    pub fn CSetOfMessage1b(S : &HashSet<CPacket>) -> (res:bool)
        ensures
            ({
                let lr = LSetOfMessage1b(S@.map(|p:CPacket| p@));
                res == lr
            })
    {
        true
    }

    #[verifier(external_body)]
    pub fn CSetOfMessage1bAboutBallot(S:&HashSet<CPacket>, b:&CBallot) -> (res:bool)
        ensures
            res == LSetOfMessage1bAboutBallot(S@.map(|p:CPacket| p@), b@)
    {
        true
    }

    #[verifier(external_body)]
    pub fn CAllAcceptorsHadNoProposal(S:HashSet<CPacket>, opn:COperationNumber) -> (result_CAllAcceptorsHadNoProposal:bool)
    requires
        forall |p:CPacket| S@.contains(p) ==> p.valid(),
        COperationNumberIsValid(opn),
        // ({
        //     forall |p:CPacket| S@.contains(p) ==> p.msg is CMessage1b
        // })
    ensures
        ({
            let lr = LAllAcceptorsHadNoProposal(S@.map(|p:CPacket| p.view()), AbstractifyCOperationNumberToOperationNumber(opn));
            result_CAllAcceptorsHadNoProposal == lr
        })
    {
        true
    }

    #[verifier(external_body)]
    pub fn CExistVotesHasProposalLargeThanOpn(p: CPacket, op: COperationNumber) -> (result_CExistVotesHasProposalLargeThanOpn:bool)
    requires
        p.valid(),
        COperationNumberIsValid(op),
        p.msg is CMessage1b
    ensures
    ({
        let lr = LExistVotesHasProposalLargeThanOpn(p.view(), AbstractifyCOperationNumberToOperationNumber(op));
        result_CExistVotesHasProposalLargeThanOpn == lr
    })
    {
        true
    }

    #[verifier(external_body)]
    pub fn CExistsAcceptorHasProposalLargeThanOpn(S:HashSet<CPacket>, op:COperationNumber) -> (result_CExistsAcceptorHasProposalLargeThanOpn:bool)
    requires
        forall |p:CPacket| S@.contains(p) ==> p.valid(),
        COperationNumberIsValid(op),
        // ({
        //     forall |p:CPacket| S@.contains(p) ==> p.msg is CMessage1b
        // })
    ensures
    ({
        let lr = LExistsAcceptorHasProposalLargeThanOpn(S@.map(|p:CPacket| p.view()), AbstractifyCOperationNumberToOperationNumber(op));
        result_CExistsAcceptorHasProposalLargeThanOpn == lr
    })

    {
        true
    }

    #[verifier(external_body)]
    pub fn Cmax_balInS(c:CBallot, S:HashSet<CPacket>, opn:COperationNumber) -> (result_Cmax_balInS:bool)
    requires
        c.valid(),
        forall |p:CPacket| S@.contains(p) ==> p.valid(),
        COperationNumberIsValid(opn),
        // ({
        //     forall |p:CPacket| S@.contains(p) ==> p.msg is CMessage1b
        // })
    ensures
    ({
        let lr = Lmax_balInS(c.view(),S@.map(|p:CPacket| p.view()), AbstractifyCOperationNumberToOperationNumber(opn));
        result_Cmax_balInS == lr
    })
    {
        true
    }

    #[verifier(external_body)]
    pub fn CExistsBallotInS(v: CRequestBatch, c: CBallot, S: HashSet<CPacket>, opn:COperationNumber) -> (result_CExistsBallotInS:bool)
    requires
        crequestbatch_is_valid(&v),
        c.valid(),
        forall |p:CPacket| S@.contains(p) ==> p.valid(),
        COperationNumberIsValid(opn),
        // ({
        //     forall |p:CPacket| S@.contains(p) ==> p.msg is CMessage1b
        // })
    ensures
    ({
        let lr = LExistsBallotInS(abstractify_crequestbatch(&v), c.view(), S@.map(|p:CPacket| p.view()), AbstractifyCOperationNumberToOperationNumber(opn));
        result_CExistsBallotInS == lr
    })
    {
        true
    }

    #[verifier(external_body)]
    pub fn CValIsHighestNumberedProposalAtBallot(v:CRequestBatch, c:CBallot, S:HashSet<CPacket>, opn:COperationNumber) -> (result_CValIsHighestNumberedProposalAtBallot:bool)
    requires
        crequestbatch_is_valid(&v),
        c.valid(),
        forall |p:CPacket| S@.contains(p) ==> p.valid(),
        COperationNumberIsValid(opn),
        // ({
        //     forall |p:CPacket| S@.contains(p) ==> p.msg is CMessage1b
        // })
    ensures
    ({
        let lr = LValIsHighestNumberedProposalAtBallot(abstractify_crequestbatch(&v), c.view(), S@.map(|p:CPacket| p.view()), AbstractifyCOperationNumberToOperationNumber(opn));
        result_CValIsHighestNumberedProposalAtBallot == lr
    })
    {
        true
    }


    #[verifier(external_body)]
    pub fn CValIsHighestNumberedProposal(v: CRequestBatch, S: HashSet<CPacket>, opn:COperationNumber ) -> (result_CValIsHighestNumberedProposal:bool)
    requires
        crequestbatch_is_valid(&v),
        forall |p:CPacket| S@.contains(p) ==> p.valid(),
        COperationNumberIsValid(opn),
        // ({
        //     forall |p:CPacket| S@.contains(p) ==> p.msg is CMessage1b
        // })
    ensures
    ({
        let lr = LValIsHighestNumberedProposal(abstractify_crequestbatch(&v), S@.map(|p:CPacket| p.view()), AbstractifyCOperationNumberToOperationNumber(opn));
        result_CValIsHighestNumberedProposal == lr
    })
    {
        true
    }

    // #[verifier(external_body)]
    pub fn CProposerCanNominateUsingOperationNumber(&self, log_truncation_point: COperationNumber, opn:COperationNumber) -> (result_CProposerCanNominateUsingOperationNumber:bool)
    requires
        self.valid(),
        COperationNumberIsValid(log_truncation_point),
        COperationNumberIsValid(opn),
    ensures
        ({
            let lr = LProposerCanNominateUsingOperationNumber(self.view(), AbstractifyCOperationNumberToOperationNumber(log_truncation_point), AbstractifyCOperationNumberToOperationNumber(opn));
            result_CProposerCanNominateUsingOperationNumber == lr
        })
    {
        let received_packets_1 = get_cloned_packets(&self.received_1b_packets);
        let received_packets_2 = get_cloned_packets(&self.received_1b_packets);

        let res1 = CUpperBoundedAddition(log_truncation_point, self.constants.all.params.max_log_length, self.constants.all.params.max_integer_val);
        let res2 = Self::CSetOfMessage1bAboutBallot(&received_packets_1, &self.max_ballot_i_sent_1a);
        let res3 = Self::CIsAfterLogTruncationPoint(opn, &received_packets_2);
        let res4 = CConfiguration::CMinQuorumSize(&self.constants.all.config);
        let res5 = CLtUpperBound(opn, self.constants.all.params.max_integer_val);
        proof{
            assert(res1 as int == UpperBoundedAddition(log_truncation_point as int, self@.constants.all.params.max_log_length, self@.constants.all.params.max_integer_val));
            assert(res2 == LSetOfMessage1bAboutBallot(self@.received_1b_packets, self@.max_ballot_i_sent_1a));
            assert(res3 == LIsAfterLogTruncationPoint(opn as int, self@.received_1b_packets));
            assert(res5 == LtUpperBound(opn as int, self@.constants.all.params.max_integer_val));
            assert(res4 == LMinQuorumSize(self@.constants.all.config));
        }
      
        let l1 = get_set_len(&self.received_1b_packets);
        
        CBalEq(&self.election_state.current_view, &self.max_ballot_i_sent_1a)
        && self.current_state == 2
        && l1 >= res4
        && res2
        && res3
        && opn < res1
        && opn >= 0
        && res5
    }

    // #[verifier(external_body)]
    pub fn CProposerInit(c : CReplicaConstants)->(result_CProposerInit:CProposer)
    requires
        c.valid(),
    ensures
        result_CProposerInit.valid(),
        LProposerInit(result_CProposerInit@, c@)
    {
        let res = CProposer {
            constants: get_cloned_replica_constants(&c),
            current_state: 0,
            request_queue: Vec::<CRequest>::new(),
            max_ballot_i_sent_1a: CBallot {
                proposer_id: 0,
                seqno: c.my_index
            },
            next_operation_number_to_propose: 0,
            received_1b_packets: HashSet::<CPacket>::new(),
            highest_seqno_requested_by_client_this_view: HashMap::<EndPoint, u64>::new(),
            election_state: CElectionState::CElectionStateInit(c),
            incomplete_batch_timer: CIncompleteBatchTimer::CIncompleteBatchTimerOff {  },
        };
        proof {
            assert(res@.constants == c@);
            assert(res@.max_ballot_i_sent_1a == Ballot{
                proposer_id: 0,
                seqno: c@.my_index
            });
            assert(res@.received_1b_packets == Set::<RslPacket>::empty());
            assert(res@.highest_seqno_requested_by_client_this_view == Map::<AbstractEndPoint, int>::empty());
            assert(ElectionStateInit(res@.election_state, c@));
            assert(res@.incomplete_batch_timer is IncompleteBatchTimerOff);
        }
        res
    }

    // #[verifier(external_body)]
    pub fn CProposerProcessRequest(&mut self, packet:CPacket)
    requires
        old(self).valid(),
        packet.valid(),
        packet.msg is CMessageRequest
    ensures
        self.valid(),
        LProposerProcessRequest(old(self)@, self@, packet@)
    {
        let cloned_end_point = get_cloned(&packet.src);
        match packet.msg {
            CMessage::CMessageRequest { seqno_req, val } => {
                let req = CRequest {
                    client: get_cloned(&packet.src),
                    seqno: seqno_req,
                    request: val
                };
                proof {
                    assert(req@.client == cloned_end_point@);
                    assert(req@.seqno == seqno_req@);
                    assert(req@.request == val@);
                }
              
                let old_election_state = get_cloned_election_state(&self.election_state);

                CElectionState::CElectionStateReflectReceivedRequest(&mut self.election_state, get_cloned(&req));
                assert(ElectionStateReflectReceivedRequest(old(self)@.election_state, self@.election_state, req@));
                if self.current_state != 0 && (Self::dom_contains(self, &cloned_end_point)
                    || seqno_req > Self::get_val_map(self, &cloned_end_point)) {
                    
                    self.request_queue.push(req);
                    Self::insert_kv(self, &cloned_end_point, seqno_req);
                    proof {
                        assert(req@ == Request{
                            client: packet@.src,
                            seqno: packet@.msg->seqno_req,
                            request: packet@.msg->val
                        });
                        assert(self@.request_queue == old(self)@.request_queue.push(req@));
                        assert(req@.seqno == seqno_req@);
                        assert(req@.client == cloned_end_point@);
                        assert(self@.highest_seqno_requested_by_client_this_view == old(self)@.highest_seqno_requested_by_client_this_view.insert(req@.client, req@.seqno));

                    }
                } else {
                    // assume(false);
                }
            },
            _ => {
                assert(false);
            }
        }
    }

    // #[verifier(external_body)]
    pub fn CProposerMaybeEnterNewViewAndSend1a(&mut self) -> (result_CProposerMaybeEnterNewViewAndSend1a:OutboundPackets)
    requires
        old(self).valid(),
    ensures
        self.valid(),
        result_CProposerMaybeEnterNewViewAndSend1a.valid(),
        LProposerMaybeEnterNewViewAndSend1a(old(self)@, self@, result_CProposerMaybeEnterNewViewAndSend1a@)
    {
        let mut packets_sent = OutboundPackets::PacketSequence { s: Vec::new() };

        if self.election_state.current_view.proposer_id == self.constants.my_index
            && CBalLt(&self.max_ballot_i_sent_1a, &self.election_state.current_view) {
                
                self.current_state = 1;
                self.max_ballot_i_sent_1a = self.election_state.current_view;
                self.highest_seqno_requested_by_client_this_view = HashMap::new();
                self.request_queue = concat_vecs(&self.election_state.requests_received_prev_epochs, &self.election_state.requests_received_this_epoch);

                let out_msg = CMessage::CMessage1a { 
                    bal_1a: self.election_state.current_view.clone_up_to_view(),
                };
        
                let config_clone = get_cloned_config(&self.constants.all.config);
                assume(ReplicaIndexValid(self.constants.my_index, config_clone));
                let broadcast = CBroadcast::BuildBroadcastToEveryone(config_clone, self.constants.my_index, out_msg);

                proof {
                    assert(self@.max_ballot_i_sent_1a == old(self)@.election_state.current_view);
                    assert(self@.highest_seqno_requested_by_client_this_view == Map::<AbstractEndPoint, int>::empty());
                    assert(self@.request_queue == old(self)@.election_state.requests_received_prev_epochs + old(self)@.election_state.requests_received_this_epoch);
                    assert(broadcast.valid());
                }
                
                match broadcast {
                    CBroadcast::CBroadcast { src, dsts, msg } => {
                        assert(msg.valid());
                        packets_sent = OutboundPackets::PacketSequence { 
                            s: CBroadcast::BuildCBroadcast(src, dsts, msg)
                        };
                        assert(LBroadcastToEveryone(old(self)@.constants.all.config, old(self)@.constants.my_index, out_msg@, packets_sent@));
                    },
                    _ => {
                        assert(false);
                    }
                }
        } else {
            assert(self@ == old(self)@);
            assert(packets_sent@.len() as int == 0);
        }
        packets_sent 
    }

    // #[verifier(external_body)]
    pub fn CProposerNominateNewValueAndSend2a(&mut self, clock: u64, log_truncation_point: COperationNumber) -> (result_CProposerNominateNewValueAndSend2a:OutboundPackets)
    requires
        old(self).valid(),
        COperationNumberIsValid(log_truncation_point),
        // Self::CProposerCanNominateUsingOperationNumber(old(self), log_truncation_point, old(self).next_operation_number_to_propose),
        // Self::CAllAcceptorsHadNoProposal(old(self).received_1b_packets, old(self).next_operation_number_to_propose),
    ensures
        self.valid(),
        result_CProposerNominateNewValueAndSend2a.valid(),
        LProposerNominateNewValueAndSend2a(old(self)@, self@, clock as int, AbstractifyCOperationNumberToOperationNumber(log_truncation_point), result_CProposerNominateNewValueAndSend2a@)
    {
        let mut packets_sent = OutboundPackets::PacketSequence { s: Vec::new() };

        let batch_size = if self.request_queue.len() as u64 <= self.constants.all.params.max_batch_size || self.constants.all.params.max_batch_size < 0 {
            assert(self@.request_queue.len() <= self@.constants.all.params.max_batch_size || self@.constants.all.params.max_batch_size < 0 );
            self.request_queue.len() as u64
        } else {
            self.constants.all.params.max_batch_size
        };
        
        let old_request_queue = get_cloned_requests(&self.request_queue);
        let truncated_queue_first = truncate_vec(&self.request_queue, 0, batch_size as usize);
        let truncated_queue_second = truncate_vec(&self.request_queue, batch_size as usize, self.request_queue.len());
        let cloned_first = get_cloned_requests(&truncated_queue_second);
        
        self.request_queue = cloned_first;
        
        let opn = self.next_operation_number_to_propose;
        
        assume(self.next_operation_number_to_propose < 0xFFFF_FFFF_FFFF_FFFF);
        let next_opn = self.next_operation_number_to_propose + 1;
        self.next_operation_number_to_propose = next_opn;
        
        self.incomplete_batch_timer = if old_request_queue.len() > batch_size as usize {
            CIncompleteBatchTimer::CIncompleteBatchTimerOn { when: CUpperBoundedAddition(clock, self.constants.all.params.max_batch_delay, self.constants.all.params.max_integer_val) }
        } else {
            CIncompleteBatchTimer::CIncompleteBatchTimerOff {}
        };


        let out_msg = CMessage::CMessage2a { 
            bal_2a: self.max_ballot_i_sent_1a.clone_up_to_view(),
            opn_2a: get_cloned(&opn),
            val_2a: get_cloned_requests(&truncated_queue_first)
        };

        let config_clone = get_cloned_config(&self.constants.all.config);
        assume(ReplicaIndexValid(self.constants.my_index, config_clone));
        let broadcast = CBroadcast::BuildBroadcastToEveryone(config_clone, self.constants.my_index, out_msg);
        
        match broadcast {
            CBroadcast::CBroadcast { src, dsts, msg } => {
                assert(msg.valid());
                packets_sent = OutboundPackets::PacketSequence { 
                    s: CBroadcast::BuildCBroadcast(src, dsts, msg)
                };
                assert(LBroadcastToEveryone(old(self)@.constants.all.config, old(self)@.constants.my_index, out_msg@, packets_sent@));
            },
            _ => {
                assert(false);
            }
        }
       
        proof {
            assert(self@.request_queue == old(self)@.request_queue.subrange(batch_size as int, old(self)@.request_queue.len() as int));
            assert(self.incomplete_batch_timer.valid());
            assert(broadcast.valid());
            assert(self.valid());
            assert(packets_sent.valid());
        }
        packets_sent
    }

    #[verifier(external_body)]
    pub fn CProposerNominateOldValueAndSend2a(&mut self, log_truncation_point:COperationNumber) -> (sent_packets:OutboundPackets)
        requires
            old(self).valid(),
            COperationNumberIsValid(log_truncation_point),
            LProposerCanNominateUsingOperationNumber(
                old(self)@,
                log_truncation_point as int,
                old(self).next_operation_number_to_propose as int,
            ),
            !LAllAcceptorsHadNoProposal(
                old(self)@.received_1b_packets,
                old(self).next_operation_number_to_propose as int,
            )
        ensures
            self.valid(),
            sent_packets.valid(),
            LProposerNominateOldValueAndSend2a(old(self)@, self@, log_truncation_point as int, sent_packets@),
    {
        let sent = OutboundPackets::PacketSequence { s: (Vec::<CPacket>::new()) };
        sent
    }

    #[verifier(external_body)]
    pub fn CProposerMaybeNominateValueAndSend2a(&mut self, clock:u64, log_truncation_point:COperationNumber) -> (sent_packets:OutboundPackets)
        requires
            old(self).valid(),
            COperationNumberIsValid(log_truncation_point),
        ensures
            self.valid(),
            sent_packets.valid(),
            LProposerMaybeNominateValueAndSend2a(old(self)@, self@, clock as int, log_truncation_point as int, sent_packets@),
    {
        let sent = OutboundPackets::PacketSequence { s: (Vec::<CPacket>::new()) };
        sent
    }

    // #[verifier(external_body)]
    pub fn CProposerProcessHeartbeat(&mut self, p:CPacket, clock:u64)
    requires
        old(self).valid(),
        p.valid(),
        p.msg is CMessageHeartbeat,
    ensures
        self.valid(),
        LProposerProcessHeartbeat(old(self)@, self@, p@, clock as int)
    {
        let mut old_state = get_CElection_clone(&self.election_state);
        CElectionState::CElectionStateProcessHeartbeat(&mut self.election_state, p, clock);
        if CBalLt(&old_state.current_view, &self.election_state.current_view) {
            self.current_state = 0;
            self.request_queue = vec![];
            assert(self@.current_state == 0);
            assert(self@.request_queue.len() == 0);
        } else {
            assert(self@.current_state == old(self)@.current_state);
            assert(self@.request_queue == old(self)@.request_queue);
        }
    }

    // #[verifier(external_body)]
    pub fn CProposerCheckForViewTimeout(& mut self, clock:u64)
    requires
        old(self).valid(),
    ensures
        self.valid(),
        LProposerCheckForViewTimeout(old(self)@, self@, clock as int)

    {
        CElectionState::CElectionStateCheckForViewTimeout(&mut self.election_state, clock);
    }

    // #[verifier(external_body)]
    pub fn CProposerCheckForQuorumOfViewSuspicions(&mut self, clock:u64)
    requires
        old(self).valid(),
    ensures
        self.valid(),
        LProposerCheckForQuorumOfViewSuspicions(old(self)@, self@, clock as int)
    {
        let mut old_state = get_CElection_clone(&self.election_state);
        CElectionState::CElectionStateCheckForQuorumOfViewSuspicions(&mut self.election_state, clock);
        if CBalLt(&old_state.current_view, &self.election_state.current_view) {
            self.current_state = 0;
            self.request_queue = vec![];
            assert(self@.current_state == 0);
            assert(self@.request_queue.len() == 0);
        } else {
            assert(self@.current_state == old(self)@.current_state);
            assert(self@.request_queue == old(self)@.request_queue);
        }
    }

    // #[verifier(external_body)]
    pub fn CProposerResetViewTimerDueToExecution(&mut self, val: &CRequestBatch)
    requires
        old(self).valid(),
        crequestbatch_is_valid(&val),
    ensures
        self.valid(),
        LProposerResetViewTimerDueToExecution(old(self)@, self@, abstractify_crequestbatch(&val)),
    {
        CElectionState::CElectionStateReflectExecutedRequestBatch(&mut self.election_state, val);
    }

    #[verifier(external_body)]
    pub fn CProposerProcess1b(&mut self, pkt:CPacket)
        requires 
            old(self).valid(),
            pkt.valid(),
            pkt.msg is CMessage1b,
            old(self).constants.all.config.replica_ids@.contains(pkt.src),
            pkt@.msg->bal_1b == old(self)@.max_ballot_i_sent_1a,
            old(self).current_state == 1,
            forall |op:CPacket| old(self).received_1b_packets@.contains(op) ==> op.src@ != pkt.src@,
        ensures
            self.valid(),
            LProposerProcess1b(old(self)@, self@, pkt@)
    {

    }

    #[verifier(external_body)]
    pub fn CProposerMaybeEnterPhase2(&mut self, log_truncation_point:COperationNumber) -> (sent_packets:OutboundPackets)
        requires
            old(self).valid(),
            COperationNumberIsValid(log_truncation_point),
        ensures
            self.valid(),
            sent_packets.valid(),
            LProposerMaybeEnterPhase2(old(self)@, self@, log_truncation_point as int, sent_packets@)
    {
        let sent = OutboundPackets::PacketSequence { s: (Vec::<CPacket>::new()) };
        sent
    }

    }

    #[verifier(external_body)]
    pub fn get_CElection_clone(c: &CElectionState) -> (res: CElectionState)
        requires
            c.valid()
        ensures
            res.valid(),
            res@ == c@
    {
        c.clone()
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
    pub fn get_cloned_config (elem: &CConfiguration) -> (res: CConfiguration)
        ensures
            res@ == elem@,
            res.valid()
    {
        elem.clone()
    }

    #[verifier(external_body)]
    fn get_cloned_packets (elem: &HashSet<CPacket>) -> (res: HashSet<CPacket>)
        ensures
            res@.map(|i: CPacket| i@) == elem@.map(|i: CPacket| i@),
            elem@.len() == res@.len()
    {
        elem.clone()
    }

    #[verifier(external_body)]
    fn CLtUpperBound(x: COperationNumber, n:u64 ) -> (res: bool)
        ensures
            res == LtUpperBound(x as int, UpperBound::UpperBoundFinite { n: (n as int) }),
    {
        x < n
    }

    #[verifier(external_body)]
    fn get_set_len(x: &HashSet<CPacket>) -> (res: usize)
        ensures
            res as int == x@.map(|i: CPacket|i@).len()
    {
        x.len()
    }
}
