use crate::common::collections::vecs::concat_vecs;
use crate::common::native::io_s::*;
use crate::implementation::common::generic_refinement::*;
use crate::implementation::common::upper_bound::*;
use crate::implementation::RSL::cbroadcast::*;
use crate::implementation::RSL::cconfiguration::*;
use crate::implementation::RSL::cconstants::*;
use crate::implementation::RSL::cmessage::*;
use crate::implementation::RSL::types_i::*;
use crate::implementation::RSL::ElectionImpl::*;
use crate::protocol::common::upper_bound::UpperBoundedAddition;
use crate::protocol::RSL::proposer::*;
use builtin::*;
use builtin_macros::*;
use std::collections::*;
use vstd::invariant;
use vstd::{map::*, prelude::*, seq::*, set::*};

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

impl CProposer{

    pub open spec fn abstractable(self) -> bool {
        &&& self.constants.abstractable()
        &&& (forall |i:int| 0 <= i < self.request_queue@.len() ==> self.request_queue@[i].abstractable())
        &&& self.max_ballot_i_sent_1a.abstractable()
        &&& (forall |p:CPacket| self.received_1b_packets@.contains(p) ==> p.abstractable())
        &&& (forall |k:EndPoint, v:u64| self.highest_seqno_requested_by_client_this_view@.contains_key(k) ==> k.abstractable())
        &&& self.incomplete_batch_timer.abstractable()
        &&& self.election_state.abstractable()
    }

    pub open spec fn valid(self) -> bool {
        &&& self.abstractable()
        &&& self.constants.valid()
        &&& (forall |i:int| 0 <= i < self.request_queue@.len() ==> self.request_queue@[i].valid())
        &&& self.max_ballot_i_sent_1a.valid()
        &&& (forall |p:CPacket| self.received_1b_packets@.contains(p) ==> p.valid())
        &&& (forall |k:EndPoint, v:u64| self.highest_seqno_requested_by_client_this_view@.contains_key(k) ==> k.valid_public_key())
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

    // #[verifier(external_body)]
    pub fn CIsAfterLogTruncationPoint(opn:COperationNumber, received_1b_packets:HashSet<CPacket>) -> bool
    {

    }

    // #[verifier(external_body)]
    pub fn CSetOfMessage1b(S : HashSet<CPacket>) -> bool
    {

    }

    // #[verifier(external_body)]
    pub fn CSetOfMessage1bAboutBallot(S:HashSet<CPacket>, b:CBallot) -> bool
    {
        
    }

    // #[verifier(external_body)]
    pub fn CAllAcceptorsHadNoProposal(S:HashSet<CPacket>, opn:COperationNumber) -> (result_CAllAcceptorsHadNoProposal:bool)
    requires
        forall |p:CPacket| S@.contains(p) ==> p.valid(),
        COperationNumberIsValid(opn),
        ({
            forall |p:CPacket| S@.contains(p) ==> p.msg is CMessage1b
        })
    ensures
        ({
            let lr = LAllAcceptorsHadNoProposal(S@.map(|p:CPacket| p.view()), AbstractifyCOperationNumberToOperationNumber(opn));
            result_CAllAcceptorsHadNoProposal == lr
        })
    {
        
    }

    // #[verifier(external_body)]
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

    }

    // #[verifier(external_body)]
    pub fn CExistsAcceptorHasProposalLargeThanOpn(S:HashSet<CPacket>, op:COperationNumber) -> (result_CExistsAcceptorHasProposalLargeThanOpn:bool)
    requires
        forall |p:CPacket| S@.contains(p) ==> p.valid(),
        COperationNumberIsValid(op),
        ({
            forall |p:CPacket| S@.contains(p) ==> p.msg is CMessage1b
        })
    ensures
    ({
        let lr = LExistsAcceptorHasProposalLargeThanOpn(S@.map(|p:CPacket| p.view()), AbstractifyCOperationNumberToOperationNumber(op));
        result_CExistsAcceptorHasProposalLargeThanOpn == lr
    })

    {
        
    }

    // #[verifier(external_body)]
    pub fn Cmax_balInS(c:CBallot, S:HashSet<CPacket>, opn:COperationNumber) -> (result_Cmax_balInS:bool)
    requires
        c.valid(),
        forall |p:CPacket| S@.contains(p) ==> p.valid(),
        COperationNumberIsValid(opn),
        ({
            forall |p:CPacket| S@.contains(p) ==> p.msg is CMessage1b
        })
    ensures
    ({
        let lr = Lmax_balInS(c.view(),S@.map(|p:CPacket| p.view()), AbstractifyCOperationNumberToOperationNumber(opn));
        result_Cmax_balInS == lr
    })
    {
        
    }

    // #[verifier(external_body)]
    pub fn CExistsBallotInS(v: CRequestBatch, c: CBallot, S: HashSet<CPacket>, opn:COperationNumber) -> (result_CExistsBallotInS:bool)
    requires
        crequestbatch_is_valid(v),
        c.valid(),
        forall |p:CPacket| S@.contains(p) ==> p.valid(),
        COperationNumberIsValid(opn),
        ({
            forall |p:CPacket| S@.contains(p) ==> p.msg is CMessage1b
        })
    ensures
    ({
        let lr = LExistsBallotInS(abstractify_crequestbatch(v), c.view(), S@.map(|p:CPacket| p.view()), AbstractifyCOperationNumberToOperationNumber(opn));
        result_CExistsBallotInS == lr
    })
    {
       
    }

    // #[verifier(external_body)]
    pub fn CValIsHighestNumberedProposalAtBallot(v:CRequestBatch, c:CBallot, S:HashSet<CPacket>, opn:COperationNumber) -> (result_CValIsHighestNumberedProposalAtBallot:bool)
    requires
        crequestbatch_is_valid(v),
        c.valid(),
        forall |p:CPacket| S@.contains(p) ==> p.valid(),
        COperationNumberIsValid(opn),
        ({
            forall |p:CPacket| S@.contains(p) ==> p.msg is CMessage1b
        })
    ensures
    ({
        let lr = LValIsHighestNumberedProposalAtBallot(abstractify_crequestbatch(v), c.view(), S@.map(|p:CPacket| p.view()), AbstractifyCOperationNumberToOperationNumber(opn));
        result_CValIsHighestNumberedProposalAtBallot == lr
    })
    {
        
    }


    // #[verifier(external_body)]
    pub fn CValIsHighestNumberedProposal(v: CRequestBatch, S: HashSet<CPacket>, opn:COperationNumber ) -> (result_CValIsHighestNumberedProposal:bool)
    requires
        crequestbatch_is_valid(v),
        forall |p:CPacket| S@.contains(p) ==> p.valid(),
        COperationNumberIsValid(opn),
        ({
            forall |p:CPacket| S@.contains(p) ==> p.msg is CMessage1b
        })
    ensures
    ({
        let lr = LValIsHighestNumberedProposal(abstractify_crequestbatch(v), S@.map(|p:CPacket| p.view()), AbstractifyCOperationNumberToOperationNumber(opn));
        result_CValIsHighestNumberedProposal == lr
    })
    {
        
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
        
    }

    // #[verifier(external_body)]
    pub fn CProposerInit(c : CReplicaConstants)->(result_CProposerInit:CProposer)
    requires
        c.valid(),
    ensures
        result_CProposerInit.valid(),
        LProposerInit(result_CProposerInit@, c@)
    {

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
        
    }

    // #[verifier(external_body)]
    pub fn CProposerCheckForViewTimeout(& mut self, clock:u64)
    requires
        old(self).valid(),
    ensures
        self.valid(),
        LProposerCheckForViewTimeout(old(self)@, self@, clock as int)

    {
        
    }

    // #[verifier(external_body)]
    pub fn CProposerCheckForQuorumOfViewSuspicions(&mut self, clock:u64)
    requires
        old(self).valid(),
    ensures
        self.valid(),
        LProposerCheckForQuorumOfViewSuspicions(old(self)@, self@, clock as int)
    {

    }

    // #[verifier(external_body)]
    pub fn CProposerResetViewTimerDueToExecution(&mut self, val: CRequestBatch)
    requires
        old(self).valid(),
        crequestbatch_is_valid(val),
    ensures
        self.valid(),
        LProposerResetViewTimerDueToExecution(old(self)@, self@, abstractify_crequestbatch(val)),
    {
        
    }

    }
}
