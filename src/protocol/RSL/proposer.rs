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
use crate::protocol::RSL::state_machine::*;
use crate::protocol::RSL::election::*;

use crate::protocol::common::upper_bound::*;

use crate::services::RSL::app_state_machine::*;

use crate::common::framework::environment_s::*;
use crate::common::native::io_s::*;

verus! {
    pub enum IncompleteBatchTimer{
        IncompleteBatchTimerOn{when:int},
        IncompleteBatchTimerOff{},
    }

    pub struct LProposer{
        pub constants:LReplicaConstants,
        // The replica constants, duplicated here for convenience

        pub current_state:int,
        // What state the proposer is in:
        // 0 = not leader
        // 1 = leader in phase 1
        // 2 = leader in phase 2

        // request_queue:RequestBatch,
        pub request_queue:Seq<Request>,
        // Values that clients have requested that I need to eventually
        // propose, in the order I should propose them

        pub max_ballot_i_sent_1a:Ballot,
        // The maximum ballot I've sent a 1a message for

        pub next_operation_number_to_propose:int,
        // The next operation number I should propose

        pub received_1b_packets:Set<RslPacket>,
        // The set of 1b messages I've received concerning max_ballot_i_sent_1a

        pub highest_seqno_requested_by_client_this_view:Map<AbstractEndPoint, int>,
        // For each client, the highest sequence number for a request
        // I proposed in max_ballot_i_sent_1a

        pub incomplete_batch_timer:IncompleteBatchTimer,
        // If the incomplete batch timer is set, it indicates when I should
        // give up on trying to amass a full-size batch and just propose
        // whatever I have.  If it's not set, I shouldn't propose an
        // incomplete batch.

        pub election_state:ElectionState,
        // State for view change election management
    }

    pub open spec fn LIsAfterLogTruncationPoint(opn:OperationNumber, received_1b_packets:Set<RslPacket>) -> bool
    {
        (forall |p:RslPacket| received_1b_packets.contains(p) && p.msg is RslMessage1b ==> p.msg->log_truncation_point <= opn)
    }


    pub open spec fn LSetOfMessage1b(S:Set<RslPacket>) -> bool
    {
        forall |p:RslPacket| S.contains(p) ==> p.msg is RslMessage1b
    }

    pub open spec fn LSetOfMessage1bAboutBallot(S:Set<RslPacket>, b:Ballot) -> bool
    {
        &&& LSetOfMessage1b(S)
        &&& (forall |p:RslPacket| S.contains(p) ==> p.msg->bal_1b == b)
    }

    pub open spec fn LExistVotesHasProposalLargeThanOpn(p:RslPacket, op:OperationNumber) -> bool
        recommends 
            p.msg is RslMessage1b
    {
        exists |opn:OperationNumber| p.msg->votes.contains_key(opn) && opn > op
    }

    pub open spec fn LExistsAcceptorHasProposalLargeThanOpn(S:Set<RslPacket>, op:OperationNumber) -> bool
    recommends 
            LSetOfMessage1b(S)
    {
        // exists p :: p in S && exists opn :: opn in p.msg.votes && opn > op
        exists |p:RslPacket| S.contains(p) && LExistVotesHasProposalLargeThanOpn(p, op)
    }

    pub open spec fn LAllAcceptorsHadNoProposal(S:Set<RslPacket>, opn:OperationNumber) -> bool
    recommends 
            LSetOfMessage1b(S)
    {
        forall |p:RslPacket| S.contains(p) ==> !p.msg->votes.contains_key(opn)
    }

    pub open spec fn Lmax_balInS(c:Ballot, S:Set<RslPacket>, opn:OperationNumber) -> bool
    recommends 
            LSetOfMessage1b(S)
    {
        forall |p:RslPacket| S.contains(p) && p.msg->votes.contains_key(opn) ==> BalLeq(p.msg->votes[opn].max_value_bal, c)
    }

    pub open spec fn LExistsBallotInS(v:RequestBatch, c:Ballot, S:Set<RslPacket>, opn:OperationNumber) -> bool
    recommends 
            LSetOfMessage1b(S)
    {
        exists |p:RslPacket| S.contains(p)
                    && p.msg->votes.contains_key(opn)
                    && p.msg->votes[opn].max_value_bal==c
                    && p.msg->votes[opn].max_val==v
    }

    pub open spec fn LValIsHighestNumberedProposalAtBallot(v:RequestBatch, c:Ballot, S:Set<RslPacket>, opn:OperationNumber) -> bool
    recommends 
            LSetOfMessage1b(S)
    {
        &&& Lmax_balInS(c, S, opn)
        &&& LExistsBallotInS(v, c, S, opn)
    }

    pub open spec fn LValIsHighestNumberedProposal(v:RequestBatch, S:Set<RslPacket>, opn:OperationNumber) -> bool
    recommends 
            LSetOfMessage1b(S)
    {
        // exists c :: c in S && opn in c.msg.votes && LValIsHighestNumberedProposalAtBallot(v, c, S, opn)
        exists |c:Ballot| LValIsHighestNumberedProposalAtBallot(v, c, S, opn)
    }

    pub open spec fn LProposerCanNominateUsingOperationNumber(s:LProposer, log_truncation_point:OperationNumber, opn:OperationNumber) -> bool
    {
        &&& s.election_state.current_view == s.max_ballot_i_sent_1a
        &&& s.current_state == 2
        &&& s.received_1b_packets.len() >= LMinQuorumSize(s.constants.all.config)
        &&& LSetOfMessage1bAboutBallot(s.received_1b_packets, s.max_ballot_i_sent_1a)
        // Don't try to nominate for an operation that's already been truncated into history:
        &&& LIsAfterLogTruncationPoint(opn, s.received_1b_packets)
        // Don't try to nominate in an operation that's too far in the future; that would grow the log too much.
        &&& opn < UpperBoundedAddition(log_truncation_point, s.constants.all.params.max_log_length, s.constants.all.params.max_integer_val)
        // Disallow negative operations
        &&& opn >= 0
        // It must be possible to add one and still be representable, so we can compute next_operation_number_to_propose
        &&& LtUpperBound(opn, s.constants.all.params.max_integer_val)
    }

    pub open spec fn LProposerInit(s:LProposer, c:LReplicaConstants) -> bool
    recommends 
            WellFormedLConfiguration(c.all.config)
    {
        
    }

    pub open spec fn LProposerProcessRequest(
        s:LProposer, 
        s_:LProposer, 
        packet:RslPacket
    ) -> bool
    recommends 
            packet.msg is RslMessageRequest
    {
        
    }

    pub open spec fn LProposerMaybeEnterNewViewAndSend1a(
        s:LProposer, 
        s_:LProposer, 
        sent_packets:Seq<RslPacket>
    ) -> bool
    {
        
    }

    pub open spec fn LProposerProcess1b(
        s:LProposer, 
        s_:LProposer, 
        p:RslPacket
    ) -> bool
    recommends 
            p.msg is RslMessage1b,
            s.constants.all.config.replica_ids.contains(p.src),
            p.msg->bal_1b == s.max_ballot_i_sent_1a,
            s.current_state == 1,
            forall |other_packet:RslPacket| s.received_1b_packets.contains(other_packet) ==> other_packet.src != p.src
    {
        
    }

    pub open spec fn LProposerMaybeEnterPhase2(
        s:LProposer, 
        s_:LProposer, 
        log_truncation_point:OperationNumber, 
        sent_packets:Seq<RslPacket>
    ) -> bool
    {
        
    }
    
    pub open spec fn LProposerNominateNewValueAndSend2a(
        s:LProposer, 
        s_:LProposer, 
        clock:int, 
        log_truncation_point:OperationNumber,
        sent_packets:Seq<RslPacket>
    ) -> bool
    recommends 
            LProposerCanNominateUsingOperationNumber(s, log_truncation_point, s.next_operation_number_to_propose),
            LAllAcceptorsHadNoProposal(s.received_1b_packets, s.next_operation_number_to_propose)
    {
        
    }

    pub open spec fn LProposerNominateOldValueAndSend2a(
        s:LProposer, 
        s_:LProposer, 
        log_truncation_point:OperationNumber, 
        sent_packets:Seq<RslPacket>
    ) -> bool
    recommends LProposerCanNominateUsingOperationNumber(s, log_truncation_point, s.next_operation_number_to_propose),
                 !LAllAcceptorsHadNoProposal(s.received_1b_packets, s.next_operation_number_to_propose)
    {
        
    }

    pub open spec fn LProposerMaybeNominateValueAndSend2a(
        s:LProposer, 
        s_:LProposer, 
        clock:int, 
        log_truncation_point:int, 
        sent_packets:Seq<RslPacket>
    ) -> bool 
    {
        
    }

    pub open spec fn LProposerProcessHeartbeat(
        s:LProposer, 
        s_:LProposer, 
        p:RslPacket, 
        clock:int
    ) -> bool
    recommends 
            p.msg is RslMessageHeartbeat
    {
        
    }

    pub open spec fn LProposerCheckForViewTimeout(
        s:LProposer, 
        s_:LProposer, 
        clock:int
    ) -> bool
    {
        
    }

    pub open spec fn LProposerCheckForQuorumOfViewSuspicions(
        s:LProposer, 
        s_:LProposer, 
        clock:int
    ) -> bool 
    {
        
    }

    pub open spec fn LProposerResetViewTimerDueToExecution(
        s:LProposer, 
        s_:LProposer, 
        val:RequestBatch
    ) -> bool    
    {
        
    }


}