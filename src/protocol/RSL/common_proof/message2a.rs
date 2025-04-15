use builtin::*;
use builtin_macros::*;
use vstd::{map::*, modes::*, prelude::*, seq::*, seq_lib::*, *};
use vstd::{set::*, set_lib::*};
use crate::protocol::RSL::distributed_system::*;
use crate::protocol::RSL::constants::*;
use crate::protocol::RSL::configuration::*;
use crate::protocol::RSL::types::*;
use crate::protocol::RSL::election::*;
use crate::protocol::RSL::proposer::*;
use crate::protocol::RSL::environment::*;
use crate::protocol::RSL::common_proof::assumptions::*;
use crate::protocol::RSL::common_proof::constants::*;
use crate::protocol::RSL::common_proof::actions::*;
use crate::protocol::RSL::common_proof::packet_sending::*;
use crate::protocol::RSL::common_proof::max_ballot_sent_1a::*;
use crate::protocol::RSL::common_proof::environment::*;
use crate::protocol::RSL::common_proof::receive1b::*;

use crate::common::logic::temporal_s::*;
use crate::common::logic::heuristics_i::*;
use crate::common::framework::environment_s::*;
use crate::common::framework::environment_s::LEnvStep;
use crate::common::native::io_s::*;
use crate::common::collections::maps2::*;

verus!{
    #[verifier::external_body]
    pub proof fn lemma_2aMessageImplicationsForProposerState(
        b:Behavior<RslState>,
        c:LConstants,
        i:int,
        p:RslPacket
    ) -> (
        proposer_idx:int
    )
        requires IsValidBehaviorPrefix(b, c, i),
                0 <= i,
                b[i].environment.sentPackets.contains(p),
                c.config.replica_ids.contains(p.src),
                p.msg is RslMessage2a,
        ensures 0 <= proposer_idx < c.config.replica_ids.len(),
                0 <= proposer_idx < b[i].replicas.len(),
                p.src == c.config.replica_ids[proposer_idx],
                p.msg->bal_2a.proposer_id == proposer_idx,
                //   var s := b[i].replicas[proposer_idx].replica.proposer;
                (BalLt(p.msg->bal_2a, b[i].replicas[proposer_idx].replica.proposer.max_ballot_i_sent_1a)
                || (&& b[i].replicas[proposer_idx].replica.proposer.max_ballot_i_sent_1a == p.msg->bal_2a
                        && b[i].replicas[proposer_idx].replica.proposer.current_state != 1
                        && b[i].replicas[proposer_idx].replica.proposer.next_operation_number_to_propose > p.msg->opn_2a)),
        decreases i
    {
        if i == 0
        {
          return arbitrary();
        }
    
        lemma_AssumptionsMakeValidTransition(b, c, i-1);
        lemma_ConstantsAllConsistent(b, c, i);
        lemma_ConstantsAllConsistent(b, c, i-1);
    
        if b[i-1].environment.sentPackets.contains(p)
        {
          let proposer_idx = lemma_2aMessageImplicationsForProposerState(b, c, i-1, p);
          let s = b[i-1].replicas[proposer_idx].replica.proposer;
          let s_ = b[i].replicas[proposer_idx].replica.proposer;
          if s_ != s
          {
            let ios = lemma_ActionThatChangesReplicaIsThatReplicasAction(b, c, i-1, proposer_idx);
          }
          return proposer_idx;
        }
    
        // let ios:Seq<RslIo>;
        let (proposer_idx, ios) = lemma_ActionThatSends2aIsMaybeNominateValueAndSend2a(b[i-1], b[i], p);
        lemma_max_balISent1aHasMeAsProposer(b, c, i-1, proposer_idx);
        proposer_idx
    }
    

    #[verifier::external_body]
    pub proof fn lemma_Find2aThatCausedVote(
        b:Behavior<RslState>,
        c:LConstants,
        i:int,
        idx:int,
        opn:OperationNumber
    ) -> (
          p:RslPacket
    )
        requires IsValidBehaviorPrefix(b, c, i),
                 0 <= i,
                 0 <= idx < b[i].replicas.len(),
                 b[i].replicas[idx].replica.acceptor.votes.contains_key(opn),
        ensures b[i].environment.sentPackets.contains(p),
                c.config.replica_ids.contains(p.src),
                p.msg is RslMessage2a,
                p.msg->opn_2a == opn,
                p.msg->val_2a == b[i].replicas[idx].replica.acceptor.votes[opn].max_val,
                p.msg->bal_2a == b[i].replicas[idx].replica.acceptor.votes[opn].max_value_bal,
        decreases i
    {
        if i == 0
        {
          return arbitrary();
        }
    
        lemma_ReplicaConstantsAllConsistent(b, c, i, idx);
        lemma_ReplicaConstantsAllConsistent(b, c, i-1, idx);
        lemma_AssumptionsMakeValidTransition(b, c, i-1);
    
        let s = b[i-1].replicas[idx].replica.acceptor;
        let s_ = b[i].replicas[idx].replica.acceptor;
    
        if s.votes.contains_key(opn) && s_.votes[opn] == s.votes[opn]
        {
          let p = lemma_Find2aThatCausedVote(b, c, i-1, idx, opn);
          return p;
        }
    
        let ios = lemma_ActionThatChangesReplicaIsThatReplicasAction(b, c, i-1, idx);
        let p = ios[0]->r;
        return p;
    }

    #[verifier::external_body]
    pub proof fn lemma_2aMessagesFromSameBallotAndOperationMatch(
        b:Behavior<RslState>,
        c:LConstants,
        i:int,
        p1:RslPacket,
        p2:RslPacket
    )
        requires IsValidBehaviorPrefix(b, c, i),
                0 <= i,
                b[i].environment.sentPackets.contains(p1),
                b[i].environment.sentPackets.contains(p2),
                c.config.replica_ids.contains(p1.src),
                c.config.replica_ids.contains(p2.src),
                p1.msg is RslMessage2a,
                p2.msg is RslMessage2a,
                p1.msg->opn_2a == p2.msg->opn_2a,
                p1.msg->bal_2a == p2.msg->bal_2a,
        ensures  p1.msg->val_2a == p2.msg->val_2a,
        decreases 2 * i + 1
    {
        if i == 0
        {
          return;
        }
    
        if b[i-1].environment.sentPackets.contains(p2) && !b[i-1].environment.sentPackets.contains(p1)
        {
          lemma_2aMessagesFromSameBallotAndOperationMatchWithoutLossOfGenerality(b, c, i, p2, p1);
        }
        else
        {
          lemma_2aMessagesFromSameBallotAndOperationMatchWithoutLossOfGenerality(b, c, i, p1, p2);
        }
    }
    
    #[verifier::external_body]
    pub proof fn lemma_2aMessagesFromSameBallotAndOperationMatchWithoutLossOfGenerality(
        b:Behavior<RslState>,
        c:LConstants,
        i:int,
        p1:RslPacket,
        p2:RslPacket
    )
        requires IsValidBehaviorPrefix(b, c, i),
                0 < i,
                b[i].environment.sentPackets.contains(p1),
                b[i].environment.sentPackets.contains(p2),
                c.config.replica_ids.contains(p1.src),
                c.config.replica_ids.contains(p2.src),
                p1.msg is RslMessage2a,
                p2.msg is RslMessage2a,
                p1.msg->opn_2a == p2.msg->opn_2a,
                p1.msg->bal_2a == p2.msg->bal_2a,
                b[i-1].environment.sentPackets.contains(p2) ==> b[i-1].environment.sentPackets.contains(p1),
        ensures  p1.msg->val_2a == p2.msg->val_2a,
        decreases 2 * i
    {
        lemma_AssumptionsMakeValidTransition(b, c, i-1);
        lemma_ConstantsAllConsistent(b, c, i);
        lemma_ConstantsAllConsistent(b, c, i-1);
    
        if b[i-1].environment.sentPackets.contains(p2)
        {
          // Both packets had already been sent by i-1, so we induction.
          lemma_2aMessagesFromSameBallotAndOperationMatch(b, c, i-1, p1, p2);
          return;
        }
    
        let (proposer_idx, ios) = lemma_ActionThatSends2aIsMaybeNominateValueAndSend2a(b[i-1], b[i], p2);
    
        if !b[i-1].environment.sentPackets.contains(p1)
        {
          // Both packets were sent in step i-1, so observe that any two packets sent in the same step
          // have the same value.
          assert(ios.contains(LIoOp::Send{s:p1}));
          assert(ios.contains(LIoOp::Send{s:p2}));
          return;
        }
    
        // Note the implications on processor state for p1, since once p1 is sent we
        // won't be able to send p2.
        let alt_proposer_idx = lemma_2aMessageImplicationsForProposerState(b, c, i-1, p1);
    
        // Note the implications on processor state for p2, just to notice that they
        // use the same replica index.
        let alt2_proposer_idx = lemma_2aMessageImplicationsForProposerState(b, c, i, p2);
        assert(alt_proposer_idx == alt2_proposer_idx);
        assert(ReplicasDistinct(c.config.replica_ids, proposer_idx, alt_proposer_idx));
        assert(proposer_idx == alt_proposer_idx);
        assert(false);
    }

    #[verifier::external_body]
    pub proof fn lemma_2aMessageHas1bQuorumPermittingIt(
        b: Behavior<RslState>,
        c: LConstants,
        i: int,
        p: RslPacket
    ) -> (q: Set<RslPacket>)
        requires
            IsValidBehaviorPrefix(b, c, i),
            0 <= i,
            b[i].environment.sentPackets.contains(p),
            c.config.replica_ids.contains(p.src),
            p.msg is RslMessage2a,
        ensures
            q.subset_of(b[i].environment.sentPackets),
            q.len() >= LMinQuorumSize(c.config),
            LIsAfterLogTruncationPoint(p.msg->opn_2a, q),
            LSetOfMessage1bAboutBallot(q, p.msg->bal_2a),
            LAllAcceptorsHadNoProposal(q, p.msg->opn_2a) || LValIsHighestNumberedProposal(p.msg->val_2a, q, p.msg->opn_2a),
            forall|p1, p2: RslPacket| q.contains(p1) && q.contains(p2) && p1 != p2 ==> p1.src != p2.src,
            forall|p1: RslPacket| q.contains(p1) ==> c.config.replica_ids.contains(p1.src),
        decreases i
    {
        if i == 0 {
            return Set::empty();
        }

        if b[i - 1].environment.sentPackets.contains(p) {
            let q_prev = lemma_2aMessageHas1bQuorumPermittingIt(b, c, i - 1, p);
            lemma_PacketSetStaysInSentPackets(b, c, i - 1, i, q_prev);
            return q_prev;
        }

        lemma_ConstantsAllConsistent(b, c, i - 1);
        lemma_ConstantsAllConsistent(b, c, i);
        lemma_AssumptionsMakeValidTransition(b, c, i - 1);
        let (idx, ios) = lemma_ActionThatSends2aIsMaybeNominateValueAndSend2a(b[i - 1], b[i], p);
        let q_new = b[i - 1].replicas[idx].replica.proposer.received_1b_packets;

        assert forall|p_1b: RslPacket| q_new.contains(p_1b) implies b[i].environment.sentPackets.contains(p_1b)
        by {
            lemma_PacketInReceived1bWasSent(b, c, i - 1, idx, p_1b);
            lemma_PacketStaysInSentPackets(b, c, i - 1, i, p_1b);
        }

        lemma_Received1bPacketsAreFrommax_balISent1a(b, c, i - 1, idx);
        return q_new;
    }

    #[verifier::external_body]
    pub proof fn lemma_2aMessageHasValidBallot(
        b: Behavior<RslState>,
        c: LConstants,
        i: int,
        p: RslPacket
    )
        requires
            IsValidBehaviorPrefix(b, c, i),
            0 <= i,
            b[i].environment.sentPackets.contains(p),
            c.config.replica_ids.contains(p.src),
            p.msg is RslMessage2a,
        ensures
            p.msg->bal_2a.seqno >= 0,
            0 <= p.msg->bal_2a.proposer_id < c.config.replica_ids.len(),
    {
        if i == 0 {
            return;
        }

        lemma_ConstantsAllConsistent(b, c, i - 1);
        lemma_ConstantsAllConsistent(b, c, i);
        lemma_AssumptionsMakeValidTransition(b, c, i - 1);

        if b[i - 1].environment.sentPackets.contains(p) {
            lemma_2aMessageHasValidBallot(b, c, i - 1, p);
            return;
        }

        let (idx, ios) = lemma_ActionThatSends2aIsMaybeNominateValueAndSend2a(b[i - 1], b[i], p);
        lemma_max_balISent1aHasMeAsProposer(b, c, i - 1, idx);
    }
}