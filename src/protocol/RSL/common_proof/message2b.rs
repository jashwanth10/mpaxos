use builtin::*;
use builtin_macros::*;
use vstd::{map::*, modes::*, prelude::*, seq::*, seq_lib::*, *};
use vstd::{set::*, set_lib::*};
use crate::protocol::RSL::distributed_system::*;
use crate::protocol::RSL::constants::*;
use crate::protocol::RSL::types::*;
use crate::protocol::RSL::election::*;
use crate::protocol::RSL::environment::*;
use crate::protocol::RSL::common_proof::assumptions::*;
use crate::protocol::RSL::common_proof::constants::*;
use crate::protocol::RSL::common_proof::actions::*;
use crate::protocol::RSL::common_proof::message2a::*;
use crate::protocol::RSL::common_proof::environment::*;
use crate::protocol::RSL::common_proof::packet_sending::*;

use crate::common::logic::temporal_s::*;
use crate::common::logic::heuristics_i::*;
use crate::common::framework::environment_s::*;
use crate::common::framework::environment_s::LEnvStep;
use crate::common::native::io_s::*;
use crate::common::collections::maps2::*;

verus!{
    #[verifier::external_body]
    pub proof fn lemma_2bMessageHasCorresponding2aMessage(
        b:Behavior<RslState>,
        c:LConstants,
        i:int,
        p_2b:RslPacket
    ) -> (
        p_2a:RslPacket
    )
        requires IsValidBehaviorPrefix(b, c, i),
                0 <= i,
                b[i].environment.sentPackets.contains(p_2b),
                c.config.replica_ids.contains(p_2b.src),
                p_2b.msg is RslMessage2b,
        ensures b[i].environment.sentPackets.contains(p_2a),
                c.config.replica_ids.contains(p_2a.src),
                p_2a.msg is RslMessage2a,
                p_2a.msg->opn_2a == p_2b.msg->opn_2b,
                p_2a.msg->bal_2a == p_2b.msg->bal_2b,
                p_2a.msg->val_2a == p_2b.msg->val_2b,
        decreases i
    {
        if i == 0
        {
          return arbitrary();
        }
    
        if b[i-1].environment.sentPackets.contains(p_2b)
        {
          let p_2a = lemma_2bMessageHasCorresponding2aMessage(b, c, i-1, p_2b);
          lemma_PacketStaysInSentPackets(b, c, i-1, i, p_2a);
          return p_2a;
        }
    
        lemma_AssumptionsMakeValidTransition(b, c, i-1);
        lemma_ConstantsAllConsistent(b, c, i);
        lemma_ConstantsAllConsistent(b, c, i-1);
    
        let (proposer_idx, ios) = lemma_ActionThatSends2bIsProcess2a(b[i-1], b[i], p_2b);
        let p_2a = ios[0]->r;
        p_2a
    }

    pub proof fn lemma_CurrentVoteDoesNotExceedMaxBal(
        b:Behavior<RslState>,
        c:LConstants,
        i:int,
        opn:OperationNumber,
        idx:int
    )
        requires IsValidBehaviorPrefix(b, c, i),
                 0 <= i,
                 0 <= idx < b[i].replicas.len(),
                 b[i].replicas[idx].replica.acceptor.votes.contains_key(opn),
        ensures  BalLeq(b[i].replicas[idx].replica.acceptor.votes[opn].max_value_bal, b[i].replicas[idx].replica.acceptor.max_bal),
        decreases i
    {
        if i == 0
        {
            return;
        }

        lemma_ReplicaConstantsAllConsistent(b, c, i, idx);
        lemma_ReplicaConstantsAllConsistent(b, c, i-1, idx);

        let s = b[i-1].replicas[idx].replica.acceptor;
        let s_ = b[i].replicas[idx].replica.acceptor;
        if s_.votes == s.votes && s_.max_bal == s.max_bal
        {
            lemma_CurrentVoteDoesNotExceedMaxBal(b, c, i-1, opn, idx);
            return;
        }

        let ios = lemma_ActionThatChangesReplicaIsThatReplicasAction(b, c, i-1, idx);
        if s.votes.contains_key(opn)
        {
            lemma_CurrentVoteDoesNotExceedMaxBal(b, c, i-1, opn, idx);
        }
    }

    #[verifier::external_body]
    pub proof fn lemma_ActionThatOverwritesVoteWithSameBallotDoesntChangeValue(
        b:Behavior<RslState>,
        c:LConstants,
        i:int,
        opn:OperationNumber,
        bal:Ballot,
        idx:int
    )
        requires IsValidBehaviorPrefix(b, c, i+1),
                 0 <= i,
                 0 <= idx < b[i].replicas.len(),
                 0 <= idx < b[i+1].replicas.len(),
                 b[i].replicas[idx].replica.acceptor.votes.contains_key(opn),
                 b[i+1].replicas[idx].replica.acceptor.votes.contains_key(opn),
                 b[i].replicas[idx].replica.acceptor.votes[opn].max_value_bal == b[i+1].replicas[idx].replica.acceptor.votes[opn].max_value_bal,
        ensures  b[i].replicas[idx].replica.acceptor.votes[opn].max_val == b[i+1].replicas[idx].replica.acceptor.votes[opn].max_val
    {
        lemma_ReplicaConstantsAllConsistent(b, c, i, idx);
        lemma_ReplicaConstantsAllConsistent(b, c, i+1, idx);
        lemma_AssumptionsMakeValidTransition(b, c, i);
    
        let s = b[i].replicas[idx].replica.acceptor;
        let s_ = b[i+1].replicas[idx].replica.acceptor;
    
        if s_.votes[opn].max_val != s.votes[opn].max_val
        {
          let ios = lemma_ActionThatChangesReplicaIsThatReplicasAction(b, c, i, idx);
          let earlier_2a = lemma_Find2aThatCausedVote(b, c, i, idx, opn);
          lemma_2aMessagesFromSameBallotAndOperationMatch(b, c, i+1, earlier_2a, ios[0]->r);
          assert(false);
        }
    }

    #[verifier::external_body]
    pub proof fn lemma_VoteWithOpnImplies2aSent(
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
                p.msg->bal_2a == b[i].replicas[idx].replica.acceptor.votes[opn].max_value_bal,
                p.msg->val_2a == b[i].replicas[idx].replica.acceptor.votes[opn].max_val,
        decreases i
    {
        if i == 0
        {
          return arbitrary();
        }
    
        lemma_AssumptionsMakeValidTransition(b, c, i-1);
        lemma_ConstantsAllConsistent(b, c, i);
        lemma_ConstantsAllConsistent(b, c, i-1);
    
        let s = b[i-1].replicas[idx].replica.acceptor;
        let s_ = b[i].replicas[idx].replica.acceptor;
    
        if s_.votes == s.votes
        {
          let p = lemma_VoteWithOpnImplies2aSent(b, c, i-1, idx, opn);
          return p;
        }
    
        let ios = lemma_ActionThatChangesReplicaIsThatReplicasAction(b, c, i-1, idx);
        if s.votes.contains_key(opn) && s_.votes[opn] == s.votes[opn]
        {
          let p = lemma_VoteWithOpnImplies2aSent(b, c, i-1, idx, opn);
          return p;
        }
    
        let p = ios[0]->r;
        p
    }

    #[verifier::external_body]
    pub proof fn lemma_2bMessageImplicationsForCAcceptor(
        b: Behavior<RslState>,
        c: LConstants,
        i: int,
        p: RslPacket
    ) -> (acceptor_idx: int)
        requires
            IsValidBehaviorPrefix(b, c, i),
            0 <= i,
            b[i].environment.sentPackets.contains(p),
            c.config.replica_ids.contains(p.src),
            p.msg is RslMessage2b,
        ensures
            0 <= acceptor_idx < c.config.replica_ids.len(),
            0 <= acceptor_idx < b[i].replicas.len(),
            p.src == c.config.replica_ids.index(acceptor_idx),
            BalLeq(p.msg->bal_2b, b[i].replicas.index(acceptor_idx).replica.acceptor.max_bal),
            ({
                let s = b[i].replicas.index(acceptor_idx).replica.acceptor;
                if p.msg->opn_2b >= s.log_truncation_point {
                    s.votes.contains_key(p.msg->opn_2b) &&
                    BalLeq(p.msg->bal_2b, s.votes[p.msg->opn_2b].max_value_bal) &&
                    (s.votes[p.msg->opn_2b].max_value_bal == p.msg->bal_2b ==> s.votes[p.msg->opn_2b].max_val == p.msg->val_2b)
                } else {
                    true
                }
            }),
        decreases i,
    {
        if i == 0 {
            return arbitrary(); // Placeholder return value
        }
    
        lemma_AssumptionsMakeValidTransition(b, c, i - 1);
        lemma_ConstantsAllConsistent(b, c, i);
        lemma_ConstantsAllConsistent(b, c, i - 1);
    
        let v = p.msg->val_2b;
        let opn = p.msg->opn_2b;
        let bal = p.msg->bal_2b;
    
        if b[i - 1].environment.sentPackets.contains(p) {
            let acceptor_idx = lemma_2bMessageImplicationsForCAcceptor(b, c, i - 1, p);
            let s = b[i - 1].replicas.index(acceptor_idx).replica.acceptor;
            let s_prime = b[i].replicas.index(acceptor_idx).replica.acceptor;
            if s_prime != s {
                let ios = lemma_ActionThatChangesReplicaIsThatReplicasAction(b, c, i - 1, acceptor_idx);
                if opn >= s_prime.log_truncation_point {
                    lemma_CurrentVoteDoesNotExceedMaxBal(b, c, i - 1, opn, acceptor_idx);
                    if s_prime.votes[p.msg->opn_2b].max_value_bal == s.votes[p.msg->opn_2b].max_value_bal {
                        lemma_ActionThatOverwritesVoteWithSameBallotDoesntChangeValue(b, c, i - 1, opn, bal, acceptor_idx);
                    }
                }
            }
            return acceptor_idx;
        }
    
        let (acceptor_idx, ios) = lemma_ActionThatSends2bIsProcess2a(b[i - 1], b[i], p);
        let s = b[i - 1].replicas.index(acceptor_idx).replica.acceptor;
        let s_prime = b[i].replicas.index(acceptor_idx).replica.acceptor;
        assert(p.msg->opn_2b >= s_prime.log_truncation_point ==> 
            s_prime.votes.contains_key(p.msg->opn_2b) &&
            BalLeq(p.msg->bal_2b, s_prime.votes[p.msg->opn_2b].max_value_bal) &&
            (s_prime.votes[p.msg->opn_2b].max_value_bal == p.msg->bal_2b ==> s_prime.votes[p.msg->opn_2b].max_val == p.msg->val_2b));
        
        return acceptor_idx;
    }
}