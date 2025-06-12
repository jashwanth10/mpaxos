use std::any::Any;

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
use crate::protocol::common::upper_bound::LeqUpperBound;
use crate::common::framework::environment_s::*;
use crate::common::native::io_s::*;
use crate::common::collections::count_matches::*;


verus! {
    pub struct LAcceptor {
        pub constants:LReplicaConstants,
        pub max_bal:Ballot,
        pub votes:Votes,
        pub last_checkpointed_operation:Seq<OperationNumber>,
        pub log_truncation_point:OperationNumber,
    }

    pub open spec fn IsLogTruncationPointValid(log_truncation_point:OperationNumber, last_checkpointed_operation:Seq<OperationNumber>,
                                              config:LConfiguration) -> bool
    {
        IsNthHighestValueInSequence(log_truncation_point, last_checkpointed_operation, LMinQuorumSize(config))
    }

    pub open spec fn RemoveVotesBeforeLogTruncationPoint(votes:Votes, votes_:Votes, log_truncation_point:OperationNumber) -> bool
    {
        &&& forall |opn: OperationNumber| votes_.contains_key(opn) ==> votes.contains_key(opn) && votes_[opn] == votes[opn]
        &&& forall |opn: OperationNumber| opn < log_truncation_point ==> !votes_.contains_key(opn)
        &&& forall |opn: OperationNumber| opn >= log_truncation_point && votes.contains_key(opn) ==> votes_.contains_key(opn)        
    }

    pub open spec fn LAddVoteAndRemoveOldOnes(votes:Votes, votes_:Votes, new_opn:OperationNumber, new_vote:Vote, log_truncation_point:OperationNumber) -> bool
    {
        &&& forall |opn: OperationNumber| votes_.contains_key(opn) <==> opn >= log_truncation_point && (votes.contains_key(opn) || opn == new_opn)
        &&& forall |opn: OperationNumber| votes_.contains_key(opn) ==> votes_[opn] == (if opn == new_opn {new_vote} else {votes[opn]})
    }

    pub open spec fn LAcceptorInit(a:LAcceptor, c:LReplicaConstants) -> bool
    {
        &&& a.constants == c 
        &&& a.max_bal == Ballot{seqno:0,proposer_id:0}
        &&& a.votes == Map::<OperationNumber, Vote>::empty()
        &&& a.last_checkpointed_operation.len() == c.all.config.replica_ids.len()
        &&& (forall |idx:int| 0 <= idx < a.last_checkpointed_operation.len() ==> a.last_checkpointed_operation[idx] == 0)
        &&& a.log_truncation_point == 0
    }

    /* 
    An example Dafny spec code in IronFleet, what you need to do is for each spec fn here, 
    find the coorsponding predicate in IronFleet code, and translate it to Verus.

    predicate LAcceptorProcess1a(
        s:LAcceptor, 
        s':LAcceptor, 
        inp:RslPacket, 
        sent_packets:seq<RslPacket>
    )
        requires inp.msg.RslMessage_1a?
    {
        var m := inp.msg;
        if inp.src in s.constants.all.config.replica_ids 
            && BalLt(s.max_bal, m.bal_1a) 
            && LReplicaConstantsValid(s.constants) then
        && sent_packets == [ LPacket(inp.src, s.constants.all.config.replica_ids[s.constants.my_index],
                                    RslMessage_1b(m.bal_1a, s.log_truncation_point, s.votes)) ]
        && s' == s.(max_bal := m.bal_1a)
        else
        s' == s && sent_packets == []
    }
    */

    pub open spec fn LAcceptorProcess1a(
        s: LAcceptor, 
        s_: LAcceptor, 
        inp: RslPacket, 
        sent_packets: Seq<RslPacket>
    ) -> bool
        recommends
            inp.msg is RslMessage1a,
    {
        let m = inp.msg;
        let bal = inp.msg->bal_1a;
        if s.constants.all.config.replica_ids.contains(inp.src) 
            && BalLt(s.max_bal, bal) 
            && LReplicaConstantsValid(s.constants)
        {
            &&& sent_packets == seq![
                RslPacket {
                    src: s.constants.all.config.replica_ids.index(s.constants.my_index),
                    dst: inp.src,
                    msg: RslMessage::RslMessage1b {
                        bal_1b: bal,
                        log_truncation_point: s.log_truncation_point,
                        votes: s.votes,
                    }
                }
            ]
            &&& s_ == LAcceptor {
                constants: s.constants,
                max_bal: bal,
                votes: s.votes,
                last_checkpointed_operation: s.last_checkpointed_operation,
                log_truncation_point: s.log_truncation_point,
            }
        } else {
            &&& s_ == s
            &&& sent_packets == Seq::<RslPacket>::empty()
        }
    }

    pub open spec fn LAcceptorProcess2a(
        s: LAcceptor, 
        s_: LAcceptor, 
        inp: RslPacket, 
        sent_packets: Seq<RslPacket>
    ) -> bool
        recommends
            inp.msg is RslMessage2a,
            s.constants.all.config.replica_ids.contains(inp.src),
            BalLeq(s.max_bal, inp.msg->bal_2a),
            LeqUpperBound(inp.msg->opn_2a, s.constants.all.params.max_integer_val)
    {
        let m = inp.msg;
        let new_log_truncation_point = if inp.msg->opn_2a - s.constants.all.params.max_log_length + 1 > s.log_truncation_point 
                                                                                    {inp.msg->opn_2a - s.constants.all.params.max_log_length + 1}
                                                                                    else {s.log_truncation_point};
        &&& LBroadcastToEveryone(s.constants.all.config, 
                                s.constants.my_index, 
                                RslMessage::RslMessage2b {
                                    bal_2b: m->bal_2a,
                                    opn_2b: m->opn_2a,
                                    val_2b: m->val_2a
                                },
                                sent_packets)
        &&& s_.max_bal == m->bal_2a
        &&& s_.log_truncation_point == new_log_truncation_point
        &&& if s.log_truncation_point <= inp.msg->opn_2a {LAddVoteAndRemoveOldOnes(s.votes, s_.votes, m->opn_2a, Vote{max_value_bal: m->bal_2a, max_val: m->val_2a}, new_log_truncation_point)}
                                else {s_.votes == s.votes}
        &&& s_.constants == s.constants
        &&& s_.last_checkpointed_operation == s.last_checkpointed_operation

    }

    pub open spec fn LAcceptorProcessHeartbeat(
        s: LAcceptor, 
        s_: LAcceptor, 
        inp: RslPacket
    ) -> bool
        recommends 
            inp.msg is RslMessageHeartbeat
    {
        if s.constants.all.config.replica_ids.contains(inp.src) {
            let sender_index = GetReplicaIndex(inp.src, s.constants.all.config);
            let msg = inp.msg;
            if 0 <= sender_index < s.last_checkpointed_operation.len() && (msg->opn_ckpt > s.last_checkpointed_operation[sender_index]) {
                s_.last_checkpointed_operation == s.last_checkpointed_operation.update(sender_index, msg->opn_ckpt)
                && s_.constants == s.constants
                && s_.max_bal == s.max_bal
                && s_.votes == s.votes
                && s_.log_truncation_point == s.log_truncation_point
            } else {
                s_ == s
            }
        } else {
            s_ == s
        }
    }

    pub open spec fn LAcceptorTruncateLog(
        s: LAcceptor, 
        s_: LAcceptor, 
        opn: OperationNumber
    ) -> bool
    {
        if opn <= s.log_truncation_point {
            s_ == s
        }else{
            RemoveVotesBeforeLogTruncationPoint(s.votes, s_.votes, opn)
            && s_ == LAcceptor{
                log_truncation_point: opn,
                votes: s_.votes,
                ..s
            }
        }
    }
}