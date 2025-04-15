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
        
    }

    pub open spec fn LAddVoteAndRemoveOldOnes(votes:Votes, votes_:Votes, new_opn:OperationNumber, new_vote:Vote, log_truncation_point:OperationNumber) -> bool
    {
       
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
        
    }

    pub open spec fn LAcceptorProcessHeartbeat(
        s: LAcceptor, 
        s_: LAcceptor, 
        inp: RslPacket
    ) -> bool
        recommends 
            inp.msg is RslMessageHeartbeat
    {
        
    }

    pub open spec fn LAcceptorTruncateLog(
        s: LAcceptor, 
        s_: LAcceptor, 
        opn: OperationNumber
    ) -> bool
    {
        
    }
}