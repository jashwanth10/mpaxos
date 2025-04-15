use builtin::*;
use builtin_macros::*;
use vstd::{map::*, modes::*, prelude::*, seq::*, seq_lib::*, *};
use vstd::{set::*, set_lib::*};
use crate::protocol::RSL::configuration::*;
use crate::protocol::RSL::constants::*;
use crate::protocol::RSL::broadcast::*;
use crate::protocol::RSL::environment::*;
use crate::protocol::RSL::types::*;
use crate::protocol::RSL::types::RequestBatch;
use crate::protocol::RSL::types::Ballot;
// use crate::protocol::RSL::types::AppState;
use crate::protocol::RSL::types::ReplyCache;
use crate::protocol::RSL::message::*;
use crate::protocol::RSL::state_machine::*;
use crate::services::RSL::app_state_machine::*;
use crate::common::framework::environment_s::*;
use crate::common::native::io_s::*;
use crate::protocol::common::upper_bound::*;

verus! {
    pub enum OutstandingOperation {
        OutstandingOpKnown{
            v:RequestBatch,
            bal:Ballot,
        },
        OutstandingOpUnknown{},
    }

    pub struct LExecutor {
        pub constants:LReplicaConstants,
        pub app:AppState,
        pub ops_complete:int,
        pub max_bal_reflected:Ballot,
        pub next_op_to_execute:OutstandingOperation,
        pub reply_cache:ReplyCache,
    }

    pub open spec fn LExecutorInit(s:LExecutor, c:LReplicaConstants) -> bool
    {
        &&& s.constants == c
        &&& s.app == AppInitialize()
        &&& s.ops_complete == 0
        &&& s.max_bal_reflected == Ballot{seqno:0, proposer_id:0}
        &&& s.next_op_to_execute == OutstandingOperation::OutstandingOpUnknown{}
        &&& s.reply_cache == Map::<AbstractEndPoint, Reply>::empty()
    }

    pub open spec fn LExecutorGetDecision(s:LExecutor, s_:LExecutor, bal:Ballot, opn:OperationNumber, v:RequestBatch) -> bool
        recommends
            opn == s.ops_complete,
            s.next_op_to_execute is OutstandingOpUnknown,
    {
        s_ == LExecutor{
            constants:s.constants,
            app:s.app,
            ops_complete:s.ops_complete,
            max_bal_reflected:s.max_bal_reflected,
            next_op_to_execute:OutstandingOperation::OutstandingOpKnown{v:v, bal:bal},
            reply_cache:s.reply_cache
        }
    }

    pub open spec fn GetPacketsFromReplies(me:AbstractEndPoint, requests:Seq<Request>, replies:Seq<Reply>) -> (ps:Seq<RslPacket>)
        recommends
            requests.len() == replies.len(),
            forall |r:Reply| replies.contains(r) ==> r is Reply,
        decreases requests.len()
        // ensures
        //     forall |p:RslPacket| ps.contains(p) ==> p.src == me && p.msg is RslMessageReply
    {
        if requests.len() == 0 {
            Seq::<RslPacket>::empty()
        } else {
            seq![LPacket{
                dst:requests[0].client,
                src:me,
                msg:RslMessage::RslMessageReply{
                    seqno_reply:requests[0].seqno,
                    reply:replies[0].reply,
                }
            }]
            +
            GetPacketsFromReplies(me, requests.drop_first(), replies.drop_first())
        }
    }

    // pub proof fn lemma_GetPacketsFromReplies(me:AbstractEndPoint, requests:Seq<Request>, replies:Seq<Reply>)
    //     requires
    //         requests.len() == replies.len(),
    //         forall |r:Reply| replies.contains(r) ==> r is Reply,
    //     ensures
    //         forall |p: RslPacket| GetPacketsFromReplies(me, requests, replies).contains(p) 
    //             ==> p.src == me && p.msg is RslMessageReply
    // {

    // }

    pub open spec fn LClientsInReplies(replies:Seq<Reply>) -> (r:ReplyCache)
        decreases replies.len()
        // ensures
        //     (forall |c:AbstractEndPoint| r.dom().contains(c) ==> r[c].client == c),
        //     (forall |c:AbstractEndPoint| r.dom().contains(c) ==> exists |req_idx:int| 0 <= req_idx < replies.len()
        //                                                     && replies[req_idx].client == c 
        //                                                     && r[c] == replies[req_idx])
    {
        if replies.len() == 0 {
            Map::<AbstractEndPoint, Reply>::empty()
        } else {
            LClientsInReplies(replies.drop_first()).insert(replies[0].client, replies[0])
        }
    }

    // pub proof fn lemma_LClientsInReplies(replies:Seq<Reply>)
    //     ensures
    //         forall |c:AbstractEndPoint| LClientsInReplies(replies).dom().contains(c) 
    //             ==> LClientsInReplies(replies)[c].client == c,
    //         forall |c:AbstractEndPoint| LClientsInReplies(replies).dom().contains(c) 
    //             ==> exists |req_idx: int| 
    //                 0 <= req_idx < replies.len()
    //                 && replies[req_idx].client == c
    //                 && LClientsInReplies(replies)[c] == replies[req_idx]
    // {

    // }

    pub open spec fn UpdateNewCache(c:ReplyCache, c_:ReplyCache, replies:Seq<Reply>) -> bool
    {
        let nc = LClientsInReplies(replies);
        &&& (forall |client:AbstractEndPoint| c_.contains_key(client) ==> (c.contains_key(client) && c_[client] == c[client])
                                                                        || (exists |req_idx:int| 0 <= req_idx < replies.len()
                                                                            && replies[req_idx].client == client
                                                                            && c_[client] == replies[req_idx]))
        &&& (forall |client:AbstractEndPoint| c_.contains_key(client) <==> (nc.contains_key(client) || c.contains_key(client)))
        &&& (forall |client:AbstractEndPoint| c_.contains_key(client) ==> c_[client] == if c.contains_key(client) {c[client]} else {nc[client]})
        &&& (forall |client:AbstractEndPoint| (nc.contains_key(client) || c.contains_key(client)) ==> c_.contains_key(client)
                                                                                                && c_[client] == if c.contains_key(client) {c[client]} else {nc[client]})
    }

    pub open spec fn LExecutorExecute(
        s:LExecutor, 
        s_:LExecutor, 
        sent_packets:Seq<RslPacket>
    ) -> bool
        recommends
            s.next_op_to_execute is OutstandingOpKnown,
            LtUpperBound(s.ops_complete, s.constants.all.params.max_integer_val),
            LReplicaConstantsValid(s.constants)
    {
        let batch = s.next_op_to_execute->v;
        let temp = HandleRequestBatch(s.app, batch);
        let new_state = temp.0[temp.0.len()-1];
        let replies = temp.1;
        let clients = LClientsInReplies(replies);
        &&& s_.constants == s.constants
        &&& s_.app == s.app
        &&& s_.ops_complete == s.ops_complete 
        &&& s_.max_bal_reflected == if BalLeq(s.max_bal_reflected, s.next_op_to_execute->bal) {s.next_op_to_execute->bal} else {s.max_bal_reflected}
        &&& s_.next_op_to_execute == OutstandingOperation::OutstandingOpUnknown{}
        &&& UpdateNewCache(s.reply_cache, s_.reply_cache, replies)
        &&& sent_packets == GetPacketsFromReplies(s.constants.all.config.replica_ids[s.constants.my_index], batch, replies)  
    }

    pub open spec fn LExecutorProcessAppStateSupply(
        s:LExecutor, 
        s_:LExecutor, 
        inp:RslPacket
    ) -> bool
    {
        let m = inp.msg;
        s_ == LExecutor{
            constants:s.constants,
            app:m->app_state,
            ops_complete:m->opn_state_supply,
            max_bal_reflected:m->bal_state_supply,
            next_op_to_execute:OutstandingOperation::OutstandingOpUnknown{},
            reply_cache:m->reply_cache
        }
    }

    pub open spec fn LExecutorProcessAppStateRequest(
        s:LExecutor, 
        s_:LExecutor, 
        inp:RslPacket, 
        sent_packets:Seq<RslPacket>
    ) -> bool 
        recommends
            inp.msg is RslMessageAppStateRequest,
    {
        let m = inp.msg;
        if s.constants.all.config.replica_ids.contains(inp.src) 
            && BalLeq(s.max_bal_reflected, m->bal_state_req)
            && s.ops_complete >= m->opn_state_req
            && LReplicaConstantsValid(s.constants)
        {
            &&& s_ == s
            &&& sent_packets == seq![LPacket{
                                        dst:inp.src,
                                        src:s.constants.all.config.replica_ids[s.constants.my_index],
                                        msg:RslMessage::RslMessageAppStateSupply{
                                            bal_state_supply:s.max_bal_reflected,
                                            opn_state_supply:s.ops_complete,
                                            app_state:s.app,
                                            reply_cache:s.reply_cache
                                        }
                                    }]
        } else {
            &&& s_ == s
            &&& sent_packets == Seq::<RslPacket>::empty()
        }
    }

    pub open spec fn LExecutorProcessStartingPhase2(
        s:LExecutor, 
        s_:LExecutor, 
        inp:RslPacket, 
        sent_packets:Seq<RslPacket>
    ) -> bool 
    {
        if s.constants.all.config.replica_ids.contains(inp.src) 
            && inp.msg->logTruncationPoint_2 > s.ops_complete
        {
            &&& s_ == s
            &&& LBroadcastToEveryone(s.constants.all.config, s.constants.my_index, 
                                    RslMessage::RslMessageAppStateRequest{
                                        bal_state_req:inp.msg->bal_2, 
                                        opn_state_req:inp.msg->logTruncationPoint_2
                                    },
                                    sent_packets)
        } else {
            &&& s_ == s 
            &&& sent_packets == Seq::<RslPacket>::empty()
        }
    }

    pub open spec fn LExecutorProcessRequest(
        s:LExecutor, 
        inp:RslPacket, 
        sent_packets:Seq<RslPacket>
    ) -> bool 
    {
        if inp.msg->seqno_req == s.reply_cache[inp.src].seqno && LReplicaConstantsValid(s.constants)
        {
            let r = s.reply_cache[inp.src];
            sent_packets == seq![LPacket{
                                dst:r.client,
                                src:s.constants.all.config.replica_ids[s.constants.my_index],
                                msg:RslMessage::RslMessageReply{
                                    seqno_reply:r.seqno,
                                    reply:r.reply
                                }
                            }]
        } else {
            sent_packets == Seq::<RslPacket>::empty()
        }
    }
}