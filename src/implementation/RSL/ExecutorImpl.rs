use crate::implementation::RSL::types_i::*;
use crate::implementation::RSL::types_i::*;
use crate::implementation::RSL::ExecutorImpl::OutboundPackets::PacketSequence;
use crate::protocol::RSL::state_machine::*;
use crate::protocol::RSL::types::*;
use crate::services::RSL::app_state_machine::*;
use std::collections::HashMap;
// use crate::implementation::RSL::types_i::abstractify_crequestbatch;
// use crate::implementation::RSL::message_i::*;
use crate::implementation::common::generic_refinement::*;
use crate::implementation::common::generic_refinement::*;
use crate::implementation::RSL::appinterface::*;
use crate::implementation::RSL::cbroadcast::*;
use crate::implementation::RSL::cbroadcast::*;
use crate::implementation::RSL::cconstants::*;
use crate::implementation::RSL::cconstants::*;
use crate::implementation::RSL::cmessage::*;
use crate::implementation::RSL::cmessage::*;
use crate::implementation::RSL::CStateMachine::*;
use crate::protocol::RSL::constants::*;
use crate::protocol::RSL::executor::*;
// use crate::implementation::common::native::io_s::*;
// use crate::implementation::RSL::cmessage::OutboundPackets::*;
use crate::implementation::RSL::ExecutorImpl::OutboundPackets::Broadcast;
use crate::services::RSL::app_state_machine::*;
// use services::RSL::app_state_machine::AppState;
// use crate::verus;
use crate::common::native::io_s::EndPoint;
use builtin::*;
use builtin_macros::*;
use vstd::{prelude::*, seq::*, seq_lib::*};

verus! {

    #[derive(Clone)]
pub enum COutstandingOperation {
    COutstandingOpKnown{
        v: CRequestBatch,
        bal: CBallot,
    },
    COutstandingOpUnknown{},
}

impl COutstandingOperation{

    pub open spec fn valid(&self) -> bool {
        match self {
            COutstandingOperation::COutstandingOpKnown{v, bal} => {
                self.abstractable()
                    && crequestbatch_is_valid(*v)
                    && bal.valid()
            }
            COutstandingOperation::COutstandingOpUnknown{} => self.abstractable()
        }
    }

    pub open spec fn abstractable(&self) -> bool {
        match self {
            COutstandingOperation::COutstandingOpKnown{v, bal} => {
                crequestbatch_is_abstractable(*v) && bal.abstractable()
            }
            COutstandingOperation::COutstandingOpUnknown{} => true
        }
    }

    pub open spec fn view(self) -> OutstandingOperation
        recommends
            self.abstractable()
    {
        match self {
            COutstandingOperation::COutstandingOpKnown{v,bal} => {
                OutstandingOperation::OutstandingOpKnown{
                    v: abstractify_crequestbatch(v),
                    // v: abstractify_crequestbatch(v),
                    bal: bal@,
                }
            }
            COutstandingOperation::COutstandingOpUnknown{} => OutstandingOperation::OutstandingOpUnknown{},
        }
    }

}

#[derive(Clone)]
pub struct CExecutor {
    pub constants: CReplicaConstants,
    pub app: CAppState,
    pub ops_complete: u64,
    pub max_bal_reflected: CBallot,
    pub next_op_to_execute: COutstandingOperation,
    pub reply_cache: CReplyCache,
}

impl CExecutor{

    pub open spec fn valid(&self) -> bool {
        self.abstractable()
            && self.constants.valid()
            && CAppStateIsValid(self.app)
            && self.max_bal_reflected.valid()
            && self.next_op_to_execute.valid()
            && creplycache_is_valid(self.reply_cache)
    }

    pub open spec fn abstractable(&self) -> bool {
        self.constants.abstractable()
            && CAppStateIsAbstractable(self.app)
            && self.max_bal_reflected.abstractable()
            && self.next_op_to_execute.abstractable()
            && creplycache_is_abstractable(self.reply_cache)
    }

    pub open spec fn view(&self) -> LExecutor
        recommends
            self.abstractable(){
        let res = LExecutor {
            constants: self.constants.view(),
            // app: AbstractifyCAppStateToAppState(s.app),
            app: self.app,
            ops_complete: self.ops_complete as int,
            max_bal_reflected: self.max_bal_reflected.view(),
            next_op_to_execute: self.next_op_to_execute.view(),
            reply_cache: abstractify_creplycache(self.reply_cache),
        };
        res
    }

    #[verifier(external_body)]
    pub fn CExecutorInit(c: CReplicaConstants) -> (s:Self)
        requires
            c.valid()
        ensures
            s.valid(),
            LExecutorInit(s.view(), c.view())
    {
        CExecutor {
            constants: c,
            app: 0 as u64,
            ops_complete: 0,
            max_bal_reflected: CBallot { seqno: 0, proposer_id: 0 },
            next_op_to_execute: COutstandingOperation::COutstandingOpUnknown{},
            reply_cache: HashMap::new(),
        }
    }

    pub fn CExecutorGetDecision(&mut self, bal: CBallot, opn: COperationNumber, v: CRequestBatch)
    requires
        old(self).valid(),
        bal.valid(),
        COperationNumberIsValid(opn),
        crequestbatch_is_valid(v),
        opn == old(self).ops_complete,
        old(self).next_op_to_execute is COutstandingOpUnknown
        // ({if let COutstandingOperation::COutstandingOpUnknown{} = old(self).next_op_to_execute {true} else {false}})
    ensures
        self.valid(),
        LExecutorGetDecision(old(self)@,
                                self@,
                                bal.view(),
                                // opn,
                                AbstractifyCOperationNumberToOperationNumber(opn),
                                // v@)
                                abstractify_crequestbatch(v))

{
    self.next_op_to_execute = COutstandingOperation::COutstandingOpKnown{v: v, bal: bal};
    // CExecutor {
    //     next_op_to_execute: COutstandingOperation::COutstandingOpKnown{v: v, bal: bal},
    //     ..self
    // }
}

#[verifier(external_body)]
pub fn CGetPacketsFromReplies(me: EndPoint, requests: Vec<CRequest>, replies: Vec<CReply>) -> (cr:Vec<CPacket>)
    requires
        // EndPointIsValid(me),
        //Needs to be checked
        crequestbatch_is_valid(requests),
        forall|i: int| 0 <= i < requests.len() ==> requests[i].valid(),
        forall|i: int| 0 <= i < replies.len() ==> replies[i].valid(),
        // forall|i: int| 0 <= i < requests.len() ==> requests[i].valid(),
        // forall|i: int| 0 <= i < replies.len() ==> replies[i].valid(),
        requests.len() == replies.len()
    ensures
        ({
            let lr = GetPacketsFromReplies(me.view(),
            // AbstractifySeq(requests, CRequest::view),
            requests@.map(|i,x:CRequest| x@),
            replies@.map(|i,x:CReply| x@));
            // AbstractifySeq(replies, CReply::view));
            // && AbstractifySeq(cr, CPacket::view) == lr;
            cr@.map(|i,x: CPacket| x@) == lr
        })
    {
    if requests.len()==0 {
        Vec::new()
    } else {

        let mut res = Self::CGetPacketsFromReplies(me.clone(), requests.clone().split_off(1),replies.clone().split_off(1));
        let x = CPacket{
            dst: requests[0].client.clone(),
            src: me.clone(),
            msg: CMessage::CMessageReply{
                seqno_reply: requests[0].seqno,
                reply: replies[0].reply.clone()
            }
        };
        res.push(x);

        res
    }
}

#[verifier(external_body)]
pub fn CClientsInReplies(replies: Vec<CReply>) -> (m:CReplyCache)
    // requires
    //     ({forall|i: int| 0 <= i < replies.len() ==>
        // if let CReply {client, seqno, reply} = replies[i]{ true } else {false}})
        // && replies[i]

    ensures
        forall|c: EndPoint| m@.contains_key(c) ==> m@[c].client == c,
        forall|c: EndPoint| m@.contains_key(c) ==> (exists|req_idx: int| req_idx < replies.len()
        && replies[req_idx].client == c
        && m@[c] == replies[req_idx]),
        ({
            let lr = LClientsInReplies(replies@.map(|i,x:CReply| x@));
            creplycache_is_valid(m)
            && abstractify_creplycache(m)==lr
        })
{

    let mut r = HashMap::new();
    if replies.len()!=0 {
        // r = CClientsInReplies(replies[1..].to_vec());
        // r.insert(replies[0].client, replies[0]);
    }
    lemma_ReplyCacheLen(r.clone());
    r
}

#[verifier(external_body)]
pub fn CUpdateNewCache(c: CReplyCache, replies: Vec<CReply>) -> (c_prime:CReplyCache)
    requires
        creplycache_is_valid(c),
        forall|i: int| i < replies.len() ==> replies[i].valid()
    ensures
        creplycache_is_valid(c_prime)
        && UpdateNewCache(abstractify_creplycache(c),
        abstractify_creplycache(c_prime),
        replies@.map(|i,x:CReply| x@))
{
    let nc = Self::CClientsInReplies(replies);
    let mut updated_cache = HashMap::new();
    // let x = c.keys().chain(nc.keys()).collect();
    for x in nc.keys() {
        let val:CReply;
        if c.contains_key(&x) {
            val = c.get(&x).unwrap().clone();
        } else {
            val = nc.get(&x).unwrap().clone();
        }
        updated_cache.insert(x.clone(), val);
    }
    // lemma_ReplyCacheLen(updated_cache);
    updated_cache
}

#[verifier(external_body)]
pub fn CExecutorExecute(&mut self) -> (res: OutboundPackets)
    requires
        old(self).valid(),
        old(self).next_op_to_execute is COutstandingOpKnown,
        // match self.next_op_to_execute{ COutstandingOperation::COutstandingOpKnown{v,bal} => {true}
        // COutstandingOperation::COutstandingOpUnknown {  }=>false},
        //Needs to be defined in Impl/common/Upperbound
        // CLtUpperBound(s.ops_complete, s.constants.all.params.max_integer_val),
        old(self).constants.valid()
    ensures
        self.valid(),
        res.valid(),
        LExecutorExecute(old(self)@,
                            self@,
                            res@)
{
    let batch = match self.next_op_to_execute.clone() {
        COutstandingOperation::COutstandingOpKnown{v, bal} => v.clone(),
        COutstandingOperation::COutstandingOpUnknown {  } => vec![]
    };

    let (new_states, replies) = CHandleRequestBatch(self.app, batch.clone());
    let new_state = new_states[new_states.len()-1];

    let clients = Self::CClientsInReplies(replies.clone());

    let x = match self.next_op_to_execute.clone() {
        COutstandingOperation::COutstandingOpKnown { v, bal } => bal,
        COutstandingOperation::COutstandingOpUnknown {  } => CBallot{seqno: 0, proposer_id:0}
    };
    let new_max_bal_reflected = if CBalLeq(&self.max_bal_reflected, &x) {
        x
    } else {
        self.max_bal_reflected
    };

        self.app= new_state.clone();
        self.ops_complete+= 1;
        self.max_bal_reflected= new_max_bal_reflected;
        self.next_op_to_execute= COutstandingOperation::COutstandingOpUnknown{   };
        self.reply_cache= Self::CUpdateNewCache(self.reply_cache.clone(), replies.clone());

    let outbound_packets = PacketSequence{s: Self::CGetPacketsFromReplies(
        self.constants.all.config.replica_ids[self.constants.my_index as usize].clone(),
        batch,
        replies
    )};

    outbound_packets
}

#[verifier(external_body)]
pub fn CExecutorProcessAppStateSupply(
    &mut self,
    inp: CPacket
)
    requires
        old(self).valid(),
        inp.valid(),
        // (if let CMessage::CMessageAppStateSupply{bal_state_supply,
        //     opn_state_supply,
        //     app_state,
        //     reply_cache} = inp.msg{ if opn_state_supply > old(self).ops_complete{true} else {false}} else {false}),
        inp.msg is CMessageAppStateSupply,
        inp.msg->opn_state_supply > old(self).ops_complete,
        (exists |i: int| 0<= i < old(self).constants.all.config.replica_ids.len() ==> old(self).constants.all.config.replica_ids[i] == &inp.src)
    ensures
        //fresh(reply_cache_mutable)
        self.valid(),
        LExecutorProcessAppStateSupply(old(self)@,
        self@,
        inp@)
{
    // let m = inp.msg;
    // let mut res = Self::CExecutorInit(self.constants.clone());
    // // if let CMessage::CMessageAppStateSupply { bal_state_supply, opn_state_supply, app_state, reply_cache } = m {

    //         self.app= m.clone()->app_state;
    //         self.ops_complete= m.clone()->opn_state_supply;
    //         self.max_bal_reflected= m.clone()->bal_state_supply;
    //         self.next_op_to_execute= COutstandingOperation::COutstandingOpUnknown{};
    //         self.reply_cache= m.clone()->reply_cache;
    // // }

    let m = inp.msg.clone();
    match m {
        CMessage::CMessageAppStateSupply {
            bal_state_supply,
            opn_state_supply,
            app_state,
            reply_cache,
        } => {
            self.app = app_state;
            self.ops_complete = opn_state_supply;
            self.max_bal_reflected = bal_state_supply;
            self.next_op_to_execute = COutstandingOperation::COutstandingOpUnknown {};
            self.reply_cache = reply_cache;
        }
        _ => {
            // Unreachable due to precondition: `inp.msg is CMessageAppStateSupply`
        }
}

}

#[verifier(external_body)]
pub fn CExecutorProcessAppStateRequest(
    &mut self,
    inp: CPacket,
    reply_cache: HashMap::<EndPoint, CReply>
) -> (res: OutboundPackets)
    requires
        old(self).valid(),
        inp.valid(),
        // if let CMessage::CMessageAppStateRequest { bal_state_req, opn_state_req } =  inp.msg {
        //      true
        // } else {false},
        inp.msg is CMessageAppStateRequest,
        (exists |i: int| 0<= i < old(self).constants.all.config.replica_ids.len() ==> old(self).constants.all.config.replica_ids[i] == &inp.src)
    ensures
        self.valid(),
        res.valid(),
        LExecutorProcessAppStateRequest(old(self)@, self@,
        inp@,
        res@)
{
    // let m = inp.msg;
    // // if let CMessage::CMessageAppStateRequest { bal_state_req, opn_state_req } = m{
    //     if (CBalLeq(&self.max_bal_reflected, &m.clone()->bal_state_req)
    //     && self.ops_complete >= m.clone()->opn_state_req
    //     && self.constants.clone().valid())
    // {
    //     let outbound_packets = PacketSequence{
    //         s: vec![CPacket{
    //             dst: inp.src,
    //             src: self.constants.all.config.replica_ids[self.constants.my_index as usize].clone(),
    //             msg: CMessage::CMessageAppStateSupply{
    //                 bal_state_supply: self.max_bal_reflected,
    //                 opn_state_supply: self.ops_complete,
    //                 app_state: self.app,
    //                 reply_cache: self.reply_cache.clone(),
    //             }
    //         }]
    //     };
    //     outbound_packets
    // } else {
    //     PacketSequence{s: vec![]}
    // }
    // // }else{
    // //     PacketSequence{s: vec![]}

    // // }

    let m = inp.msg.clone();

    match m {
        CMessage::CMessageAppStateRequest { bal_state_req, opn_state_req } => {
            if CBalLeq(&self.max_bal_reflected, &bal_state_req)
                && self.ops_complete >= opn_state_req
                && self.constants.clone().valid()
            {
                let outbound_packets = PacketSequence {
                    s: vec![CPacket {
                        dst: inp.src,
                        src: self.constants.all.config.replica_ids[self.constants.my_index as usize].clone(),
                        msg: CMessage::CMessageAppStateSupply {
                            bal_state_supply: self.max_bal_reflected,
                            opn_state_supply: self.ops_complete,
                            app_state: self.app,
                            reply_cache: self.reply_cache.clone(),
                        },
                    }],
                };
                outbound_packets
            } else {
                PacketSequence { s: vec![] }
            }
        }
        _ => {
            // Unreachable due to precondition: `inp.msg is CMessageAppStateRequest`
            PacketSequence { s: vec![] }
        }
}


}

#[verifier(external_body)]
pub fn CExecutorProcessStartingPhase2(
    &mut self,
    inp: CPacket
) -> (res: OutboundPackets)
    requires
        old(self).valid(),
        inp.valid(),
        // if let CMessage::CMessageStartingPhase2{
        //     bal_2,
        //     logTruncationPoint_2,
        // } = inp.msg {true} else {false},
        inp.msg is CMessageStartingPhase2
    ensures
        self.valid(),
        res.valid(),
        LExecutorProcessStartingPhase2(old(self)@, self@,
        inp@,
        res@)
    {
        // let mut log_tp = 0;
        // let mut bal = CBallot { seqno: 0, proposer_id: 0 };
        // // if let CMessage::CMessageStartingPhase2{
        // //     bal_2,
        // //     logTruncationPoint_2,
        // // } = inp.msg{
        // //     log_tp = logTruncationPoint_2;
        // //     bal = bal_2;
        // // }
        // log_tp = inp.msg.clone()->logTruncationPoint_2;
        // bal = inp.msg.clone()->bal_2;

        // if self.constants.all.config.replica_ids.contains(&inp.src)
        // && log_tp > self.ops_complete{
        //      OutboundPackets::Broadcast{broadcast: CBroadcast::BuildBroadcastToEveryone(self.constants.all.config.clone(), self.constants.my_index, CMessage::CMessageAppStateRequest{bal_state_req: bal,opn_state_req: log_tp})}
        // }
        //  else {
        // return Broadcast{broadcast: CBroadcast::CBroadcastNop{}};}

            match inp.msg.clone() {
                CMessage::CMessageStartingPhase2 { bal_2, logTruncationPoint_2 } => {
                    let log_tp = logTruncationPoint_2;
                    let bal = bal_2;

                    if self.constants.all.config.replica_ids.contains(&inp.src)
                        && log_tp > self.ops_complete
                    {
                        OutboundPackets::Broadcast {
                            broadcast: CBroadcast::BuildBroadcastToEveryone(
                                self.constants.all.config.clone(),
                                self.constants.my_index,
                                CMessage::CMessageAppStateRequest {
                                    bal_state_req: bal,
                                    opn_state_req: log_tp,
                                },
                            ),
                        }
                    } else {
                        OutboundPackets::Broadcast {
                            broadcast: CBroadcast::CBroadcastNop {},
                        }
                    }
                }
                _ => {
                    // Unreachable due to `inp.msg is CMessageStartingPhase2`
                    OutboundPackets::Broadcast {
                        broadcast: CBroadcast::CBroadcastNop {},
                    }
                }
            }
    }


    #[verifier(external_body)]
    pub fn CExecutorProcessRequest(self,inp: CPacket) -> (res: OutboundPackets)
    requires
        self.valid(),
        inp.valid(),
        // ({
        //  if let CMessage::CMessageRequest { seqno_req, val } = inp.msg {
        //     if self.reply_cache@[inp.src].seqno >= seqno_req {true} else {false}
        //     // if val.seqno >= seqno_req {true} else {false}
        // } else {false}}),
        inp.msg is CMessageRequest,
        inp.msg->seqno_req <= self.reply_cache@[inp.src].seqno,
        self.reply_cache@.contains_key(inp.src),
    ensures
        res.valid(),
        LExecutorProcessRequest(self.view(),
        inp.view(),
        res.view())
    {

    //     let mut seqno = 0;

    //     // if let CMessage::CMessageRequest { seqno_req, val } = inp.msg {seqno = seqno_req;}
    //     seqno = inp.msg->seqno_req;

    //     let condition1 = if let Some(reply) = self.reply_cache.get(&inp.src){ if reply.seqno == seqno {true} else {false}} else {false};

    //     if condition1 && self.constants.clone().valid(){

    //         let r = self.reply_cache.get(&inp.src).unwrap();
    //         let pkt = PacketSequence{s: vec![CPacket{
    //             dst:r.client.clone(),
    //             src:self.constants.all.config.replica_ids[self.constants.my_index as usize].clone(),
    //             msg: CMessage::CMessageReply{
    //                 seqno_reply: r.seqno,
    //                 reply: r.reply.clone()
    //             }
    //         }]}	;
    //         pkt
    //     } else {
    //             OutboundPackets::PacketSequence{s:vec![]}
    // }

    match inp.msg.clone() {
        CMessage::CMessageStartingPhase2 { bal_2, logTruncationPoint_2 } => {
            let log_tp = logTruncationPoint_2;
            let bal = bal_2;

            if self.constants.all.config.replica_ids.contains(&inp.src)
                && log_tp > self.ops_complete
            {
                OutboundPackets::Broadcast {
                    broadcast: CBroadcast::BuildBroadcastToEveryone(
                        self.constants.all.config.clone(),
                        self.constants.my_index,
                        CMessage::CMessageAppStateRequest {
                            bal_state_req: bal,
                            opn_state_req: log_tp,
                        },
                    ),
                }
            } else {
                OutboundPackets::Broadcast {
                    broadcast: CBroadcast::CBroadcastNop {},
                }
            }
        }
        _ => {
            // Unreachable due to `inp.msg is CMessageStartingPhase2`
            OutboundPackets::Broadcast {
                broadcast: CBroadcast::CBroadcastNop {},
            }
        }
    }

}

}

    #[verifier(external_body)]
    pub proof fn lemma_ReplyCacheLen(cache: CReplyCache)
    ensures
        cache.len() < 256
        {

        }

}

// verus!
