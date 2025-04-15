use crate::implementation::common::upper_bound::*;
use crate::implementation::common::upper_bound_i::*;
use crate::implementation::RSL::types_i::*;
use builtin::*;
use builtin_macros::*;
// use crate::implementation::lock::message_i::*;
use crate::implementation::RSL::acceptorimpl::*;
use crate::implementation::RSL::cbroadcast::*;
use crate::implementation::RSL::cconstants::*;
use crate::implementation::RSL::cmessage::*;
use crate::implementation::RSL::learnerimpl::*;
use crate::implementation::RSL::ExecutorImpl::*;
use crate::implementation::RSL::ProposerImpl::*;
use crate::implementation::RSL::ProposerImpl::*;
use crate::protocol::RSL::replica::*;
// use crate::protocol::RSL::types::*;
use crate::protocol::RSL::{
    acceptor::*, constants::*, executor::*, learner::*, message::*, proposer::*, types::*,
};
use vstd::{map::*, map_lib::*, prelude::*, seq::*};

verus! {

#[derive(Clone)]
pub struct CReplica {
    pub constants: CReplicaConstants,
    pub nextHeartbeatTime: u64,
    pub proposer: CProposer,
    pub acceptor: CAcceptor,
    pub learner: CLearner,
    pub executor: CExecutor,
}

impl CReplica{

    pub open spec fn valid(self) -> bool {
        self.abstractable()
        &&
        self.constants.valid()
        &&
        self.proposer.valid()
        &&
        self.acceptor.valid()
        &&
        self.learner.valid()
        &&
        self.executor.valid()
        &&
        self.constants == self.acceptor.constants
    }

    pub open spec fn abstractable(self) -> bool{
        self.constants.abstractable()
        &&
        self.proposer.abstractable()
        &&
        self.acceptor.abstractable()
        &&
        self.learner.abstractable()
        &&
        self.executor.abstractable()
    }


    pub open spec fn view(self) -> LReplica
    recommends
        self.abstractable()
    {
        LReplica{
            constants:self.constants@,
            nextHeartbeatTime:self.nextHeartbeatTime as int,
            proposer:self.proposer@,
            acceptor:self.acceptor@,
            learner:self.learner@,
            executor:self.executor@
        }
    }

    #[verifier(external_body)]
    pub fn CReplicaInit(c: CReplicaConstants) -> (result: Self)
        requires
            c.valid()
        ensures
            result.valid(),
            LReplicaInit(result@,c@)
    {
        CReplica{
            constants: c.clone(),
            nextHeartbeatTime: 0,
            proposer: CProposer::CProposerInit(c.clone()),
            acceptor: CAcceptor::CAcceptorInit(c.clone()),
            learner: CLearner::CLearnerInit(c.clone()),
            executor: CExecutor::CExecutorInit(c.clone())
        }
    }

    #[verifier(external_body)]
    pub fn CReplicaNextProcessInvalid(&mut self, received_packet: CPacket) -> (res: OutboundPackets)
        requires
            old(self).valid(),
            received_packet.valid(),
            if let CMessage::CMessageInvalid{} = received_packet.msg{
                true
            } else {false}
        ensures
            res.valid(),
            LReplicaNextProcessInvalid(old(self)@,
            self@,
            received_packet@,
            res@)
    {
        OutboundPackets::PacketSequence { s: vec![] }
    }

    #[verifier(external_body)]
    pub fn CReplicaNextProcessRequest(&mut self, received_packet: CPacket) -> (res: OutboundPackets)
    requires
        old(self).valid(),
        received_packet.valid(),
        // ({if let CMessage::CMessageRequest { seqno_req, val } = received_packet.msg{true} else {false}})
        received_packet.msg is CMessageRequest
    ensures
        self.valid(),
        Replica_Common_Postconditions(old(self)@,*self, received_packet,res),
        res.valid(),
        LReplicaNextProcessInvalid(old(self)@,
        self@,
        received_packet@,
        res@)
{
    // if self.executor.reply_cache.contains_key(&received_packet.src) && self.executor.reply_cache[&received_packet.src].seqno >= received_packet.msg.clone()->seqno_req{
    //         return self.executor.clone().CExecutorProcessRequest( received_packet);
    //     } else {
    //         self.proposer.CProposerProcessRequest(received_packet);
    //         return OutboundPackets::PacketSequence { s: vec![] };
    //     }
    //     // Lemma Postconditions

    match received_packet.msg.clone() {
        CMessage::CMessageRequest { seqno_req, .. } => {
            if self.executor.reply_cache.contains_key(&received_packet.src)
                && self.executor.reply_cache[&received_packet.src].seqno >= seqno_req
            {
                return self.executor.clone().CExecutorProcessRequest(received_packet);
            } else {
                self.proposer.CProposerProcessRequest(received_packet);
                return OutboundPackets::PacketSequence { s: vec![] };
            }
        }
        _ => OutboundPackets::PacketSequence { s: vec![] } // Shouldn't happen due to precondition
    }

}

#[verifier(external_body)]
pub fn CReplicaNextProcess1a(&mut self, received_packet: CPacket ) -> (res: OutboundPackets)
requires
    old(self).valid(),
    received_packet.valid(),
    // ({if let CMessage::CMessageRequest { seqno_req, val } = received_packet.msg{true} else {false}})
    received_packet.msg is CMessage1a
ensures
    self.valid(),
    Replica_Common_Postconditions(old(self)@,*self, received_packet,res),
    res.valid(),
    LReplicaNextProcess1a(old(self)@,
    self@,
    received_packet@,
    res@)
    {

        let res = self.acceptor.CAcceptorProcess1a(received_packet);
        //Post conditions
        res

    }

#[verifier(external_body)]
pub fn CReplicaNextProcess1b(&mut self, received_packet: CPacket ) -> (res: OutboundPackets)
    requires
        old(self).valid(),
        received_packet.valid(),
        // ({if let CMessage::CMessageRequest { seqno_req, val } = received_packet.msg{true} else {false}})
        received_packet.msg is CMessage1b
    ensures
        self.valid(),
        Replica_Common_Postconditions(old(self)@,*self, received_packet,res),
        res.valid(),
        LReplicaNextProcess1b(old(self)@,
        self@,
        received_packet@,
        res@)
    {

        // let mut samesrc:bool = true;

        // for x in &self.proposer.received_1b_packets{
        //     if x.src == received_packet.src { samesrc = false;}
        // }

        // if self.proposer.constants.all.config.replica_ids.contains(&received_packet.src) && received_packet.msg.clone()->bal_1b == self.proposer.max_ballot_i_sent_1a && self.proposer.current_state == 1 && samesrc{
        //     // self.proposer.CProposerProcess1b(received_packet);
        //     self.acceptor.CAcceptorTruncateLog(received_packet.msg->log_truncation_point);
        //     // Post cond
        //     OutboundPackets::PacketSequence { s: vec![] }
        // } else{
        //     //Post cond
        //     OutboundPackets::PacketSequence { s: vec![] }
        // }

        match received_packet.msg.clone() {
            CMessage::CMessage1b { bal_1b, log_truncation_point, .. } => {
                let mut samesrc = true;
                for x in &self.proposer.received_1b_packets {
                    if x.src == received_packet.src {
                        samesrc = false;
                    }
                }

                if self.proposer.constants.all.config.replica_ids.contains(&received_packet.src)
                    && bal_1b == self.proposer.max_ballot_i_sent_1a
                    && self.proposer.current_state == 1
                    && samesrc
                {
                    self.acceptor.CAcceptorTruncateLog(log_truncation_point);
                }

                OutboundPackets::PacketSequence { s: vec![] }
            }
            _ => OutboundPackets::PacketSequence { s: vec![] } // should be unreachable
        }

    }

#[verifier(external_body)]
pub fn CReplicaNextProcessStartingPhase2(&mut self, received_packet: CPacket ) -> (res: OutboundPackets)
requires
    old(self).valid(),
    received_packet.valid(),
    // ({if let CMessage::CMessageRequest { seqno_req, val } = received_packet.msg{true} else {false}})
    received_packet.msg is CMessageStartingPhase2
ensures
    self.valid(),
    Replica_Common_Postconditions(old(self)@,*self, received_packet,res),
    res.valid(),
    LReplicaNextProcessStartingPhase2(old(self)@,
    self@,
    received_packet@,
    res@)
    {

        let res = self.executor.CExecutorProcessStartingPhase2(received_packet);
        //Post conditions
        res

    }

    #[verifier(external_body)]
    pub fn CReplicaNextProcess2a(&mut self, received_packet: CPacket ) -> (res: OutboundPackets)
    requires
        old(self).valid(),
        received_packet.valid(),
        // ({if let CMessage::CMessageRequest { seqno_req, val } = received_packet.msg{true} else {false}})
        received_packet.msg is CMessage2a
    ensures
        self.valid(),
        Replica_Common_Postconditions(old(self)@,*self, received_packet,res),
        res.valid(),
        LReplicaNextProcess2a(old(self)@,
        self@,
        received_packet@,
        res@)
    {

        // if self.proposer.constants.all.config.replica_ids.contains(&received_packet.src)
        // && CBalLeq(&self.acceptor.max_bal, &received_packet.msg.clone()->bal_2a)
        // && received_packet.msg.clone()->opn_2a <= self.acceptor.constants.all.params.max_integer_val{
        //     let res = self.acceptor.CAcceptorProcess2a(received_packet);
        //     // Post cond
        //     res
        // } else{
        //     //Post cond
        //     OutboundPackets::PacketSequence { s: vec![] }
        // }

        match received_packet.msg.clone() {
            CMessage::CMessage2a { bal_2a, opn_2a, .. } => {
                if self.proposer.constants.all.config.replica_ids.contains(&received_packet.src)
                    && CBalLeq(&self.acceptor.max_bal, &bal_2a)
                    && opn_2a <= self.acceptor.constants.all.params.max_integer_val
                {
                    self.acceptor.CAcceptorProcess2a(received_packet)
                } else {
                    OutboundPackets::PacketSequence { s: vec![] }
                }
            }
            _ => OutboundPackets::PacketSequence { s: vec![] }
        }

    }

    #[verifier(external_body)]
    pub fn CReplicaNextProcess2b(&mut self, received_packet: CPacket ) -> (res: OutboundPackets)
    requires
        old(self).valid(),
        received_packet.valid(),
        // ({if let CMessage::CMessageRequest { seqno_req, val } = received_packet.msg{true} else {false}})
        received_packet.msg is CMessage2b
    ensures
        self.valid(),
        Replica_Common_Postconditions(old(self)@,*self, received_packet,res),
        res.valid(),
        LReplicaNextProcess2b(old(self)@,
        self@,
        received_packet@,
        res@)
    {

        // let opn = received_packet.msg.clone()->opn_2b;

        // if self.executor.ops_complete < opn
        // || (self.executor.ops_complete == opn && self.executor.next_op_to_execute.clone() is COutstandingOpUnknown){
        //     self.learner.CLearnerProcess2b(received_packet);
        //     OutboundPackets::PacketSequence { s: vec![] }
        // }else{
        //     OutboundPackets::PacketSequence { s: vec![] }
        // }

        match received_packet.msg.clone() {
            CMessage::CMessage2b { opn_2b, .. } => {
                if self.executor.ops_complete < opn_2b
                    || (self.executor.ops_complete == opn_2b
                        && self.executor.next_op_to_execute.clone() is COutstandingOpUnknown)
                {
                    self.learner.CLearnerProcess2b(received_packet);
                }

                OutboundPackets::PacketSequence { s: vec![] }
            }
            _ => OutboundPackets::PacketSequence { s: vec![] }
        }

    }

    #[verifier(external_body)]
    pub fn CReplicaNextProcessReply(&mut self, received_packet: CPacket ) -> (res: OutboundPackets)
requires
    old(self).valid(),
    received_packet.valid(),
    // ({if let CMessage::CMessageRequest { seqno_req, val } = received_packet.msg{true} else {false}})
    received_packet.msg is CMessageReply
ensures
    self.valid(),
    Replica_Common_Postconditions(old(self)@,*self, received_packet,res),
    res.valid(),
    LReplicaNextProcessReply(old(self)@,
    self@,
    received_packet@,
    res@)
    {

        OutboundPackets::PacketSequence { s: vec![] }

    }

    #[verifier(external_body)]
    pub fn CReplicaNextProcessAppStateSupply(&mut self, received_packet: CPacket ) -> (res: OutboundPackets)
    requires
        old(self).valid(),
        received_packet.valid(),
        // ({if let CMessage::CMessageRequest { seqno_req, val } = received_packet.msg{true} else {false}})
        received_packet.msg is CMessageAppStateSupply
    ensures
        self.valid(),
        Replica_Common_Postconditions(old(self)@,*self, received_packet,res),
        res.valid(),
        LReplicaNextProcessAppStateSupply(old(self)@,
        self@,
        received_packet@,
        res@)
    {

        // if self.executor.constants.all.config.replica_ids.contains(&received_packet.src) && received_packet.msg.clone()->opn_state_supply > self.executor.ops_complete{
        //     self.learner.CLearnerForgetOperationsBefore(received_packet.msg.clone()->opn_state_supply);
        //     self.executor.CExecutorProcessAppStateSupply(received_packet);
        //     OutboundPackets::PacketSequence { s: vec![] }
        // } else{
        //     OutboundPackets::PacketSequence { s: vec![] }
        // }

        match received_packet.msg.clone() {
            CMessage::CMessageAppStateSupply { opn_state_supply, .. } => {
                if self.executor.constants.all.config.replica_ids.contains(&received_packet.src)
                    && opn_state_supply > self.executor.ops_complete
                {
                    self.learner.CLearnerForgetOperationsBefore(opn_state_supply);
                    self.executor.CExecutorProcessAppStateSupply(received_packet);
                }

                OutboundPackets::PacketSequence { s: vec![] }
            }
            _ => OutboundPackets::PacketSequence { s: vec![] }
        }

    }

    #[verifier(external_body)]
    pub fn CReplicaNextProcessAppStateRequest(&mut self, received_packet: CPacket ) -> (res: OutboundPackets)
requires
    old(self).valid(),
    received_packet.valid(),
    // ({if let CMessage::CMessageRequest { seqno_req, val } = received_packet.msg{true} else {false}})
    received_packet.msg is CMessageAppStateRequest
ensures
    self.valid(),
    Replica_Common_Postconditions(old(self)@,*self, received_packet,res),
    res.valid(),
    LReplicaNextProcessAppStateRequest(old(self)@,
    self@,
    received_packet@,
    res@)
    {

        let res  =self.executor.CExecutorProcessAppStateRequest(received_packet, self.executor.reply_cache.clone());
        res

    }

    #[verifier(external_body)]
    pub fn CReplicaNextProcessHeartbeat(&mut self, received_packet: CPacket ,clock: u64) -> (res: OutboundPackets)
requires
    old(self).valid(),
    received_packet.valid(),
    // ({if let CMessage::CMessageRequest { seqno_req, val } = received_packet.msg{true} else {false}})
    received_packet.msg is CMessageHeartbeat
ensures
    self.valid(),
    Replica_Common_Postconditions(old(self)@,*self, received_packet,res),
    res.valid(),
    LReplicaNextProcessHeartbeat(old(self)@,
    self@,
    received_packet@,
    clock as int,
    res@)
    {

        self.proposer.CProposerProcessHeartbeat(received_packet.clone(), clock);
        self.acceptor.CAcceptorProcessHeartbeat(received_packet);
        OutboundPackets::PacketSequence { s: vec![] }

    }

    #[verifier(external_body)]
    pub fn CReplicaNextSpontaneousMaybeEnterNewViewAndSend1a(&mut self) -> (res: OutboundPackets)
requires
    old(self).valid(),
ensures
    self.valid(),
    Replica_Common_Postconditions_NoPacket(old(self)@,*self,res),
    res.valid(),
    LReplicaNextSpontaneousMaybeEnterNewViewAndSend1a(old(self)@,
    self@,
    res@)
    {

        let res = self.proposer.CProposerMaybeEnterNewViewAndSend1a();
        res

    }

    #[verifier(external_body)]
    pub fn CReplicaNextSpontaneousMaybeEnterPhase2(&mut self) -> (res: OutboundPackets)
requires
    old(self).valid(),
ensures
    self.valid(),
    Replica_Common_Postconditions_NoPacket(old(self)@,*self,res),
    res.valid(),
    LReplicaNextSpontaneousMaybeEnterPhase2(old(self)@,
    self@,
    res@)
    {
        let res = OutboundPackets::PacketSequence { s: vec![] };
        // let res = self.proposer.CProposerMaybeEnterPhase2(self.acceptor.log_truncation_point);
        res

    }

    #[verifier(external_body)]
    pub fn CReplicaNextSpontaneousMaybeMakeDecision(&mut self) -> (res: OutboundPackets)
requires
    old(self).valid(),
ensures
    self.valid(),
    Replica_Common_Postconditions_NoPacket(old(self)@,*self,res),
    res.valid(),
    LReplicaNextSpontaneousMaybeMakeDecision(old(self)@,
    self@,
    res@)
    {

        let opn = self.executor.ops_complete;

        if self.executor.next_op_to_execute.clone() is COutstandingOpUnknown
        && self.learner.unexecuted_learner_state.contains_key(&opn)
        && self.learner.unexecuted_learner_state[&opn].received_2b_message_senders.len() >= self.learner.constants.all.config.CMinQuorumSize(){
            self.executor.CExecutorGetDecision(self.learner.max_ballot_seen, opn, self.learner.unexecuted_learner_state[&opn].candidate_learned_value.clone());
            OutboundPackets::PacketSequence { s: vec![] }
        }else{
            OutboundPackets::PacketSequence { s: vec![] }
        }

    }

    #[verifier(external_body)]
    pub fn CReplicaNextSpontaneousMaybeExecute(&mut self) -> (res: OutboundPackets)
    requires
        old(self).valid(),
    ensures
        self.valid(),
        Replica_Common_Postconditions_NoPacket(old(self)@,*self,res),
        res.valid(),
        LReplicaNextSpontaneousMaybeExecute(old(self)@,
        self@,
        res@)
    {

        // if self.executor.next_op_to_execute.clone() is COutstandingOpKnown
        // && self.executor.ops_complete < self.executor.constants.all.params.max_integer_val
        // && self.executor.constants.clone().valid(){
        //     self.proposer.CProposerResetViewTimerDueToExecution(self.executor.next_op_to_execute.clone()->v);
        //     self.learner.CLearnerForgetDecision(self.executor.ops_complete);
        //     let res = self.executor.CExecutorExecute();
        //     res
        // }else{
        //     OutboundPackets::PacketSequence { s: vec![] }
        // }

        match self.executor.next_op_to_execute.clone() {
            COutstandingOperation::COutstandingOpKnown { v,.. } => {
                if self.executor.ops_complete < self.executor.constants.all.params.max_integer_val
                    && self.executor.constants.clone().valid()
                {
                    self.proposer.CProposerResetViewTimerDueToExecution(v);
                    self.learner.CLearnerForgetDecision(self.executor.ops_complete);
                    self.executor.CExecutorExecute()
                } else {
                    OutboundPackets::PacketSequence { s: vec![] }
                }
            }
            _ => OutboundPackets::PacketSequence { s: vec![] }
        }


    }

#[verifier(external_body)]
pub fn CReplicaNextReadClockMaybeSendHeartbeat(&mut self, clock: u64) -> (res: OutboundPackets)
requires
old(self).valid(),
ensures
self.valid(),
Replica_Common_Postconditions_NoPacket(old(self)@,*self,res),
res.valid(),
LReplicaNextReadClockMaybeSendHeartbeat(old(self)@,
self@,
ClockReading{t: clock as int},
res@)
{

    if clock < self.nextHeartbeatTime{
        OutboundPackets::PacketSequence { s:vec![] }
    }else{
        let t = CUpperBoundedAddition(clock, self.constants.all.params.heartbeat_period, self.constants.all.params.max_integer_val);
        self.nextHeartbeatTime = t;
        OutboundPackets::Broadcast { broadcast: CBroadcast::BuildBroadcastToEveryone(self.constants.all.config.clone(), self.constants.my_index, CMessage::CMessageHeartbeat { bal_heartbeat: self.proposer.election_state.current_view, suspicious: self.proposer.election_state.current_view_suspectors.contains(&self.constants.my_index), opn_ckpt: self.executor.ops_complete }) }
    }

}

#[verifier(external_body)]
pub fn CReplicaNextReadClockCheckForViewTimeout(&mut self, clock: u64) -> (res: OutboundPackets)
requires
    old(self).valid(),
ensures
    self.valid(),
    Replica_Common_Postconditions_NoPacket(old(self)@,*self,res),
    res.valid(),
    LReplicaNextReadClockCheckForViewTimeout(old(self)@,
    self@,
    ClockReading{t: clock as int},
    res@)
{

    self.proposer.CProposerCheckForViewTimeout(clock);
    OutboundPackets::PacketSequence { s: vec![] }

}

#[verifier(external_body)]
pub fn CReplicaNextReadClockCheckForQuorumOfViewSuspicions(&mut self, clock: u64) -> (res: OutboundPackets)
requires
    old(self).valid(),
ensures
    self.valid(),
    Replica_Common_Postconditions_NoPacket(old(self)@,*self,res),
    res.valid(),
    LReplicaNextReadClockCheckForQuorumOfViewSuspicions(old(self)@,
    self@,
    ClockReading{t: clock as int},
    res@)
{

    self.proposer.CProposerCheckForQuorumOfViewSuspicions(clock);
    OutboundPackets::PacketSequence { s: vec![] }

}

#[verifier(external_body)]
pub fn CReplicaNextSpontaneousTruncateLogBasedOnCheckpoints(&mut self) -> (res:OutboundPackets)
    requires
        old(self).valid()
    ensures
        self.valid(),
        Replica_Common_Postconditions_NoPacket(old(self)@,*self,res),
        res.valid(),
        LReplicaNextSpontaneousTruncateLogBasedOnCheckpoints(old(self)@,
        self@,
        res@)
        {

            let mut cond1 = false;
            let mut cond2 = false;
            let mut opn_val: u64 = 0;

            for i in 0..self.acceptor.last_checkpointed_operation.len() {
                let opn = self.acceptor.last_checkpointed_operation[i];
                if CAcceptor::CIsLogTruncationPointValid(opn, self.acceptor.last_checkpointed_operation.clone(), self.constants.all.config.clone()){
                    if opn > self.acceptor.log_truncation_point{
                    opn_val = opn;
                    cond1 = true;
                    break;}
                    else {
                        cond2 = true;}
                }
            }

            if cond1{
                self.acceptor.CAcceptorTruncateLog(opn_val);
                OutboundPackets::Broadcast { broadcast: CBroadcast::CBroadcastNop {  } }
            }

            else if cond2{
                OutboundPackets::Broadcast { broadcast: CBroadcast::CBroadcastNop {  } }
            }

            else{
                OutboundPackets::Broadcast { broadcast: CBroadcast::CBroadcastNop {  } }
            }

        }

#[verifier(external_body)]
pub fn CReplicaNextReadClockMaybeNominateValueAndSend2a(&mut self, clock: u64) -> (res: OutboundPackets)
requires
    old(self).valid(),
ensures
    self.valid(),
    Replica_Common_Postconditions_NoPacket(old(self)@,*self,res),
    res.valid(),
    LReplicaNextReadClockCheckForQuorumOfViewSuspicions(old(self)@,
    self@,
    ClockReading{t: clock as int},
    res@){
        let res = self.proposer.CProposerNominateNewValueAndSend2a(clock, self.acceptor.log_truncation_point);
        res
    }

}

pub open spec fn ConstantsStayConstant_Replica(replica: LReplica, replica_: CReplica) -> bool
    recommends
        replica_.constants.abstractable()
    {

        replica_.constants@ == replica.constants
        && replica.constants == replica.proposer.constants
        && replica.constants == replica.acceptor.constants
        && replica.constants == replica.learner.constants
        && replica.constants == replica.executor.constants
        && replica_.constants == replica_.proposer.constants
        && replica_.constants == replica_.acceptor.constants
        && replica_.constants == replica_.learner.constants
        && replica_.constants == replica_.executor.constants

    }

// Pre-Conditions


pub open spec fn Replica_Common_Preconditions(replica:CReplica, inp:CPacket) ->bool
  {
    replica.valid()
    // && CPacketIsSendable(inp)
    //
    // ^^^ Needs to be implemented in packetparsing:
    // predicate CPacketIsSendable(cpacket:CPacket)
    // {
    //   && CMessageIsMarshallable(cpacket.msg)
    //   && CPacketIsAbstractable(cpacket)
    //   && EndPointIsValidIPV4(cpacket.src)
    // }
  }

  pub open spec fn Replica_Next_Process_Heartbeat_Preconditions(replica:CReplica, inp:CPacket) -> bool
  {
    inp.msg is CMessageHeartbeat
    && replica.valid()
    && inp.valid()
    // && inp.msg.marshallable()
  }

  pub open spec fn Replica_Next_ReadClock_MaybeNominateValueAndSend2a_Preconditions(replica:CReplica) -> bool
  {
    replica.valid()
  }

  pub open spec fn Replica_Next_ReadClock_CheckForViewTimeout_Preconditions(replica:CReplica) -> bool
  {
    replica.valid()
  }

  pub open spec fn Replica_Next_ReadClock_CheckForQuorumOfViewSuspicions_Preconditions(replica:CReplica) -> bool
  {
    replica.valid()
  }

  pub open spec fn Replica_Next_ReadClock_MaybeSendHeartbeat_Preconditions(replica:CReplica) -> bool
  {
    replica.valid()
  }

  pub open spec fn Replica_Next_MaybeEnterNewViewAndSend1a_Preconditions(replica:CReplica) -> bool
  {
    replica.valid()
  }

  pub open spec fn Replica_Next_MaybeEnterPhase2_Preconditions(replica:CReplica) -> bool
  {
    replica.valid()
  }

  pub open spec fn Replica_Next_Spontaneous_TruncateLogBasedOnCheckpoints_Preconditions(replica:CReplica) -> bool
  {
    replica.valid()
  }

  pub open spec fn Replica_Next_Spontaneous_MaybeMakeDecision_Preconditions(replica:CReplica) -> bool
  {
    replica.valid()
  }

  pub open spec fn Replica_Next_Spontaneous_MaybeExecute_Preconditions(replica:CReplica) -> bool
  {
    replica.valid()
  }

  pub open spec fn Replica_Next_Process_Request_Preconditions(replica:CReplica, inp:CPacket) -> bool
  {
    inp.msg is CMessageRequest
    && replica.valid()
    && inp.valid()
    // && inp.msg.marshallable()
  }

  pub open spec fn Replica_Next_Process_1a_Preconditions(replica:CReplica, inp:CPacket) -> bool
  {
    inp.msg is CMessage1a
    && replica.valid()
    && inp.valid()
    // && inp.msg.marshallable()
  }

  pub open spec fn Replica_Next_Process_1b_Preconditions(replica:CReplica, inp:CPacket) -> bool
  {
    inp.msg is CMessage1b
    && replica.valid()
    && inp.valid()
    // && inp.msg.marshallable()
  }

  pub open spec fn Replica_Next_Process_StartingPhase2_Preconditions(replica:CReplica, inp:CPacket) -> bool
  {
    inp.msg is CMessageStartingPhase2
    && replica.valid()
    && inp.valid()
    // && inp.msg.marshallable()
  }

  pub open spec fn Replica_Next_Process_2a_Preconditions(replica:CReplica, inp:CPacket) -> bool
  {
    inp.msg is CMessage2a
    && replica.valid()
    && inp.valid()
    // && inp.msg.marshallable()
  }

  pub open spec fn Replica_Next_Process_2b_Preconditions(replica:CReplica, inp:CPacket) -> bool
  {
    inp.msg is CMessage2b
    && replica.valid()
    && inp.valid()
    // && inp.msg.marshallable()
  }

  pub open spec fn Replica_Next_Process_AppStateRequest_Preconditions(replica:CReplica, inp:CPacket) -> bool
  {
    inp.msg is CMessageAppStateRequest
    && replica.valid()
    && inp.valid()
    // && inp.msg.marshallable()
  }

  pub open spec fn Replica_Next_Process_AppStateSupply_Preconditions(replica:CReplica, inp:CPacket) -> bool
  {

    inp.msg is CMessageAppStateSupply
    && replica.valid()
    && inp.valid()
    // && inp.msg.marshallable()
  }

// // Post-Conditions predicates

pub open spec fn Replica_Common_Postconditions(replica: LReplica, replica_: CReplica, inp: CPacket, packets_sent: OutboundPackets) -> bool {
    replica_.constants.valid()
    // CPacketIsSendable(inp) has to be implemented in packetparsing.rs
    && replica_.abstractable()
    && ConstantsStayConstant_Replica(replica, replica_)
    && replica_.valid()
    && packets_sent.valid()
    && packets_sent.OutboundPacketsHasCorrectSrc(replica_.constants.all.config.replica_ids[replica_.constants.my_index as int])
    && packets_sent.abstractable()
}

pub open spec fn Replica_Common_Postconditions_NoPacket(replica: LReplica, replica_: CReplica, packets_sent: OutboundPackets) -> bool {
    replica_.constants.valid()
    // CPacketIsSendable(inp) has to be implemented in packetparsing.rs
    && replica_.abstractable()
    && ConstantsStayConstant_Replica(replica, replica_)
    && replica_.valid()
    && packets_sent.valid()
    && packets_sent.OutboundPacketsHasCorrectSrc(replica_.constants.all.config.replica_ids[replica_.constants.my_index as int])
    && packets_sent.abstractable()
}

pub open spec fn Replica_Next_Process_AppStateSupply_Postconditions(replica: LReplica, replica_: CReplica, inp: CPacket, packets_sent: OutboundPackets) -> bool {
    inp.abstractable()
    && inp.msg is CMessageAppStateSupply
    && Replica_Common_Postconditions(replica, replica_, inp, packets_sent)
    && LReplicaNextProcessAppStateSupply(
        replica,
        replica_@,
        inp.view(),
        packets_sent.view()
    )
}

pub open spec fn Replica_Next_Process_AppStateRequest_Postconditions(replica: LReplica, replica_: CReplica, inp: CPacket, packets_sent: OutboundPackets) -> bool {
    inp.abstractable()
    && inp.msg is CMessageAppStateRequest
    && Replica_Common_Postconditions(replica, replica_, inp, packets_sent)
    && LReplicaNextProcessAppStateRequest(
        replica,
        replica_@,
        inp.view(),
        packets_sent.view()
    )
}

pub open spec fn Replica_Next_Process_2b_Postconditions(replica: LReplica, replica_: CReplica, inp: CPacket, packets_sent: OutboundPackets) -> bool {
    inp.abstractable()
    && inp.msg is CMessage2b
    && Replica_Common_Postconditions(replica, replica_, inp, packets_sent)
    && LReplicaNextProcess2b(
        replica,
        replica_@,
        inp.view(),
        packets_sent.view()
    )
}

pub open spec fn Replica_Next_Process_2a_Postconditions(replica: LReplica, replica_: CReplica, inp: CPacket, packets_sent: OutboundPackets) -> bool {
    inp.abstractable()
    && inp.msg is CMessage2a
    && Replica_Common_Postconditions(replica, replica_, inp, packets_sent)
    && LReplicaNextProcess2a(
        replica,
        replica_@,
        inp.view(),
        packets_sent.view()
    )
}

// pub open spec fn Replica_Next_Process_2a_Postconditions(replica: LReplica, replica_: CReplica, inp: CPacket, packets_sent: OutboundPackets) -> bool {
//     inp.abstractable()
//     && inp.msg is CMessage2a
//     && Replica_Common_Postconditions(replica, replica_, inp, packets_sent)
//     && LReplicaNextProcess2a(
//         replica,
//         replica_@,
//         inp.view(),
//         packets_sent.view()
//     )
// }

pub open spec fn Replica_Next_Process_StartingPhase2_Postconditions(replica: LReplica, replica_: CReplica, inp: CPacket, packets_sent: OutboundPackets) -> bool {
    inp.abstractable()
    && inp.msg is CMessageStartingPhase2
    && Replica_Common_Postconditions(replica, replica_, inp, packets_sent)
    && LReplicaNextProcessStartingPhase2(
        replica,
        replica_@,
        inp.view(),
        packets_sent.view()
    )
}

pub open spec fn Replica_Next_Process_1b_Postconditions(replica: LReplica, replica_: CReplica, inp: CPacket, packets_sent: OutboundPackets) -> bool {
    inp.abstractable()
    && inp.msg is CMessage1b
    && Replica_Common_Postconditions(replica, replica_, inp, packets_sent)
    && LReplicaNextProcess1b(
        replica,
        replica_@,
        inp.view(),
        packets_sent.view()
    )
}

pub open spec fn Replica_Next_Process_1a_Postconditions(replica: LReplica, replica_: CReplica, inp: CPacket, packets_sent: OutboundPackets) -> bool {
    inp.abstractable()
    && inp.msg is CMessage1a
    && Replica_Common_Postconditions(replica, replica_, inp, packets_sent)
    && LReplicaNextProcess1a(
        replica,
        replica_@,
        inp.view(),
        packets_sent.view()
    )
}

pub open spec fn Replica_Next_Process_Request_Postconditions(replica: LReplica, replica_: CReplica, inp: CPacket, packets_sent: OutboundPackets) -> bool {
    inp.abstractable()
    && inp.msg is CMessageRequest
    && Replica_Common_Postconditions(replica, replica_, inp, packets_sent)
    && LReplicaNextProcessRequest(
        replica,
        replica_@,
        inp.view(),
        packets_sent.view()
    )
}

pub open spec fn Replica_Next_Process_Heartbeat_Postconditions(replica: LReplica, replica_: CReplica, inp: CPacket, clock: u64, packets_sent: OutboundPackets) -> bool {
    inp.abstractable()
    && inp.msg is CMessageHeartbeat
    && Replica_Common_Postconditions(replica, replica_, inp, packets_sent)
    && LReplicaNextProcessHeartbeat(
        replica,
        replica_@,
        inp.view(),
        clock as int,
        packets_sent.view()
    )
}

pub open spec fn Replica_Next_ReadClock_MaybeNominateValueAndSend2a_Postconditions(replica: LReplica, replica_: CReplica, clock: ClockReading, packets_sent: OutboundPackets) -> bool {
    Replica_Common_Postconditions_NoPacket(replica, replica_, packets_sent)
    && LReplicaNextReadClockMaybeNominateValueAndSend2a(replica,
         replica_@,
        clock,
        packets_sent@)
}

pub open spec fn Replica_Next_ReadClock_CheckForViewTimeout_Postconditions(replica: LReplica, replica_: CReplica, clock: ClockReading, packets_sent: OutboundPackets) -> bool {
    Replica_Common_Postconditions_NoPacket(replica, replica_, packets_sent)
    && LReplicaNextReadClockCheckForViewTimeout(replica,
         replica_@,
        clock,
        packets_sent@)
}

pub open spec fn Replica_Next_ReadClock_CheckForQuorumOfViewSuspicions_Postconditions(replica: LReplica, replica_: CReplica, clock: ClockReading, packets_sent: OutboundPackets) -> bool {
    Replica_Common_Postconditions_NoPacket(replica, replica_, packets_sent)
    && LReplicaNextReadClockCheckForQuorumOfViewSuspicions(replica,
         replica_@,
        clock,
        packets_sent@)
}

pub open spec fn Replica_Next_ReadClock_MaybeSendHeartbeat_Postconditions(replica: LReplica, replica_: CReplica, clock: ClockReading, packets_sent: OutboundPackets) -> bool {
    Replica_Common_Postconditions_NoPacket(replica, replica_, packets_sent)
    && LReplicaNextReadClockMaybeSendHeartbeat(replica,
         replica_@,
        clock,
        packets_sent@)
}

pub open spec fn Replica_Next_MaybeEnterNewViewAndSend1a_Postconditions(replica: LReplica, replica_: CReplica, packets_sent: OutboundPackets) -> bool {
    Replica_Common_Postconditions_NoPacket(replica, replica_, packets_sent)
    && LReplicaNextSpontaneousMaybeEnterNewViewAndSend1a(replica,
         replica_@,
        packets_sent@)
}

pub open spec fn Replica_Next_MaybeEnterPhase2_Postconditions(replica: LReplica, replica_: CReplica, packets_sent: OutboundPackets) -> bool {
    Replica_Common_Postconditions_NoPacket(replica, replica_, packets_sent)
    && LReplicaNextSpontaneousMaybeEnterPhase2(replica,
         replica_@,
        packets_sent@)
}

pub open spec fn Replica_Next_Spontaneous_TruncateLogBasedOnCheckpoints_Postconditions(replica: LReplica, replica_: CReplica, clock: ClockReading, packets_sent: OutboundPackets) -> bool {
    Replica_Common_Postconditions_NoPacket(replica, replica_, packets_sent)
    && LReplicaNextSpontaneousTruncateLogBasedOnCheckpoints(replica,
         replica_@,
        packets_sent@)
}

pub open spec fn Replica_Next_Spontaneous_MaybeMakeDecision_Postconditions(replica: LReplica, replica_: CReplica, clock: ClockReading, packets_sent: OutboundPackets) -> bool {
    Replica_Common_Postconditions_NoPacket(replica, replica_, packets_sent)
    && LReplicaNextSpontaneousMaybeMakeDecision(replica,
         replica_@,
        packets_sent@)
}

pub open spec fn Replica_Next_Spontaneous_MaybeExecute_Postconditions(replica: LReplica, replica_: CReplica, clock: ClockReading, packets_sent: OutboundPackets) -> bool {
    Replica_Common_Postconditions_NoPacket(replica, replica_, packets_sent)
    && LReplicaNextSpontaneousMaybeExecute(replica,
         replica_@,
        packets_sent@)
}

} // verus!
