use builtin::*;
use builtin_macros::*;
use vstd::{map::*, modes::*, prelude::*, seq::*, seq_lib::*, *};
use vstd::{set::*, set_lib::*};
use std::collections::*;
use crate::protocol::RSL::types::*;
use crate::protocol::RSL::message::*;
use crate::protocol::RSL::broadcast::*;
use crate::protocol::RSL::environment::*;
use crate::implementation::common::generic_refinement::*;
use crate::implementation::RSL::types_i::*;
use crate::implementation::RSL::cmessage::*;
use crate::implementation::RSL::cconfiguration::*;
use crate::common::framework::environment_s::*;
use crate::common::native::io_s::*;
use crate::implementation::RSL::appinterface::*;
use crate::services::RSL::app_state_machine::*;

use super::cconfiguration::CConfiguration;

verus!{
    pub enum CBroadcast {
        CBroadcast{
            src: EndPoint,
            dsts: Vec<EndPoint>,
            msg:CMessage,
        },
        CBroadcastNop{},
    }

    impl CBroadcast{
        pub open spec fn abstractable(self) -> bool 
        {
            match self {
                CBroadcast::CBroadcast{src, dsts, msg} => 
                    self->src.abstractable() && (forall |i:int| 0 <= i < self->dsts.len() ==> self->dsts[i].abstractable()) && self->msg.abstractable(),
                CBroadcast::CBroadcastNop{} => true
            }
        }

        pub open spec fn valid(self) -> bool 
        {
            &&& self.abstractable()
            &&& match self {
                CBroadcast::CBroadcast{src, dsts, msg} => 
                    self->src.valid_public_key() && (forall |i:int| 0 <= i < self->dsts.len() ==> self->dsts[i].valid_public_key()) && self->msg.valid(),
                CBroadcast::CBroadcastNop{} => true
            }
        }

        

        pub open spec fn view(self) -> Seq<RslPacket>
            recommends self.abstractable()
        {
            match self {
                CBroadcast::CBroadcast{src, dsts, msg} => Self::BuildLBroadcast(
                    self->src@,
                    self->dsts@.map(|i, e:EndPoint| e@),
                    self->msg@,
                ),
                CBroadcast::CBroadcastNop{} => Seq::<RslPacket>::empty(),
            }
        }

        #[verifier(external_body)]
        pub open spec fn BuildLBroadcast(src: AbstractEndPoint, dsts: Seq<AbstractEndPoint>, m: RslMessage) -> (res:Seq<RslPacket>)
        // ensures
        //     res.len() ==  dsts.len(),
        //     (forall |i: int| 0<=dsts.len()<dsts.len() ==> res[i] == LPacket{dst: dsts[i],src:src, msg:m})
            decreases dsts.len()
        {
            if dsts.len() == 0 {Seq::empty()}
            else {seq![LPacket{dst: dsts[0],src: src,msg: m}] + Self::BuildLBroadcast(src, dsts.skip(1), m)}
        }

        #[verifier(external_body)]
        pub fn BuildBroadcastToEveryone(config:CConfiguration, my_index: u64, msg: CMessage) -> (res:Self)
        requires 
            config.valid(),
            ReplicaIndexValid(my_index, config),
            msg.abstractable(),
            // msg.marshallable()
        ensures
            res.valid(),
            res.abstractable(),
            ({
                let packets = OutboundPackets::Broadcast { broadcast: res };
                packets.OutboundPacketsHasCorrectSrc(config.replica_ids@[my_index as int])
            }),
            LBroadcastToEveryone(config@, my_index as int, msg@, res@)
        {
            if my_index < config.replica_ids.len() as u64 {
                CBroadcast::CBroadcast { src: config.replica_ids[my_index as usize].clone(), dsts: config.replica_ids, msg: msg }
            }
            else{
                CBroadcast::CBroadcastNop{}
            }
        }
    }

    #[verifier(external_body)]
    pub proof fn lemma_BuildBroadcast_ensures(src:AbstractEndPoint, dsts:Seq<AbstractEndPoint>, m:RslMessage)
        ensures 
            ({
                let b = CBroadcast::BuildLBroadcast(src, dsts, m);
                &&& b.len() == dsts.len()
                &&& (forall |i:int| 0 <= i < dsts.len() ==> CBroadcast::BuildLBroadcast(src, dsts, m)[i] == LPacket{dst:dsts[i], src:src, msg:m})
            })
        decreases dsts.len()
    {
        if dsts.len() == 0 {
            let b = CBroadcast::BuildLBroadcast(src, dsts, m);
            assert(b.len() == 0);
            assert(forall |i:int| 0 <= i < dsts.len() ==> CBroadcast::BuildLBroadcast(src, dsts, m)[i] == LPacket{dst:dsts[i], src:src, msg:m});
        } else {
            lemma_BuildBroadcast_ensures(src, dsts.drop_first(), m);

            let b = CBroadcast::BuildLBroadcast(src, dsts, m);
            let b_rest = CBroadcast::BuildLBroadcast(src, dsts.drop_first(), m);
            assert(b == seq![LPacket{dst: dsts[0], src: src, msg: m}] + b_rest);
        }
    }


    pub enum OutboundPackets {
        Broadcast{
            broadcast:CBroadcast,
        },
        OutboundPacket{
            p:Option<CPacket>,
        },
        PacketSequence{
            s:Vec<CPacket>,
        }
    }

    impl OutboundPackets{
        pub open spec fn abstractable(self) -> bool 
        {
            match self {
                OutboundPackets::Broadcast{broadcast} => self->broadcast.abstractable(),
                OutboundPackets::OutboundPacket{p} => 
                    match self->p{
                        Some(p_val) => p_val.abstractable(),
                        None => true,
                    },
                OutboundPackets::PacketSequence{s} => (forall |i:int| 0 <= i < self->s.len() ==> self->s[i].abstractable()),
            }
        }

        pub open spec fn valid(self) -> bool 
        {
            &&& self.abstractable()
            &&& match self {
                OutboundPackets::Broadcast{broadcast} => self->broadcast.valid(),
                OutboundPackets::OutboundPacket{p} => 
                    match self->p{
                        Some(p_val) => p_val.valid(),
                        None => true,
                    },
                OutboundPackets::PacketSequence{s} => (forall |i:int| 0 <= i < self->s.len() ==> self->s[i].valid()),
            }
        }

        pub open spec fn view(self) -> Seq<RslPacket>
            recommends self.abstractable()
        {
            match self {
                OutboundPackets::Broadcast{broadcast} => self->broadcast@,
                OutboundPackets::OutboundPacket{p} => 
                    match self->p{
                        Some(p_val) => seq![p_val@],
                        None => Seq::<RslPacket>::empty(),
                    },
                OutboundPackets::PacketSequence{s} => self->s@.map(|i, p:CPacket| p@),
            }
        }

        pub open spec fn OutboundPacketsHasCorrectSrc(self, me:EndPoint) -> bool 
        {
            match self {
                OutboundPackets::Broadcast{broadcast} => 
                    match self->broadcast {
                        CBroadcast::CBroadcast{src, dsts, msg} => src == me,
                        CBroadcast::CBroadcastNop{} => true,
                    }
                OutboundPackets::OutboundPacket{p} => 
                    match self->p{
                        Some(p_val) => p_val.src == me,
                        None => true,
                    },
                OutboundPackets::PacketSequence{s} => (forall |i:int| 0 <= i < self->s.len() ==> self->s[i].src == me),
            }
        }
    }
}