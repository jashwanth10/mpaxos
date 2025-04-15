use builtin::*;
use builtin_macros::*;
use vstd::{map::*, modes::*, prelude::*, seq::*, seq_lib::*, *};
use vstd::{set::*, set_lib::*};
use crate::protocol::RSL::distributed_system::*;
use crate::protocol::RSL::constants::*;
use crate::protocol::RSL::types::*;
use crate::protocol::RSL::environment::*;
use crate::protocol::RSL::acceptor::*;
use crate::protocol::RSL::executor::*;
use crate::protocol::RSL::replica::*;
use crate::protocol::RSL::common_proof::assumptions::*;
use crate::protocol::RSL::common_proof::constants::*;

use crate::common::logic::temporal_s::*;
use crate::common::logic::heuristics_i::*;
use crate::common::framework::environment_s::*;
use crate::common::framework::environment_s::LEnvStep;
use crate::common::native::io_s::*;
use crate::common::collections::maps2::*;

verus!{
    #[verifier::external_body]
    pub proof fn lemma_ActionThatSendsPacketIsActionOfSource(
        ps:RslState,
        ps_:RslState,
        p:RslPacket
    ) -> (rc:(int,Seq<RslIo>))
    requires ps.constants.config.replica_ids.contains(p.src),
             ps_.environment.sentPackets.contains(p),
             !ps.environment.sentPackets.contains(p),
             RslNext(ps, ps_),
    ensures 0 <= rc.0 < ps.constants.config.replica_ids.len(),
            0 <= rc.0 < ps_.constants.config.replica_ids.len(),
            p.src == ps.constants.config.replica_ids[rc.0],
            RslNextOneReplica(ps, ps_, rc.0, rc.1),
            rc.1.contains(LIoOp::Send{s:p}),
    {
        assert(ps.environment.nextStep is LEnvStepHostIos);
        assume(ps.environment.nextStep->ios.contains(LIoOp::Send{s:p}));
        let (idx, ios) = choose |idx:int, ios:Seq<RslIo>| RslNextOneReplica(ps, ps_, idx, ios) && ios.contains(LIoOp::Send{s:p});
        assert(RslNextOneReplica(ps, ps_, idx, ios));
        assert(0 <= idx < ps.constants.config.replica_ids.len());
        (idx, ios)
    }

    #[verifier::external_body]
    pub proof fn lemma_ActionThatSends2aIsMaybeNominateValueAndSend2a(
        ps:RslState,
        ps_:RslState,
        p:RslPacket
    ) -> (
        rc:(int,Seq<RslIo>)
    )
        requires ps.constants.config.replica_ids.contains(p.src),
                p.msg is RslMessage2a,
                ps_.environment.sentPackets.contains(p),
                ps.environment.sentPackets.contains(p),
                RslNext(ps, ps_),
        ensures 0 <= rc.0 < ps.constants.config.replica_ids.len(),
                0 <= rc.0 < ps_.constants.config.replica_ids.len(),
                p.src == ps.constants.config.replica_ids[rc.0],
                RslNextOneReplica(ps, ps_, rc.0, rc.1),
                rc.1.contains(LIoOp::Send{s:p}),
                SpontaneousIos(rc.1, 1),
                LReplicaNextReadClockMaybeNominateValueAndSend2a(ps.replicas[rc.0].replica, ps_.replicas[rc.0].replica,
                                                                  SpontaneousClock(rc.1), ExtractSentPacketsFromIos(rc.1)),
    {
        assert(ps.environment.nextStep is LEnvStepHostIos);
        assert(ps.environment.nextStep->ios.contains(LIoOp::Send{s:p}));
        let (idx, ios) = choose |idx:int, ios:Seq<RslIo>| RslNextOneReplica(ps, ps_, idx, ios) && ios.contains(LIoOp::Send{s:p});
        let nextActionIndex = ps.replicas[idx].nextActionIndex;
        if nextActionIndex != 3
        {
          assert(false);
        }
        (idx, ios)
    }

    #[verifier::external_body]
    pub proof fn lemma_ActionThatSends1bIsProcess1a(
        ps:RslState,
        ps_:RslState,
        p:RslPacket
    ) -> (
        rc:(int,Seq<RslIo>)
    )
        requires ps.constants.config.replica_ids.contains(p.src),
                p.msg is RslMessage1b,
                ps_.environment.sentPackets.contains(p),
                !ps.environment.sentPackets.contains(p),
                RslNext(ps, ps_),
        ensures 0 <= rc.0 < ps.constants.config.replica_ids.len(),
                0 <= rc.0 < ps_.constants.config.replica_ids.len(),
                p.src == ps.constants.config.replica_ids[rc.0],
                RslNextOneReplica(ps, ps_, rc.0, rc.1),
                rc.1.len() > 0,
                rc.1[0] is Receive,
                rc.1[0]->r.msg is RslMessage1a,
                rc.1.contains(LIoOp::Send{s:p}),
                LReplicaNextProcessPacketWithoutReadingClock(ps.replicas[rc.0].replica, ps_.replicas[rc.0].replica, rc.1),
                LAcceptorProcess1a(ps.replicas[rc.0].replica.acceptor, ps_.replicas[rc.0].replica.acceptor, rc.1[0]->r, seq![p]),
    {
        assert(ps.environment.nextStep is LEnvStepHostIos);
        assert(ps.environment.nextStep->ios.contains(LIoOp::Send{s:p}));
        let (idx, ios) = choose |idx:int, ios:Seq<RslIo>| RslNextOneReplica(ps, ps_, idx, ios) && ios.contains(LIoOp::Send{s:p});
        (idx, ios)
    }

    #[verifier::external_body]
    pub proof fn lemma_ActionThatSends2bIsProcess2a(
        ps:RslState,
        ps_:RslState,
        p:RslPacket
    ) -> (
        rc:(int,Seq<RslIo>)
    )
        requires ps.constants.config.replica_ids.contains(p.src),
                p.msg is RslMessage2b,
                ps_.environment.sentPackets.contains(p),
                ps.environment.sentPackets.contains(p),
                RslNext(ps, ps_),
        ensures 0 <= rc.0 < ps.constants.config.replica_ids.len(),
                0 <= rc.0 < ps_.constants.config.replica_ids.len(),
                p.src == ps.constants.config.replica_ids[rc.0],
                RslNextOneReplica(ps, ps_, rc.0, rc.1),
                rc.1.len() > 0,
                rc.1[0] is Receive,
                rc.1.contains(LIoOp::Send{s:p}),
                LReplicaNextProcess2a(ps.replicas[rc.0].replica, ps_.replicas[rc.0].replica, rc.1[0]->r, ExtractSentPacketsFromIos(rc.1)),
    {
        assert(ps.environment.nextStep is LEnvStepHostIos);
        assert(ps.environment.nextStep->ios.contains(LIoOp::Send{s:p}));
        let (idx, ios) = choose |idx:int, ios:Seq<RslIo>| RslNextOneReplica(ps, ps_, idx, ios) && ios.contains(LIoOp::Send{s:p});
        (idx, ios)
    }

    #[verifier::external_body]
    pub proof fn lemma_ActionThatSendsAppStateSupplyIsProcessAppStateRequest(
        ps: RslState,
        ps_prime: RslState,
        p: RslPacket
    ) -> (rc:(int, Seq<RslIo>))
        requires
            ps.constants.config.replica_ids.contains(p.src),
            p.msg is RslMessageAppStateSupply,
            ps_prime.environment.sentPackets.contains(p),
            !ps.environment.sentPackets.contains(p),
            RslNext(ps, ps_prime),
        ensures
            ({
                let idx = rc.0;
                let ios = rc.1;
                &&& (0 <= idx < ps.constants.config.replica_ids.len())
                &&& (0 <= idx < ps_prime.constants.config.replica_ids.len())
                &&& p.src == ps.constants.config.replica_ids[idx]
                &&& RslNextOneReplica(ps, ps_prime, idx, ios)
                &&& ios.len() > 0
                &&& ios[0] is Receive
                &&& ios[0]->r.msg is RslMessageAppStateRequest
                &&& ios.contains(LIoOp::Send{s:p})
                &&& LReplicaNextProcessPacketWithoutReadingClock(
                    ps.replicas[idx].replica, ps_prime.replicas[idx].replica, ios
                )
                &&& LExecutorProcessAppStateRequest(
                    ps.replicas[idx].replica.executor, ps_prime.replicas[idx].replica.executor, ios[0]->r, seq![p]
                )
            }),
    {
        assert(ps.environment.nextStep is LEnvStepHostIos);
        assert(ps.environment.nextStep->ios.contains(LIoOp::Send{s:p}));
        let (idx, ios) = choose |idx: int, ios: Seq<RslIo>| 
            RslNextOneReplica(ps, ps_prime, idx, ios) && ios.contains(LIoOp::Send{s:p});
        (idx, ios)
    }
    
}