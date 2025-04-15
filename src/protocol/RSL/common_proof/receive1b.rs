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
use crate::protocol::RSL::common_proof::message2b::*;
use crate::protocol::RSL::common_proof::packet_sending::*;

use crate::common::logic::temporal_s::*;
use crate::common::logic::heuristics_i::*;
use crate::common::framework::environment_s::*;
use crate::common::framework::environment_s::LEnvStep;
use crate::common::native::io_s::*;
use crate::common::collections::maps2::*;

verus!{
    #[verifier::external_body]
    pub proof fn lemma_PacketInReceived1bWasSent(
        b:Behavior<RslState>,
        c:LConstants,
        i:int,
        replica_idx:int,
        p:RslPacket
    )
        requires IsValidBehaviorPrefix(b, c, i),
                0 <= i,
                0 <= replica_idx < b[i].replicas.len(),
                b[i].replicas[replica_idx].replica.proposer.received_1b_packets.contains(p),
        ensures b[i].environment.sentPackets.contains(p),
                c.config.replica_ids.contains(p.src),
        decreases i
    {
        if i == 0
        {
          return;
        }
      
        lemma_ConstantsAllConsistent(b, c, i-1);
        lemma_ConstantsAllConsistent(b, c, i);
        lemma_AssumptionsMakeValidTransition(b, c, i-1);
        let s = b[i-1].replicas[replica_idx].replica.proposer;
        let s_ = b[i].replicas[replica_idx].replica.proposer;
      
        if s.received_1b_packets.contains(p)
        {
          lemma_PacketInReceived1bWasSent(b, c, i-1, replica_idx, p);
          assert(b[i].environment.sentPackets.contains(p));
          return;
        }
      
        let ios = lemma_ActionThatChangesReplicaIsThatReplicasAction(b, c, i-1, replica_idx);
    }
}