use super::types_i::COperationNumber;
use builtin::*;
use builtin_macros::*;
use std::collections::HashMap;
use std::result;
use vstd::{map::*, prelude::*, seq::*};

use crate::common::collections::{count_matches::*, maps::*, vecs::*};
use crate::implementation::RSL::types_i::CBalLt;

use crate::common::{collections::maps::*, native::io_s::EndPoint};
use crate::implementation::common::{generic_refinement::*, upper_bound_i::*};
use crate::implementation::RSL::{
    cbroadcast::*, cconfiguration::*, cconstants::*, cmessage::*, types_i::*,
};
use crate::protocol::RSL::{acceptor::*, environment::*, message::*, types::*};

verus! {

    // Datatype for CAcceptor
    #[derive(Clone)]
    pub struct CAcceptor {
        pub constants: CReplicaConstants,
        pub max_bal: CBallot,
        pub votes: CVotes,
        pub last_checkpointed_operation: Vec<COperationNumber>,
        pub log_truncation_point: COperationNumber,
    }

    impl CAcceptor{
        pub open spec fn abstractable(self) -> bool
        {
            &&& self.constants.abstractable()
            &&& self.max_bal.abstractable()
            &&& cvotes_is_abstractable(self.votes)
            &&& (forall |i:int| 0 <= i < self.last_checkpointed_operation.len() ==> COperationNumberIsAbstractable(self.last_checkpointed_operation[i]))
            &&& COperationNumberIsAbstractable(self.log_truncation_point)
        }

        // Predicate to check if CAcceptor is valid
        pub open spec fn valid(self) -> bool {
            &&& self.abstractable()
            &&& self.constants.valid()
            &&& self.max_bal.valid()
            &&& cvotes_is_valid(self.votes)
            &&& (forall |i:int| 0 <= i < self.last_checkpointed_operation.len() ==> COperationNumberIsValid(self.last_checkpointed_operation[i]))
            &&& COperationNumberIsValid(self.log_truncation_point)
            &&& self.last_checkpointed_operation.len() == self.constants.all.config.replica_ids.len()
        }

        // Function to abstractify CAcceptor to LAcceptor
        pub open spec fn view(self) -> LAcceptor
            recommends self.abstractable()
        {
            LAcceptor {
                constants: self.constants.view(),
                max_bal: self.max_bal.view(),
                votes: abstractify_cvotes(self.votes),
                last_checkpointed_operation:self.last_checkpointed_operation@.map(|i,c:COperationNumber| AbstractifyCOperationNumberToOperationNumber(c)),
                log_truncation_point: AbstractifyCOperationNumberToOperationNumber(self.log_truncation_point),
            }
        }

        // #[verifier(external_body)]
        pub fn CIsLogTruncationPointValid(log_truncation_point: COperationNumber, last_checkpointed_operation: Vec<COperationNumber>, config: CConfiguration) -> (isValid :bool)
            requires
                COperationNumberIsValid(log_truncation_point),
                forall|i:int| 0<=i<=last_checkpointed_operation.len() | last_checkpointed_operation[i] as usize ==> COperationNumberIsValid(last_checkpointed_operation[i]),
                config.valid()
            ensures
                isValid == IsLogTruncationPointValid(AbstractifyCOperationNumberToOperationNumber(log_truncation_point),
                last_checkpointed_operation@.map(|i,c:COperationNumber| AbstractifyCOperationNumberToOperationNumber(c)),
                config.view())
        {

        }

        // #[verifier(external_body)]
        pub fn CRemoveVotesBeforeLogTruncationPoint(votes: CVotes, log_truncation_point: COperationNumber) -> (cvotes:CVotes)
            requires
                cvotes_is_valid(votes),
                COperationNumberIsValid(log_truncation_point),
            ensures
            cvotes_is_valid(cvotes) && RemoveVotesBeforeLogTruncationPoint(abstractify_cvotes(cvotes), abstractify_cvotes(votes), AbstractifyCOperationNumberToOperationNumber(log_truncation_point))
        {

        }

        // #[verifier(external_body)]
        pub fn CAddVoteAndRemoveOldOnes(votes: CVotes, new_opn: COperationNumber, new_vote: CVote, log_truncation_point: COperationNumber) -> (cvotes_2:CVotes)
            requires
                cvotes_is_valid(votes),
                COperationNumberIsValid(new_opn),
                new_vote.valid(),
                COperationNumberIsValid(log_truncation_point),
            ensures
                cvotes_is_valid(cvotes_2) && LAddVoteAndRemoveOldOnes(abstractify_cvotes(votes), abstractify_cvotes(cvotes_2), AbstractifyCOperationNumberToOperationNumber(new_opn), new_vote.view(), AbstractifyCOperationNumberToOperationNumber(log_truncation_point))
        {

        }


        pub fn CAcceptorInit(c: CReplicaConstants) -> (rc:Self)
            requires c.valid()
            ensures
                rc.valid(),
                LAcceptorInit(
                    rc@, /* used to convert the implementation type to protocol type */
                    c@
                ) /* refinement condition */
        {
            let t2 = CBallot{
                seqno: 0,
                proposer_id: 0,
            };
            let t3: HashMap<COperationNumber,CVote> = HashMap::new();
    
            let len = c.all.config.replica_ids.len();
            let mut t4: Vec<u64> = Vec::new();
            let mut i = 0;
            while i < len
                invariant
                    i <= len,
                    t4.len() == i,
                    forall |j:int| 0 <= j < i ==> t4[j] == 0,
            {
                t4.push(0);
                i = i + 1;
            }
    
            assert(t4.len() == len);
            assert(forall |idx:int| 0 <= idx < t4.len() ==> t4[idx] == 0);
    
            let t5 = 0;
    
            let s = CAcceptor{constants:c, max_bal:t2, votes:t3, last_checkpointed_operation:t4, log_truncation_point:t5};
    
            let ghost ss = s@;
            let ghost sc = c@;
    
            assert(ss.constants == sc);
            assert(ss.max_bal == Ballot{seqno:0,proposer_id:0});
            assert(ss.votes == Map::<OperationNumber, Vote>::empty());
            assert(ss.last_checkpointed_operation.len() == sc.all.config.replica_ids.len());
            assert(forall |idx:int| 0 <= idx < ss.last_checkpointed_operation.len() ==> ss.last_checkpointed_operation[idx] == 0);
            assert(ss.log_truncation_point == 0);
    
            s
        }

        // #[verifier(external_body)]
        pub fn CAcceptorProcess1a(&mut self, inp: CPacket) -> (sent: OutboundPackets)
            requires
                old(self).valid(),
                inp.valid(),
                inp.msg is CMessage1a
            ensures
                self.valid(),
                sent.valid(),
                LAcceptorProcess1a(old(self)@, self@, inp@, sent@) /* this is the refinement obligation */
        {

        }



        // #[verifier(external_body)]
        pub fn CAcceptorProcess2a(&mut self, inp:CPacket) -> (sent:OutboundPackets)
            requires
                old(self).valid(),
                inp.valid(),
                inp.msg is CMessage2a,
            ensures
                self.valid(),
                LAcceptorProcess2a(old(self)@, self@, inp@, sent@)
        {

        }


        // #[verifier(external_body)]
        pub fn CAcceptorProcessHeartbeat(&mut self, inp: CPacket)
            requires
                old(self).valid(),
                inp.valid(),
                inp.msg is CMessageHeartbeat,
            ensures
                self.valid(),
                LAcceptorProcessHeartbeat(old(self)@, self@, inp@)
        {

        }

        // #[verifier(external_body)]
        pub fn CAcceptorTruncateLog(&mut self, opn: COperationNumber)
            requires
                old(self).valid(),
                COperationNumberIsValid(opn)
            ensures
                self.valid(),
                LAcceptorTruncateLog(old(self)@, self@, AbstractifyCOperationNumberToOperationNumber(opn))
        {

        }

    }
}
