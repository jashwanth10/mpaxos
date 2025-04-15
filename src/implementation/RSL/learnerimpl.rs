use vstd::{map::*, prelude::*, set::*};

use crate::common::collections::maps::*;
use crate::common::framework::abstractservice_s;
use crate::common::native::io_s::*;
use crate::implementation::RSL::cconstants::*;
use crate::implementation::RSL::cmessage::*;
use crate::implementation::RSL::types_i::*;
use crate::protocol::RSL::learner::*;
use std::collections::HashMap;
use std::collections::HashSet;
// #[derive(PartialEq, Eq, Structural)]

/*
    CLearnerProcess2b: I think CLearnerTuple doesn't support clone() and maybe that is why the value moved error?

    CLearnerForgetDecision: Even though the dafny version has used RemoveELt to remove the key, I am using remove() method.

    CLearnerForgetOperationsBefore: again self.unexecuted_learner_state is not letting me assign a value?
*/

verus! {
#[derive(Clone)]
    pub struct CLearner {
        pub constants: CReplicaConstants,
        pub max_ballot_seen: CBallot,
        pub unexecuted_learner_state: CLearnerState,
    }

    impl CLearner
    {
        pub open spec fn abstractable(self) -> bool
        {
            {
                &&& self.constants.abstractable()
                &&& self.max_ballot_seen.abstractable()
                &&& clearnerstate_is_abstractable(self.unexecuted_learner_state)
            }
        }

        pub open spec fn valid(self) -> bool
        {
            {
                &&& self.abstractable()
                &&& self.constants.valid()
                &&& self.max_ballot_seen.valid()
                &&& clearnerstate_is_valid(self.unexecuted_learner_state)
            }
        }

        pub open spec fn view(self) -> LLearner
        recommends self.abstractable()
        {
            LLearner {
                constants: self.constants.view(),
                max_ballot_seen: self.max_ballot_seen.view(),
                unexecuted_learner_state: abstractify_clearnerstate(self.unexecuted_learner_state),
            }
        }

        #[verifier(external_body)]
        pub fn CLearnerInit(c:CReplicaConstants) -> (clearner_init_result:Self)
        requires c.valid()
        ensures
            clearner_init_result.valid(),
            LLearnerInit(clearner_init_result@, c@)

        {
            let t1 = c;
            let t2 = CBallot{seqno:0, proposer_id:0};
            let t3: HashMap<COperationNumber,CLearnerTuple> = HashMap::new();
            let rc = CLearner{
                constants: t1,
                max_ballot_seen: t2,
                unexecuted_learner_state: t3,
            };

            let ghost arc = rc@;
            let ghost ac = c@;
            assert(arc.constants == ac);
            assert(arc.max_ballot_seen == CBallot{seqno:0, proposer_id:0});
            assert(arc.unexecuted_learner_state == HashMap::<COperationNumber, CLearnerTuple>::new());

            rc
        }

        #[verifier(external_body)]
        pub fn CLearnerProcess2b(&mut self, packet: CPacket)
            requires
                old(self).valid(),
                packet.valid(),
                packet.msg is CMessage2b
            ensures
                self.valid(),
                LLearnerProcess2b(old(self)@, self@, packet@)
        {
            // let ghost ss = self@;
            // let ghost p = packet@;
            // let mut m = packet.msg;
            // let opn = m.clone()->opn_2b;

            // if !self.constants.all.config.replica_ids.contains(&packet.src) || CBalLt(&m.clone()->bal_2b, &self.max_ballot_seen) {
            //     // No state changes needed
            // } else {
            //     if CBalLt(&self.max_ballot_seen, &m.clone()->bal_2b) {
            //         let mut m_set : HashSet<EndPoint> = HashSet::new();
            //         m_set.insert(packet.src);
            //         let tup = CLearnerTuple {
            //             received_2b_message_senders: m_set,
            //             candidate_learned_value: m.clone()->val_2b
            //         };
            //         self.max_ballot_seen = m->bal_2b;
            //         self.unexecuted_learner_state.insert(opn, tup);
            //     } else {
            //         if !self.unexecuted_learner_state.contains_key(&opn) {
            //             let mut m_set : HashSet<EndPoint> = HashSet::new();
            //             m_set.insert(packet.src);
            //             let tup = CLearnerTuple {
            //                 received_2b_message_senders: m_set,
            //                 candidate_learned_value: m.clone()->val_2b
            //             };
            //             self.unexecuted_learner_state.insert(opn, tup);
            //         } else {
            //             if self.unexecuted_learner_state[&opn].received_2b_message_senders.contains(&packet.src) {
            //                 // No state changes needed
            //             } else {
            //                 let mut tup = self.unexecuted_learner_state[&opn].clone();
            //                 let mut m_set : HashSet<EndPoint> = HashSet::new();
            //                 m_set.insert(packet.src);
            //                 tup.received_2b_message_senders = m_set;
            //                 self.unexecuted_learner_state.insert(opn, tup);
            //             }
            //         }
            //     }
            // }

            let ghost ss = self@;
            let ghost p = packet@;

            match packet.msg.clone() {
                CMessage::CMessage2b { opn_2b, bal_2b, val_2b } => {
                    let opn = opn_2b;

                    if !self.constants.all.config.replica_ids.contains(&packet.src)
                        || CBalLt(&bal_2b, &self.max_ballot_seen)
                    {
                        // No state changes needed
                    } else {
                        if CBalLt(&self.max_ballot_seen, &bal_2b) {
                            let mut m_set: HashSet<EndPoint> = HashSet::new();
                            m_set.insert(packet.src);
                            let tup = CLearnerTuple {
                                received_2b_message_senders: m_set,
                                candidate_learned_value: val_2b,
                            };
                            self.max_ballot_seen = bal_2b;
                            self.unexecuted_learner_state.insert(opn, tup);
                        } else {
                            if !self.unexecuted_learner_state.contains_key(&opn) {
                                let mut m_set: HashSet<EndPoint> = HashSet::new();
                                m_set.insert(packet.src);
                                let tup = CLearnerTuple {
                                    received_2b_message_senders: m_set,
                                    candidate_learned_value: val_2b,
                                };
                                self.unexecuted_learner_state.insert(opn, tup);
                            } else {
                                if self.unexecuted_learner_state[&opn].received_2b_message_senders.contains(&packet.src) {
                                    // No state changes needed
                                } else {
                                    let mut tup = self.unexecuted_learner_state[&opn].clone();
                                    tup.received_2b_message_senders.insert(packet.src);
                                    self.unexecuted_learner_state.insert(opn, tup);
                                }
                            }
                        }
                    }
                }
                _ => {
                    // unreachable due to precondition: `packet.msg is CMessage2b`
                }
}


        }

        #[verifier(external_body)]
        pub fn CLearnerForgetDecision(&mut self, opn:COperationNumber)
        requires
            old(self).valid(),
            COperationNumberIsValid(opn)
        ensures
            self.valid(),
            LLearnerForgetDecision(old(self)@, self@, AbstractifyCOperationNumberToOperationNumber(opn))
        {
            if self.unexecuted_learner_state.contains_key(&opn) {
                self.unexecuted_learner_state.remove(&opn);
            }
            else {
                // No state changes needed
            }
        }

        #[verifier(external_body)]
        pub fn CLearnerForgetOperationsBefore(&mut self, ops_complete:COperationNumber)
        requires
            old(self).valid(),
            COperationNumberIsValid(ops_complete)
        ensures
            self.valid(),
            LLearnerForgetOperationsBefore(old(self)@, self@, AbstractifyCOperationNumberToOperationNumber(ops_complete))
        {
            let mut new_state: HashMap<COperationNumber, CLearnerTuple> = HashMap::new();
            for (opn,tuple) in &self.unexecuted_learner_state {
                if *opn >= ops_complete {
                    new_state.insert(*opn, tuple.clone());
                }
            }
            self.unexecuted_learner_state = new_state;
        }

    }
}
