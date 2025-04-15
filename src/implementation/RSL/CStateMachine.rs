use builtin::*;
use builtin_macros::*;
use vstd::{prelude::*, seq::*, seq_lib::*};
use crate::protocol::RSL::types::*;
use crate::protocol::RSL::state_machine::*;
use crate::services::RSL::app_state_machine::*;
use crate::implementation::RSL::appinterface::*;
use crate::implementation::RSL::types_i::*;
use crate::implementation::common::generic_refinement::*;

verus! {
pub fn CHandleRequest(state: CAppState, request: CRequest) -> ( result:(CAppState, CReply))
    requires
        CAppStateIsValid(state),
        request.valid()
    ensures 
        AbstractifyCAppStateToAppState(result.0) == HandleRequest(AbstractifyCAppStateToAppState(state), request.view()).0,
        result.1.view() == HandleRequest(AbstractifyCAppStateToAppState(state), request.view()).1
{
    let (new_state, reply) = HandleAppRequest(state, request.request);
    (new_state, CReply { client: request.client, seqno: request.seqno, reply })
}

#[verifier(external_body)]
pub fn CHandleRequestBatchHidden(state: CAppState, batch: CRequestBatch) -> (result:(Vec<CAppState>, Vec<CReply>))
    requires 
        CAppStateIsValid(state),
        crequestbatch_is_valid(batch)
    ensures
        // forall |i: int| 0 <= i < batch.len() ==> matches!(result.1.index(i),CReply),
        result.0.len() == batch.len()+1,
        result.1.len() == batch.len(),
        ({  
            let (lr0, lr1) = HandleRequestBatchHidden(AbstractifyCAppStateToAppState(state), abstractify_crequestbatch(batch));
            &&& forall |i: int| 0 <= i < result.1.len() ==> result.1[i].valid() 
            &&& result.1@.map(|i, x: CReply| x@) == lr1
            &&& result.0@.map(|i, x: CAppState| x@) == lr0
            
            //  (AbstractifySeq(result.0, AbstractifyCAppStateToAppState, CAppStateIsAbstractable), AbstractifySeq(result.1, abstractify_crequestbatch,crequestbatch_is_abstractable)) == (lr0,lr1)
        })
    decreases batch.len()
{
    if batch.len() == 0 {
        let states = vec![state];
        let replies = vec![];
        let ghost s = AbstractifyCAppStateToAppState(state);
        let ghost b = abstractify_crequestbatch(batch);
        let ghost (ss, rs) = HandleRequestBatchHidden(s,b);
        assert(states@.map(|i, x: CAppState| x@)==ss);
        assert(replies@.map(|i, x: CReply| x@)==rs);
        assert(HandleRequestBatchHidden(s,b)==(states@.map(|i, x: CAppState| x@),replies@.map(|i, x: CReply| x@)));
        (states, replies)
    } else {
        let (rest_states, rest_replies) = CHandleRequestBatchHidden(state, batch[0..batch.len()-1].to_vec());
        let (new_state, reply) = HandleAppRequest(*rest_states.last().unwrap(), batch.last().unwrap().request.clone());

        let mut states = rest_states;
        states.push(new_state);
        let mut replies = rest_replies;
        replies.push(CReply{client: batch.last().unwrap().client.clone(), seqno: batch.last().unwrap().seqno, reply: reply});

        let ghost s = AbstractifyCAppStateToAppState(state);
        let ghost b = abstractify_crequestbatch(batch);
        let ghost (rs, rp) = HandleRequestBatchHidden(s, b.take(b.len() - 1));
        let ghost (s1, r) = AppHandleRequest(rs.last(), b.last().request);
        // assert(b.take(b.len() - 1) == abstractify_crequestbatch(batch[0..batch.len()-1].to_vec()));
        
        // let ghost s = AbstractifyCAppStateToAppState(state);
        // let ghost b = abstractify_crequestbatch(batch);
        let ghost (ss_prime, rs_prime) = HandleRequestBatchHidden(s, b);
        assert(states@.map(|i, x: CAppState| x@) == ss_prime);
        assert(replies@.map(|i, x: CReply| x@) == rs_prime);
        assert(
            HandleRequestBatchHidden(AbstractifyCAppStateToAppState(state), abstractify_crequestbatch(batch)) == 
            (states@.map(|i, x: CAppState| x@), replies@.map(|i, x: CReply| x@))
        );
    
        (states, replies)
    }
}

// // Batch request handler with validity proofs
// pub open spec fn CHandleRequestBatch(state: CAppState, batch: CRequestBatch) -> (result:(Vec<CAppState>, Vec<CReply>))
//     requires
//         CAppStateIsValid(state),
//         crequestbatch_is_valid(batch)
//     ensures 
//         result.0.first() == state,
//         result.0.len() == batch.len() + 1,
//         result.1.len() == batch.len(),
//         (forall |i: int| 0 <= i < batch.len() ==> 
//             result.1[i].client == batch[i].client
//             && (result.0[i+1],result.1[i]) == HandleAppRequest(result.0[i],batch[i].request)
//             && result.1[i].client == batch[i].client
//             && result.1[i].seqno == batch[i].seqno),
//         ({
//             let (lr0, lr1) = HandleRequestBatch(
//                 AbstractifyCAppStateToAppState(state),
//                 abstractify_crequestbatch(batch)
//             );
//             let cr0 = result.0;
//             let cr1 = result.1;

//             &&& (forall |i: CAppState| cr0.contains(&i) ==> CAppStateIsValid(i))
//             &&& (forall|i: int| 0<= i < cr1.len() ==> cr1[i].valid())
//             &&& (cr0@.map(|i, x: CAppState| x@),
//             cr1@.map(|i, x: CReply| x@)) == (lr0, lr1)
//         })

// {
//     let (states, replies) = CHandleRequestBatchHidden(state, batch);
//     lemma_CHandleRequestBatchHidden(state, batch, states, replies);
//     (states, replies)
// }

// // Core proof lemma for batch processing
// #[verifier::external_body]
// proof fn lemma_CHandleRequestBatchHidden(
//     state: CAppState, 
//     batch: Vec<CRequest>, 
//     states: Vec<CAppState>, 
//     replies: Vec<CReply>
// )
//     requires 
//         CAppStateIsValid(state),
//         crequestbatch_is_valid(batch),
//         (states, replies) == CHandleRequestBatchHidden(state, batch),
//     ensures
//         states[0] == state,
//         states.len() == batch.len() + 1,
//         replies.len() == batch.len(),
//         forall |i: int| 0 <= i < batch.len() ==> {
//             // replies.index(i).is_CReply() --Not sure why CReply is being checked since it is not an enum
//             && (states[i +1], replies[i].reply) == HandleAppRequest(states[i], batch[i].request)
//             && replies[i].client == batch[i].client
//             && replies[i].seqno == batch[i].seqno
//         },
// {
//     if batch.len() == 0 {
//         assert(states.len() == batch.len() + 1);
//         assert(replies.len() == batch.len());
//         assert(forall |i: int| 0 <=i <batch.len() ==> ((states[i+1],replies[i].reply)==HandleAppRequest(states[i],batch[i].request)))
//     } else {
//         let rest_batch = CHandleRequestBatchHidden(state, batch.take(..batch.len() - 1));
//         let rest_states = rest_batch.0;
//         let AHR_result = HandleAppRequest(*rest_states.last().unwrap(),batch.last().unwrap().request);

//         lemma_CHandleRequestBatchHidden(state, batch.take(..batch.len() - 1).unwrap(), rest_states, rest_batch.1);

//         assert(replies.last().unwrap().reply == AHR_result.1);
//     }
// }

#[verifier(external_body)]
pub fn CHandleRequestBatch(state:CAppState, batch:CRequestBatch) -> (rc:(Vec<CAppState>, Vec<CReply>))
    requires 
        CAppStateIsValid(state),
        crequestbatch_is_valid(batch)
    ensures 
        ({
            let states = rc.0;
            let replies = rc.1;
            let (lr0, lr1) = HandleRequestBatch(AbstractifyCAppStateToAppState(state), abstractify_crequestbatch(batch));
            &&& states[0] == state
            &&& states.len() == batch.len() + 1
            &&& replies.len() == batch.len()
            // &&& (forall |i:int| 0 <= i < batch.len() ==>
            //         replies[i] is CReply
            //         && (states[i+1], replies[i].reply) == HandleAppRequest(states[i], batch[i].request)
            //         && replies[i].client == batch[i].client
            //         && replies[i].seqno == batch[i].seqno
            //     )
            &&& (forall |i:int| 0 <= i < states@.len() ==> CAppStateIsValid(states[i]))
            &&& (forall |i:int| 0 <= i < replies@.len() ==> replies[i].valid())
            &&& states@.map(|i, s:CAppState| AbstractifyCAppStateToAppState(s)) == lr0
            &&& replies@.map(|i, r:CReply| r@) == lr1
        })
{
    let (states, replies) = CHandleRequestBatchHidden(state, batch);
    (states, replies)
}

} // verus!
