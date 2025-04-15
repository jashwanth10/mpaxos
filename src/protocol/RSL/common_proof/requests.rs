use builtin::*;
use builtin_macros::*;
use vstd::{map::*, modes::*, prelude::*, seq::*, seq_lib::*, *};
use vstd::{set::*, set_lib::*};
use crate::protocol::RSL::distributed_system::*;
use crate::protocol::RSL::constants::*;
use crate::protocol::RSL::types::*;
use crate::protocol::RSL::election::*;
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
    pub proof fn lemma_RemoveAllSatisfiedRequestsInSequenceProducesSubsequence(
        s_:Seq<Request>, 
        s:Seq<Request>, 
        r:Request
    )
        requires s_ == RemoveAllSatisfiedRequestsInSequence(s, r)
        ensures  forall |x:Request| s_.contains(x) ==> s.contains(x)
        decreases s
    {
        if s.len() > 0 && !RequestsMatch(s[0], r)
        {
            lemma_RemoveAllSatisfiedRequestsInSequenceProducesSubsequence(RemoveAllSatisfiedRequestsInSequence(s.drop_first(), r), s.drop_first(), r);
        }
    }

    pub proof fn lemma_RemoveExecutedRequestBatchProducesSubsequence(
        s_:Seq<Request>, 
        s:Seq<Request>, 
        batch:RequestBatch
    )
        requires s_ == RemoveExecutedRequestBatch(s, batch)
        ensures  forall |x:Request| s_.contains(x) ==> s.contains(x)
        decreases batch.len()
    {
        if batch.len() > 0
        {
            let s__ = RemoveAllSatisfiedRequestsInSequence(s, batch[0]);
            lemma_RemoveAllSatisfiedRequestsInSequenceProducesSubsequence(s__, s, batch[0]);
            lemma_RemoveExecutedRequestBatchProducesSubsequence(s_, s__, batch.drop_first());
        }
    }
}