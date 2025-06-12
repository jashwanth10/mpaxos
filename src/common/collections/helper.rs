use builtin::*;
use builtin_macros::*;
use std::collections::*;
use vstd::prelude::*;
use vstd::seq::*;
use vstd::view::*;

verus! {
    #[verifier(external_body)]
    pub fn contains_vec<T>(vec: &Vec<T>, sender: &T) -> (res: bool)
        where T: Eq + Clone + View,
        ensures
            res == vec@.map(|i, t:T| t@).contains(sender@),
    {
        vec.contains(sender)
    }

    #[verifier(external_body)]
    pub fn get_cloned<T>(t: &T) -> (res: T)
        where T: Clone + View 
        ensures
            res@==t@
    {
        t.clone()
    }
}
