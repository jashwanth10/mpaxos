#![allow(unused_imports)]
#![allow(unused_attributes)]
#![verus::trusted]
use builtin::*;
use builtin_macros::*;
use vstd::map::*;
use vstd::modes::*;
use vstd::multiset::*;
use vstd::pervasive::*;
use vstd::seq::*;

use crate::implementation::common::marshalling::Marshalable;

mod common;
mod implementation;
mod protocol;
mod services;
mod verus_extra;

verus! {
    pub proof fn my_proof(x: bool) {
        assert(1 + 1 == 2);
    }

    #[verifier(external_body)]
    pub fn main() {

        // let x = vec![true as u8];
        // let mut y: Vec<u8> = vec![];
        // x.serialize(&mut y);
        // let mut res = false;
        // if let Some(z) = bool::deserialize(&y, 0){
        //     res = true;
        // };
        // let z = vec![false as u8];
        // println!("test");
        // assert!(x == z);

        proof {
            my_proof(true);
        }
    }

}
