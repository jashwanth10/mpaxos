#![allow(unused_imports)]
use std::net;

use builtin::*;
use builtin_macros::*;
use std::collections::*;
use vstd::{modes::*, prelude::*, seq::*, *};

verus! {
    pub open spec fn SeqIsAbstractable<CT>(s:Vec<CT>, AbstractableValue:spec_fn(CT) -> bool) -> bool
    {
        forall |i:int| 0 <= i < s.len() ==> AbstractableValue(s[i])
    }

    pub open spec fn SeqIsValid<CT>(s:Vec<CT>, ValidateValue:spec_fn(CT) -> bool, AbstractableValue:spec_fn(CT) -> bool) -> bool
    {
        forall |i:int| 0 <= i < s.len() ==> AbstractableValue(s[i]) && ValidateValue(s[i])
    }

    pub open spec fn AbstractifySeq<T, CT>(
        s: Vec<CT>,
        RefineValue: spec_fn(CT) -> T,
        AbstractableValue:spec_fn(CT) -> bool
    ) -> Seq<T>
        recommends SeqIsAbstractable(s, AbstractableValue)
        // decreases s.len()
    {
        s@.map(|i, ct:CT| RefineValue(ct))
    }


    pub proof fn lemma_AbstractifySeq_Ensures<T, CT>(s: Vec<CT>, RefineValue: spec_fn(CT) -> T, AbstractableValue:spec_fn(CT) -> bool)
        requires SeqIsAbstractable(s, AbstractableValue)
        ensures
        ({
            let cs = AbstractifySeq(s, RefineValue, AbstractableValue);
            &&& cs.len() == s.len()
            &&& (forall |i:int| 0 <= i < s.len() ==> cs[i] == RefineValue(s[i]))
            &&& (forall |i:T| cs.contains(i) ==> exists |x:int| 0 <= x < s.len() && i == RefineValue(s[x]))
            // &&& (forall |i:CT| #![trigger RefineValue(i)]cs.contains(RefineValue(i)) ==> exists |x:int| 0 <= x < s.len() && i == s[x])
        })
    {
    }


    pub open spec fn SetIsAbstractable<CT>(s:HashSet<CT>, AbstractableValue:spec_fn(CT) -> bool) -> bool
    {
        forall |x:CT| s@.contains(x) ==> AbstractableValue(x)
    }

    pub open spec fn SetIsValid<CT>(s:HashSet<CT>, ValidateValue:spec_fn(CT) -> bool, AbstractableValue:spec_fn(CT) -> bool) -> bool
    {
        forall |x:CT| s@.contains(x) ==> AbstractableValue(x) && ValidateValue(x)
    }

    pub open spec fn AbstractifySet<T, CT>(
        s: HashSet<CT>,
        RefineValue: spec_fn(CT) -> T,
        AbstractableValue:spec_fn(CT) -> bool
    ) -> Set<T>
        recommends SetIsAbstractable(s, AbstractableValue)
    {
        s@.map(|i:CT| RefineValue(i))
    }

    pub proof fn lemma_AbstractifySet_Ensuers<T, CT>(s: HashSet<CT>, RefineValue: spec_fn(CT) -> T, AbstractableValue:spec_fn(CT) -> bool)
        requires
            SetIsAbstractable(s, AbstractableValue),
            (forall |x:CT, y:CT| s@.contains(x) && s@.contains(y) && RefineValue(x) == RefineValue(y) ==> x == y)
        ensures
            ({
                let cs = AbstractifySet(s, RefineValue, AbstractableValue);
                &&& cs.len() == s.len()
                &&& (forall |i:CT| s@.contains(i) ==> cs.contains(RefineValue(i)))
                &&& (forall |y:T| cs.contains(y) <==> exists |x:CT| s@.contains(x) && y == RefineValue(x))
            })
    {
        let ss = s@.map(|i:CT| RefineValue(i));
        let cs = s@;
        lemma_AbstractifySet_SizeUnchange(s@, ss, RefineValue, AbstractableValue);
        assume(s.len() == s@.len());
        assert(cs.len() == ss.len());
    }

    #[verifier::external_body]
    pub proof fn lemma_AbstractifySet_SizeUnchange<T, CT>(s:Set<CT>, ss:Set<T>, RefineValue: spec_fn(CT) -> T, AbstractableValue:spec_fn(CT) -> bool)
        requires
            (forall |x:CT| s.contains(x) ==> AbstractableValue(x)),
            (forall |x:CT, y:CT| s.contains(x) && s.contains(y) && RefineValue(x) == RefineValue(y) ==> x == y),
            (forall |i:CT| s.contains(i) ==> ss.contains(RefineValue(i))),
            (forall |y:T| ss.contains(y) <==> exists |x:CT| s.contains(x) && y == RefineValue(x)),
        ensures
            s.len() == ss.len(),
        decreases s.len()
    {
        if s.len() > 0 {
            assume(exists |x:CT| s.contains(x));
            let x = choose |x:CT| s.contains(x);
            assert(s.contains(x));
            let s_ = s.remove(x);
            let ss_ = ss.remove(RefineValue(x));
            // assert(s_.len() == s.len() - 1);

            assert(s.contains(x));
            assert(!s_.contains(x));
            assert forall |y:CT| s_.contains(y) implies s.contains(y) && y != x by {
                assert(s.contains(y));
                assert(y != x);
            };
            assert forall |y:CT| s.contains(y) && y != x implies s_.contains(y) by {
                assert(s_.contains(y));
            };
            assert(s_.len() == s.len() - 1);

            assert(ss_.len() == ss.len() - 1);
            lemma_AbstractifySet_SizeUnchange(s_, ss_, RefineValue, AbstractableValue);
            assert(s.len() == ss.len());
        }
    }

    // pub proof fn lemma_HashSetView_SizeUnchange<CT: std::cmp::Eq + std::hash::Hash>(s:HashSet<CT>, ss:Set<CT>)
    //     requires
    //         ss == s@,
    //     ensures
    //         s.len() == ss.len()
    // {
    //     assert forall |x:CT| s.contains(x) <==> ss.contains(x) by {
    //         assert(ss.contains(x) == s@.contains(x));
    //     };
    // }



    pub open spec fn MapIsAbstractable<CKT, CVT, KT, VT>(
        m:HashMap<CKT, CVT>,
        RefineKey: spec_fn(CKT) -> KT,
        AbstractableKey:spec_fn(CKT) -> bool,
        RefineValue: spec_fn(CVT) -> VT,
        AbstractableValue:spec_fn(CVT) -> bool,
        ReverseKey: spec_fn(KT) -> CKT,
    ) -> bool
    {
        &&& (forall |ck:CKT| m@.contains_key(ck) ==> AbstractableKey(ck) && AbstractableValue(m@[ck]))
        &&& (forall |ck:CKT| m@.contains_key(ck) ==> ReverseKey(RefineKey(ck)) == ck)
    }

    pub open spec fn MapIsValid<CKT, CVT, KT, VT>(
        m:HashMap<CKT, CVT>,
        RefineKey: spec_fn(CKT) -> KT,
        AbstractableKey:spec_fn(CKT) -> bool,
        ValidateKey:spec_fn(CKT) -> bool,
        RefineValue: spec_fn(CVT) -> VT,
        AbstractableValue:spec_fn(CVT) -> bool,
        ValidateValue:spec_fn(CVT) -> bool,
        ReverseKey: spec_fn(KT) -> CKT,
    ) -> bool
    {
        &&& MapIsAbstractable(m, RefineKey, AbstractableKey, RefineValue, AbstractableValue, ReverseKey)
        &&& (forall |ck:CKT| m@.contains_key(ck) ==> ValidateKey(ck) && ValidateValue(m@[ck]))
    }

    pub open spec fn AbstractifyMap<CKT, CVT, KT, VT>(
        m:HashMap<CKT, CVT>,
        RefineKey: spec_fn(CKT) -> KT,
        AbstractableKey:spec_fn(CKT) -> bool,
        ValidateKey:spec_fn(CKT) -> bool,
        RefineValue: spec_fn(CVT) -> VT,
        AbstractableValue:spec_fn(CVT) -> bool,
        ValidateValue:spec_fn(CVT) -> bool,
        ReverseKey: spec_fn(KT) -> CKT,
    ) -> Map<KT, VT>
        recommends
            MapIsAbstractable(m, RefineKey, AbstractableKey, RefineValue, AbstractableValue, ReverseKey)
    {
        Map::new(
            |k:KT| exists |ck:CKT| m@.contains_key(ck) && RefineKey(ck) == k,
            |k:KT| {
                let ck = choose |ck:CKT| m@.contains_key(ck) && RefineKey(ck) == k;
                RefineValue(m@[ck])
            }
        )
    }

    pub proof fn lemma_AbstractifyMap_Ensuers<CKT, CVT, KT, VT>(
        m:HashMap<CKT, CVT>,
        RefineKey: spec_fn(CKT) -> KT,
        AbstractableKey:spec_fn(CKT) -> bool,
        ValidateKey:spec_fn(CKT) -> bool,
        RefineValue: spec_fn(CVT) -> VT,
        AbstractableValue:spec_fn(CVT) -> bool,
        ValidateValue:spec_fn(CVT) -> bool,
        ReverseKey: spec_fn(KT) -> CKT,
    )
        requires
            MapIsAbstractable(m, RefineKey, AbstractableKey, RefineValue, AbstractableValue, ReverseKey)
        ensures
            ({
                let rm = AbstractifyMap(m, RefineKey, AbstractableKey, ValidateKey, RefineValue, AbstractableValue, ValidateValue, ReverseKey);
                &&& (forall |ck:CKT| m@.contains_key(ck) ==> rm.contains_key(RefineKey(ck)))
                &&& (forall |ck:CKT| m@.contains_key(ck) ==> rm[RefineKey(ck)] == RefineValue(m@[ck]))
                &&& (forall |k:KT| rm.contains_key(k) ==> (exists |ck:CKT| m@.contains_key(ck) && RefineKey(ck) == k))
            })
    {

    }
}
