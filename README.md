# IronFleet Verus
This project is a verus version of IronFleet from SOSP'15. [[paper](https://www.andrew.cmu.edu/user/bparno/papers/ironfleet.pdf), [code](https://github.com/microsoft/Ironclad/tree/main/ironfleet)].

Our goal is to implement and formally verify the Multi-Paxos protocol via refinement, following IronFleet's methodology.

## What is verus?

Verus is a **verification language** (https://verus-lang.github.io/verus/guide/) developed by Microsoft Research, which extends Rust language. It is designed for writing both executable code and formal specifications, supporting:

- A rich specification language (`spec`, `proof`, `ensures`, `requires`, `invariant`)
- SMT-based automatic verification using Z3
- Ghost variables, pure logic functions, and proof-carrying code

It allows programmers to write real code and prove that it satisfies safety, security, or protocol correctness properties—just like Dafny, but with Rust-like syntax and idioms.

## Code Structure
- `csharp` - The client and server written in C#. These call into the Verus code to run the system.
- `src` – The verus code.
   - `common` – Some common libraries can be used to verify distributed systems.
      - `collections` - Useful definitions, lemmas, and methods for dealing with Sets, Maps, Sequences, Vectors.
      - `framework` - This is the trusted framework that forms the core portion of each service's specification. Each service further adds service-specific specifications in src/services.
      - `logic` - Our encoding of TLA in Verus.
      - `native` - Our trusted interface to C# for networking.
   - `implementation` – The implememtation code.
      - `common` - Useful libraries shared across different systems. Includes command-line parsing, generic marshalling and parsing.
      - `lock` - The core implementation for IronLock.
      - `RSL` - The core implementation of IronRSL, each file in this folder has a one-to-one corrsponding relatoinship with spec files in `src/protocol/RSL`. ( You should work here!!! )
   - `protocol` – The concrete protocol specification.
      - `common` - Common files shared by all of our protocols.
      - `lock` - Defines the protocol layer of our Lock service.
      - `RSL` - Defines the protocol layer of Multi-Paxos. (You should work here!!!)
        - `refienemnt_proof` - Proof of safety, prove the protocol refines the specfication in `src/services/RSL`.
        - `common_proof` -  Common proof code for both safety and liveness. (We haven't prove the livenss)
   - `services` – The spec of the single node state machine.
   - `main.rs` -  The main entry.

## What you should do?
This project follows IronFleet's two-level refinement approach for verifying distributed protocols. The architecture is divided into three layers:

Service layer (abstract spec) – ✅ Already provided

Protocol layer (refined distributed protocol spec) – 🧩 Partially provided

Implementation layer (concrete executable code) – 🧩 Partially provided

You will complete the missing parts in the protocol and implementation layers.

Specifically, you will implement and verify:

`acceptor`

`election`

`proposer`

Each missing function already has its signature defined — you only need to fill in the function body and prove your implementation code refines the specifications in protocol layer.


## How to do it?
You can do it in three main steps:

*Step 1: Implement the Protocol Layer*

The protocol layer defines the system behavior in terms of specification functions. These functions are written using `spec fn`, which are non-executable and describe logical behavior only.

- For each missing `spec fn` in `src/protocol/RSL/`, locate its corresponding `predicate` or `function` in the original IronFleet Dafny code.

- Translate the Dafny code into Verus `spec fn`.

- These `spec fn` serve as the reference model to which the implementation must conform.


*Step 2: Implement the Implementation Layer*

The implementation layer contains the executable code for the system. Each  action in protocol layer should be implemented as a Verus `fn`.

- For each `spec fn` you've defined, find the matching `fn` in `src/implementation/RSL/`.

- Implement the logic inside the function to reflect the protocol’s intent.

- Use Verus’s ensures clause to express that the function refines the `spec fn`. (already provided)

*Step 3: Writing Proof Code*

To verify that your implementation satisfies the spec, you need to write proof code.

- Inline proofs: Embedded directly inside the `fn` body using assert statements and ghost variables.

- Standalone proof functions: Written using `proof fn`, which are analogous to `lemma` in Dafny. Use this for complex reasoning or reusable proofs.

Refer to the Verus proof guide for examples:

👉 [Verus Proof Functions Guide](https://verus-lang.github.io/verus/guide/proof_functions.html)

## Building and running Verification

### Requirements

* Verus (We provide the specific version in the `verus` folder, where you can also find the installation documentation)
* rustc (Last build was using rustc - 1.80.1 (3f5fd8dd4 2024-08-06))
* .NET 6.0 SDK (https://dotnet.microsoft.com/download)
* scons (`pip install scons`)
* python 3 (for running scons)

### Run verification
```
cd verus-ironrsl/src
verus main.rs
```

### Build the project
We have not finished it, will be released later.

# Notes

- In protocol layer, you can only use spec types, such as Seq, Map, Set, int, nat.
But in implementation layer, you can only use executable types, such as Vec, HashMap, HashSet, i32, i64, u64, etc. Their relationships are:
   - Seq -> Vec
   - Map -> HashMap
   - Set -> HashSet
   - int -> i32, i64, u64, etc. (I suggest you use u64 in the implementation layer).
- Verus spec functions cannot have any mutable variables or iteration. Any code that depends on iteration in a Dafny (ghost) function needs to be written recursively or in a proof function. However, you can't call proof functions in pre/post-condition clauses.  
- Verus doesn't support adding additional conditions on anything implementing a trait. I'm not sure how to implement the IronFleet structure of having a base, more abstract module and then refining it in each subclass. That's why the clauses from the framework abstract classes are just copied over into the lock functions.
- Verus doesn't support using addition/other operations in a forall clause. For example, trying to state something about two adjacent items in a Dafny function usually looks like:

```
forall i :: 0 <= i < |s| - 1 ==> foo(s[i], s[i+1])
```

This will fail in Verus, and you need to introduce another variable j, with the value for i+1, i.e.

```
forall |i: int| 0 <= i < s.len() - 1 && j == i+1 ==> foo(s[i], s[j])
```

- Verus maps and sets are infinite by default. In Dafny, there are imaps, isets, maps and sets. All verus maps are imaps, and need to be bounded with m.dom().finite() if required.
- Verus has a handy View trait for mapping a concrete type to a ghost type. This is used a lot for the protocol->host implementation. To use it, the struct needs a spec function called view() that returns the ghost type. The shortcut to call the view function is `@`, e.g. host_protocol@ returns an abstract node (The abstract protocol struct).
- Marshalling has a flaw - there's no spec function to check whether something is not deserializable. This makes it hard to assign something like a "CInvalid" message type for non-deserializable message, because I can't prove it's not a valid message. So, these packets are currently just ignored. 

# Code borrowed from IronKV

Some of the code in [IronKV](https://github.com/verus-lang/verified-ironkv) has been directly used:

- NetClient code (src/common/framework/native/io_s.rs)
  - Depends on the verus_extra code as well: (src/verus_extra/...)
- C# code (slightly modified to use Lock)
- Binding to C# code (src/lib.rs)
- The common marshalling library (src/implementation/common/marshalling.rs)
