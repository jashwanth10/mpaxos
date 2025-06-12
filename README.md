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
```shell
scons --verus-path="$VERUS_PATH"
```

This should run verus verification and create .dlls/.so in a bin/ folder for the C# files, and at the root of the project for Rust files. To only run the build without verification use `--no-verify`.


### Running

#### IronRSL

#### Generate Certs

Each IronRSL host has a unique public key as an identifier. Generate these with the CreateIronServiceCerts dll.

```shell
dotnet bin/CreateIronServiceCerts.dll outputdir=certs name=MyCounter type=IronRSL addr1=127.0.0.1 port1=4001 addr2=127.0.0.1 port2=4002 addr3=127.0.0.1 port3=4003
```

#### Running the IronRSLservers

Run these lines in separate terminals to run the 3 servers.

```shell
dotnet bin/IronRSLServer.dll certs/MyCounter.IronRSL.service.txt certs/MyCounter.IronRSL.server1.private.txt
dotnet bin/IronRSLServer.dll certs/MyCounter.IronRSL.service.txt certs/MyCounter.IronRSL.server2.private.txt
dotnet bin/IronRSLServer.dll certs/MyCounter.IronRSL.service.txt certs/MyCounter.IronRSL.server3.private.txt
```

# Code borrowed from IronKV

Some of the code in [IronKV](https://github.com/verus-lang/verified-ironkv) has been directly used:

- NetClient code (src/common/framework/native/io_s.rs)
  - Depends on the verus_extra code as well: (src/verus_extra/...)
- C# code (slightly modified to use Lock)
- Binding to C# code (src/lib.rs)
- The common marshalling library (src/implementation/common/marshalling.rs)
