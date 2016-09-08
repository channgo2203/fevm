(*============================================================================================
 The Ethereum Runtime Environment (ERE) for the virtual machine EVM.

 ============================================================================================*)

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrfun ssrbool eqtype ssrnat seq fintype finfun tuple zmodp.

Require Import bitsrep bitsops cursor pmap reader writer mem stack instr program.

(*= Log topic *)
Definition LOGTopic n := n.-tuple EVMWORD.

(*=Log entry *)
Record LOGEntry :=
  mkLOGEntry {
      a : ADDRESS;
      t {n} : n.-tuple EVMWORD;
      logm {m} : m.-tuple BYTE
    }.

(*=ERE *)
Record EREnvironment :=
  mkEREnvironment {
      (* address of the contract or contract-to-be that owns the running code *)
      Ia : ADDRESS;
      (* the sender address that sends the message - either equal to origin or a constract *)
      Io : ADDRESS;
      (* Original transactor *)
      Is : ADDRESS;
      (* the price of gas in the transaction *)
      Ip : EVMWORD;
      (* the input data *)
      Id : seq BYTE;
      (* the value *)
      Iv : EVMWORD;
      (* the bytecode *)
      Ib : Program;
      (* the hash of executing code *)
      Ih : EVMWORD;
      
      (* sub-state *)
      As : seq ADDRESS;
      Al : LOGEntry;
      Ar : EVMWORD;

      (* the call depth *)
      Ie : EVMWORD
    }.

