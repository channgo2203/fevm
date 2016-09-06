(*=========================================================

 EVM state := 
   (gas available,
    program counter,
    memory,
    active number of words in the memory,
    stack content)

 ==========================================================*)


Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrfun ssrbool eqtype ssrnat seq fintype finfun tuple zmodp.

Require Import bitsrep bitsops cursor pmap reader writer mem stack instr program.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(*= EVMState *)
Record EVMState :=
  mkEVMState {
      g : EVMWORD;
      pc : EVMWORD;
      m :> Mem;
      i : EVMWORD;
      s :> Stack}.

(*End *)

               


