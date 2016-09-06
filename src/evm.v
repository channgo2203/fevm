(*=============================================
 The Ethereum Virtual Machine
 =============================================*)


Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrfun ssrbool eqtype ssrnat seq fintype finfun tuple zmodp.

Require Import bitsrep bitsops cursor pmap reader writer mem stack storage instr program state ere.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(*= EVM Exception *)
Inductive EVMException :=
| BreakPointHit
| BadInstruction
| BadJumpDestination
| OutOfGas
| OutOfStack
| StackUnderflow.

(*=EVM *)
Record EVMachine :=
  mkEVMachine {
      m_ere : EREnvironment;
      m_evmstate : EVMState;
      m_storage : Storage
    }.

