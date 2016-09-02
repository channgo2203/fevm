(*=============================================================================
 Instruction syntax and semantics
 
 Execution of an instruction will make the current EVM state and the environment 
 (contract storage, ...) to next state and environment.
 ============================================================================*)


Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrfun ssrbool eqtype ssrnat seq fintype tuple zmodp.

Require Import bitsrep bitsprops bitsops bitsopsprops mem storage stack instr.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.


(*-------------------------------------------------------------------------------
 Stop and arithmetic operations.
 -------------------------------------------------------------------------------*)

