(*===================================================================================================================================================================================
 All EVM exceptions.
 ===================================================================================================================================================================================*)

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrfun ssrbool eqtype ssrnat seq fintype finfun tuple zmodp.

Require Import common_definitions.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.



(*=EVM Exception *)
Inductive EVMException :=
| BreakPointHit
| BadInstruction
| BadJumpDestination
| OutOfGas
| StackUnderflow
| StackOverflow
| BadFormProgram
| BadInitialEVM
| OutOfRange.             (* e.g. get a byte code at a position beyon the program bytecode, read or write beyon the memory range *)
(*=End *)


(*----------------------------------------------------------------------------------------------------
 Exception to string
 ----------------------------------------------------------------------------------------------------*)
Require Import Coq.Strings.String.
Import Ascii.

Definition exceptionToString (e : EVMException) :=
  (match e with
     | BreakPointHit => "Break points hit"
     | BadInstruction => "Bad instructions"
     | BadJumpDestination => "Bad destination for jumping"
     | OutOfGas => "Out of gas"
     | StackUnderflow => "Stack under-flow"
     | StackOverflow => "Stack over-flow"
     | BadFormProgram => "Ill-formed program"
     | BadInitialEVM => "Bad initial EVM"
     | OutOfRange => "Out of range"
   end)%string.

