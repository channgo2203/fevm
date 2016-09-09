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
| OutOfStack              (* e.g. peek an item when the stack is empty *)
| StackUnderflow
| StackOverflow
| BadFormProgram
| OutOfRange.             (* e.g. get a byte code at a position beyon the program bytecode *)
(*=End *)
