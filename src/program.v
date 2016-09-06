(*=====================================================================
 A program is represented as a list of BYTE.
 =====================================================================*)

From mathcomp Require Import all_ssreflect.
Require Import bitsops bitsrep instr instrsyntax.

Require Import listhelp.

(*=Program *)
Definition Program := list BYTE.
(*=End *)

(* BYTE to OpCode *)
Definition BYTEToOpCode (b : BYTE) : Instr :=
  let n := toNat (b : BYTE) in
  fromNatToInstr n.





	
