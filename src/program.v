(*=====================================================================
 A program is represented as a list of BYTE.
 =====================================================================*)

From mathcomp Require Import all_ssreflect.
Require Import bitsops bitsrep instr.

Require Import listhelp.

(*=Program *)
Definition Program := list BYTE.
(*=End *)

(* BYTE to OpCode *)
Definition BYTEToOpCode (b : BYTE) : Instr :=
  let n := toNat (b : BYTE) in
  fromNatToInstr n.


(* Get BYTE at postion [pc], counting from 0 *)
Definition getCodeAt (pc : nat) (pro : Program) : option BYTE :=
  if (nth_ok n pro (#0 : BYTE)) then
    Some (nth n pro (#0 : BYTE))
  else
    None.
           
  
(* Unit test *)
Compute (BYTEToOpCode (#243 : BYTE)).



	
