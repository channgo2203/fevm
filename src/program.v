(*=====================================================================
 A program is represented as a list of BYTE.
 =====================================================================*)

From mathcomp Require Import all_ssreflect.
Require Import bitsops bitsrep instr.

Require Import List.
Import ListNotations.
Require Import listhelp.

(*=Program *)
Definition Program := list BYTE.
(*=End *)

(* BYTE to OpCode *)
Definition BYTEToOpCode (b : BYTE) : Instr :=
  let n := toNat (b : BYTE) in
  fromNatToInstr n.


(* Get BYTE at postion [pc], counting from 0 *)
Definition getCodeAt (pc : EVMWORD) (pro : Program) : option BYTE :=
  let n := toNat pc in 
  if (nth_ok n pro (#0 : BYTE)) then
    Some (nth n pro (#0 : BYTE))
  else
    None.
           

(*---------------------------------------------------------------------
 Unit test.
 ---------------------------------------------------------------------*)
Example pro1 : Program := [(#96:BYTE); (#0:BYTE); (#53:BYTE); (#84:BYTE); (#25:BYTE); (#96:BYTE); (#9:BYTE); (#87:BYTE); (#0:BYTE); (#91:BYTE); (#96:BYTE); (#32:BYTE); (#53:BYTE);
                (#96:BYTE); (#0:BYTE); (#53:BYTE); (#85:BYTE)].

Compute (
    let oInstr := getCodeAt (#2:EVMWORD) pro1 in
    match oInstr with
      | Some b => BYTEToOpCode b
      | None => BADINSTR
    end
  ).




	
