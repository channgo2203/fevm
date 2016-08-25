(*Module Type EVMSTATE
End EVMSTATE.
*)
(* state =
	 gas available,
	 program counter,
	 memory,
	 active number of words in the memory,
	 stack content
 *)

Require Import FMapInterface.
Require Import FMapList.
Require Export ZArith.

Definition n : nat := 5.

Compute (n > 0).



