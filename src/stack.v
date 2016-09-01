(*=====================================================================
    Model for the EVM stack

    Each item on stack is a EVMWORD - 256-bit.
 *====================================================================*)


Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrfun ssrbool eqtype ssrnat seq fintype tuple zmodp.

Require Import bitsrep bitsops.


Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* Stack is defined as a list of EVMWORDs *)
(*=Stack *)
Definition Stack := list EVMWORD.

(* Initilize the stack, empty stack *)
Definition initialStack : Stack := nil.

(* Stack size *)
Definition maxSize := 1024.

(* Check the stack is empty *)
Definition isEmpty (s : Stack) : bool :=
  match s with
    | nil => true
    | _ => false
  end.

(* Check the stack is full *)
Definition isFull (s : Stack) : bool :=
  if (length s) >= maxSize then true
  else false.

(* Return a singleton stack *)
Definition  singletonStack (evmw : EVMWORD) : Stack :=
  evmw::nil.

(* Peek the head element *)
Definition peek (s : Stack) : option EVMWORD :=
  match s with
    | nil => None
    | w::_ => Some w
  end.

(* Peek the head element if [s] is not nil, otherwise return [dw] *)
Definition peekdefault (s : Stack) (dw : EVMWORD) : EVMWORD :=
  match s with
    | nil => dw
    | w::_ => w
  end.

(*---------------------------------------------------------------------
  Push BYTE, WORD, DWORD, QWORD, DQWORD, ADDRESS, and EVMWORD.
 
 ---------------------------------------------------------------------*)

Definition pushBYTE (s : Stack) (b : BYTE) :  Stack :=
  (* Zero extension of [b] to EVMWORD size *)
  (BYTEtoEVMWORD b)::s.

Definition pushWORD (s : Stack) (w : WORD) : Stack :=
  (WORDtoEVMWORD w)::s.

Definition pushDWORD (s : Stack) (w : DWORD) : Stack :=
  (DWORDtoEVMWORD w)::s.

Definition pushQWORD (s : Stack) (qw : QWORD) : Stack :=
  (QWORDtoEVMWORD qw)::s.

Definition pushDQWORD (s : Stack) (dqw : DQWORD) : Stack :=
  (DQWORDtoEVMWORD dqw)::s.

Definition pushADDRESS (s : Stack) (addr : ADDRESS) : Stack :=
  (ADDRESStoEVMWORD addr)::s.

Definition pushEVMWORD (s : Stack) (evmw : EVMWORD) : Stack :=
  evmw::s.             


(*--------------------------------------------------------------------
 Pop EVMWORD
 --------------------------------------------------------------------*)
Definition popEVMWORD (s : Stack) : Stack :=
  match s with
    | nil => nil
    | w::t => t
  end.


Definition apply_top (f : EVMWORD -> EVMWORD) (s : Stack) : Stack :=
  match s with
    | nil => nil
    | w::t => (f w)::t
  end.


Definition replace_top (w : EVMWORD) (s : Stack) : Stack :=
  match s with
    | nil => nil
    | h::t => w::t
  end.

(* Truncate [s] into size [n] *)
Fixpoint truncate (n : nat) (s : Stack) : Stack :=
  if n < (length s) then
        match s with
          | _::t => truncate n t
          | _ => nil
        end
  else s.

