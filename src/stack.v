(*=====================================================================
    Model for the EVM stack

    Each item on stack is a EVMWORD - 256-bit.
 *====================================================================*)


Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrfun ssrbool eqtype ssrnat seq fintype finfun.

Require Import bitsrep bitsops.

Require Import listhelp.

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
  
  [pushARRAY] pushes an abitrary number of bytes. 
 ---------------------------------------------------------------------*)

Definition pushBYTE (s : Stack) (b : BYTE) : option Stack :=
  (* Zero extension of [b] to EVMWORD size *)
  if (length s) < maxSize then
    Some ((BYTEtoEVMWORD b)::s)
  else None.

Definition pushWORD (s : Stack) (w : WORD) : option Stack :=
  if (length s) < maxSize then
    Some ((WORDtoEVMWORD w)::s)
  else None.

Definition pushEVMWORD (s : Stack) (evmw : EVMWORD) : option Stack :=
  if (length s) < maxSize then
    Some (evmw::s)
  else None.
