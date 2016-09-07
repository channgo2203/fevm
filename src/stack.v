(*=====================================================================
    Model for the EVM stack

    Each item on stack is a EVMWORD - 256-bit.
 =====================================================================*)


Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrfun ssrbool eqtype ssrnat seq fintype tuple zmodp.

Require Import bitsrep bitsops.
Require Import List.
Import ListNotations.
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

Definition pushBytes (m : nat) (s : Stack) (bytes : m.-tuple BYTE) : Stack :=
  let p := @fromBytes (rev bytes) in
  (lowWithZeroExtendToEVMWORD p)::s.

(*--------------------------------------------------------------------
 Pop EVMWORD, application on top element, truncation
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


(*---------------------------------------------------------------------
 Exchange operations.
 Exchange 1st and nth stack items. Items are counted from 1.
 ---------------------------------------------------------------------*)

(* separate [s] into two stacks: from top item to nth item 
   and the rest *)

Definition nth_separate (n : nat) (s : Stack) : Stack * Stack :=
 ((firstn n s), (skipn n s)).


Definition exchange (n : nat) (s : Stack) : Stack :=
  if n is _.+1 then
    let fs := (nth_separate (n-1) s).1 in
    let ss := (nth_separate (n-1) s).2 in
    match fs with
      | nil => s
      | h::t => match ss with
                  | nil => s
                  | h1::t1 => (h1::t) ++ (h::t1)
                end
    end
  else s.


(*--------------------------------------------------------------------
 Duplication operations.
 Duplicate the nth item and push on the top of the stack.
 --------------------------------------------------------------------*)
Definition duplicate (n : nat) (s : Stack) : Stack :=
  if (nth_ok (n-1) s (#0 : EVMWORD)) then
    (nth (n-1) s (#0 : EVMWORD))::s
  else s.


(*-------------------------------------------------------------------
 Arithmetic operations.
 -------------------------------------------------------------------*)
Definition add2top (s : Stack) : option Stack :=
  match s with
    | nil => None
    | _::nil => None
    | x1::x2::t => Some ((addB x1 x2)::t)
  end.

Definition mul2top (s : Stack) : option Stack :=
  match s with
    | nil => None
    | _::nil => None
    | x1::x2::t => Some ((mulB x1 x2)::t)
  end.

Definition sub2top (s : Stack) : option Stack :=
  match s with
    | nil => None
    | _::nil => None
    | x1::x2::t => Some ((subB x1 x2)::t)
  end.

Definition div2top (s : Stack) : option Stack :=
  match s with
    | nil => None
    | _::nil => None
    | x1::x2::t => match (toNat x2) with
                      | 0 => Some ((#0:EVMWORD)::t)
                      | _ => Some ((# (Nat.div (toNat x1) (toNat x2)) : EVMWORD)::t)
                              
                   end
  end.

(*--------------------------------------------------------------------
 Comparison and bitwise logic operations.
 --------------------------------------------------------------------*)
Definition lt2top (s : Stack) : option Stack :=
  match s with
    | nil => None
    | _::nil => None
    | x1::x2::t => if (ltB x1 x2) then Some ((#1 : EVMWORD)::t)
                   else Some ((#0 : EVMWORD)::t)
  end.

Definition gt2top (s : Stack) : option Stack :=
  match s with
    | nil => None
    | _::nil => None
    | x1::x2::t => if (ltB x2 x1) then Some ((#1 : EVMWORD)::t)
                   else Some ((#0 : EVMWORD)::t)
  end.

Definition isZero (s : Stack) : option Stack :=
  match s with
    | nil => None
    | x::t => if (isZeroB x) then Some ((#1 : EVMWORD)::t)
              else Some ((#0 : EVMWORD)::t)
  end.



(*--------------------------------------------------------------------
 Stack layout to string.
 --------------------------------------------------------------------*)
Require Import Coq.Strings.String.
Import Ascii.

Definition stackToString (s : Stack) :=
  fold_left (fun x (y : EVMWORD) => (x ++ "; " ++ toHex y)%string) s ""%string.

(*---------------------------------------------------------------------
 Unit test
 ---------------------------------------------------------------------*)
Example s := (pushEVMWORD (pushEVMWORD (pushEVMWORD (pushEVMWORD (pushEVMWORD (initialStack) (#1:EVMWORD)) (#2:EVMWORD)) (#3:EVMWORD)) (#4:EVMWORD)) (#5:EVMWORD)).

Compute (stackToString s).

Compute (stackToString (nth_separate 3 s).1).
Compute (stackToString (nth_separate 3 s).2).

Compute (stackToString (exchange 3 s)).
Compute (stackToString (duplicate 6 s)).