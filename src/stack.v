(*=====================================================================
    Model for the EVM stack

    Each item on stack is a EVMWORD - 256-bit.
 =====================================================================*)


Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrfun ssrbool eqtype ssrnat seq fintype tuple zmodp.

Require Import bitsrep bitsops.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* Stack is defined as a list of EVMWORDs *)
(*=Stack *)
Definition Stack := seq EVMWORD.

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
  if (size s) >= maxSize then
    true
  else
    false.

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

Definition pushBYTE (b : BYTE) (s : Stack) :  Stack :=
  (* Zero extension of [b] to EVMWORD size *)
  (BYTEtoEVMWORD b)::s.

Definition pushWORD (w : WORD) (s : Stack) : Stack :=
  (WORDtoEVMWORD w)::s.

Definition pushDWORD (w : DWORD) (s : Stack) : Stack :=
  (DWORDtoEVMWORD w)::s.

Definition pushQWORD (qw : QWORD) (s : Stack) : Stack :=
  (QWORDtoEVMWORD qw)::s.

Definition pushDQWORD (dqw : DQWORD) (s : Stack) : Stack :=
  (DQWORDtoEVMWORD dqw)::s.

Definition pushADDRESS (addr : ADDRESS) (s : Stack) : Stack :=
  (ADDRESStoEVMWORD addr)::s.

Definition pushEVMWORD (evmw : EVMWORD) (s : Stack) : Stack :=
  evmw::s.

(* Notice that the head of tuple is the least-significant byte *)
Definition pushBytes (m : nat) (bytes : m.-tuple BYTE) (s : Stack) : Stack :=
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
  if n < (size s) then
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
 ((take n s), (drop n s)).


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
  (* if n is out-of-range *)
  if (size s) < n then
    s
  else
    (nth (#0 : EVMWORD) s (n - 1))::s.


(*-------------------------------------------------------------------
 Arithmetic operations.
 -------------------------------------------------------------------*)
Definition add2top (s : Stack) : option Stack :=
  match s with
    | x1::x2::t => Some ((addB x1 x2)::t)
    | _ => None
  end.

Definition mul2top (s : Stack) : option Stack :=
  match s with
    | x1::x2::t => Some ((mulB x1 x2)::t)
    | _ => None            
  end.

Definition sub2top (s : Stack) : option Stack :=
  match s with
    | x1::x2::t => Some ((subB x1 x2)::t)
    | _ => None
  end.

Definition div2top (s : Stack) : option Stack :=
  match s with
    | x1::x2::t => match (toNat x2) with
                      | 0 => Some ((#0:EVMWORD)::t)
                      | _ => Some ((# (Nat.div (toNat x1) (toNat x2)) : EVMWORD)::t)
                              
                   end
    | _ => None            
  end.

(*--------------------------------------------------------------------
 Comparison and bitwise logic operations.
 --------------------------------------------------------------------*)
Definition lt2top (s : Stack) : option Stack :=
  match s with
    | x1::x2::t => if (ltB x1 x2) then Some ((#1 : EVMWORD)::t)
                   else Some ((#0 : EVMWORD)::t)
    | _ => None
  end.

Definition gt2top (s : Stack) : option Stack :=
  match s with
    | x1::x2::t => if (ltB x2 x1) then Some ((#1 : EVMWORD)::t)
                   else Some ((#0 : EVMWORD)::t)
    | _ => None
  end.

Definition isZero (s : Stack) : option Stack :=
  match s with
    | x::t => if (isZeroB x) then Some ((#1 : EVMWORD)::t)
              else Some ((#0 : EVMWORD)::t)
    | nil => None
  end.

Definition notTop (s : Stack) : option Stack :=
  match s with
    | x::t => Some ((xorB x (ones 256))::t)
    | nil => None
  end.


(*--------------------------------------------------------------------
 Stack layout to string.
 --------------------------------------------------------------------*)
Require Import Coq.Strings.String.
Import Ascii.

Definition stacktoString (s : Stack) :=
  foldl (fun x (y : EVMWORD) => (x ++ " " ++ toHex y)%string) ""%string s.

(*---------------------------------------------------------------------
 Unit test
 ---------------------------------------------------------------------*)
Example s := (pushEVMWORD (#5:EVMWORD) (pushEVMWORD (#4:EVMWORD) (pushEVMWORD (#3:EVMWORD) (pushEVMWORD (#2:EVMWORD) (pushEVMWORD (#1:EVMWORD) (initialStack)))))).

Compute (stacktoString s).

Compute (stacktoString (nth_separate 3 s).1).
Compute (stacktoString (nth_separate 3 s).2).

Compute (stacktoString (exchange 3 s)).
Compute (stacktoString (duplicate 6 s)).