(*===========================================================================
    Reader monad, with instances for BYTE, WORD and DWORD
  ===========================================================================*)
From mathcomp Require Import all_ssreflect.
Require Import bitsrep bitsops monad cursor.
Require Import Coq.Logic.FunctionalExtensionality Coq.Strings.String cstring.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* Term representation for a T-reader *)
(*=Reader *)
Inductive ReaderTm T :=
| readerRetn (x: T)
| readerNext (rd: BYTE -> ReaderTm T)
| readerSkip (rd: ReaderTm T)
| readerCursor (rd: EVMWORDCursor -> ReaderTm T).

Class Reader T := getReaderTm : ReaderTm T.
(*=End *)
Instance readCursor : Reader (EVMWORDCursor) := readerCursor (fun p => readerRetn p).
Definition readNext {T} {R: Reader T}: Reader T := R.

Fixpoint readerBind X Y (r: Reader X) (f: X -> Reader Y) : Reader Y :=
  match r with
  | readerRetn r => f r
  | readerNext rd => readerNext (fun b => readerBind (rd b) f)
  | readerSkip rd => readerSkip (readerBind rd f)
  | readerCursor rd => readerCursor (fun p => readerBind (rd p) f)
  end.

Fixpoint readerTmSkipFree X (r: ReaderTm X) :=
match r with
| readerRetn _ => True
| readerSkip _ => False
| readerNext r => forall b, readerTmSkipFree (r b)
| readerCursor r => forall f, readerTmSkipFree (r f)
end.


Instance readerMonadOps : MonadOps Reader :=
{ retn := readerRetn
; bind := readerBind }.

Instance readerMonad : Monad Reader.
Proof. apply Build_Monad.
(* id_l *)
  move => X Y x f. done.
(* id_r *)
  move => X. elim => //.
  - move => rd IH/=.
    apply f_equal. apply functional_extensionality => b. apply IH.
  - move => rd IH/=. by apply f_equal.
  - move => rd IH/=.
    apply f_equal. apply functional_extensionality => b. apply IH.
(* assoc *)
  move => X Y Z. elim => //.
  - move => rd IH f g/=.
    apply f_equal. apply functional_extensionality => b. apply IH.
  - move => rd IH f g/=. by apply f_equal.
  - move => rd IH f g/=.
    apply f_equal. apply functional_extensionality => b. apply IH.
Qed.

(* Functional interpretation of reader on sequences.
   Returns the final position, the tail of the given sequence and the value
   read. *)
Fixpoint runReader T (r:Reader T) (c:EVMWORDCursor) xs : option (EVMWORDCursor * seq BYTE * T) :=
  match r with
  | readerRetn x => Some (c, xs, x)
  | readerNext rd =>
    if c is mkCursor p
    then
      if xs is x::xs
      then runReader (rd x) (next p) xs
      else None
    else None
  | readerSkip rd =>
    if c is mkCursor p
    then runReader rd (next p) xs
    else None
  | readerCursor rd =>
    runReader (rd c) c xs
  end.

Lemma runReader_bind T U (r: Reader T) (f: T -> Reader U) :
  forall x xs ys cursor cursor',
  runReader r cursor xs = Some (cursor', ys, x) ->
  runReader (readerBind r f) cursor xs = runReader (f x) cursor' ys.
Proof. induction r.
+ move => x' xs ys c c' H. simpl in H. by injection H => -> -> ->.
+ move => x xs ys c c' H'. simpl.
  destruct c => //.
  destruct xs => //. simpl in H'. by apply H.
+ move => x xs ys c c' H'. simpl.
  destruct c => //. simpl in H'. by apply IHr.
+ move => x xs ys c c' H'. simpl. simpl in H'.
  by apply H.
Qed.


(*---------------------------------------------------------------------------
   Reader type class together with BYTE, WORD, DWORD, QWORD, DQWORD, 
   ADDRESS, EVMWORD, and pad instances
  ---------------------------------------------------------------------------*)
(*=readBYTE *)
Instance readBYTE : Reader BYTE | 0 :=
  readerNext (fun b => readerRetn b).
(*=End *)

Lemma runReader_readBYTE (p: EVMWORD) byte bytes :
  runReader readBYTE p (byte::bytes) =
  Some (next p, bytes, byte).
Proof. done. Qed.

Definition readSkip : Reader unit :=
  readerSkip (readerRetn tt).

(*=readWORD *)
Definition bytesToWORD (b1 b0: BYTE) : WORD := b1 ## b0.
Instance readWORD: Reader WORD | 0 :=
  let! b0 = readNext;
  let! b1 = readNext;
  retn (bytesToWORD b1 b0).
(*=End *)

(*=readDWORD *)
Definition bytesToDWORD (b3 b2 b1 b0: BYTE) : DWORD :=
  b3 ## b2 ## b1 ## b0.
Instance readDWORD : Reader DWORD | 0 :=
  let! b0 = readNext;
  let! b1 = readNext;
  let! b2 = readNext;
  let! b3 = readNext;
  retn (bytesToDWORD b3 b2 b1 b0).
(*=End *)

(*=readQWORD *)
Definition bytesToQWORD (b7 b6 b5 b4 b3 b2 b1 b0: BYTE) : QWORD :=
  b7 ## b6 ## b5 ## b4 ## b3 ## b2 ## b1 ## b0.
Instance readQWORD : Reader QWORD | 0 :=
  let! b0 = readNext;
  let! b1 = readNext;
  let! b2 = readNext;
  let! b3 = readNext;
  let! b4 = readNext;
  let! b5 = readNext;
  let! b6 = readNext;
  let! b7 = readNext;
  retn (bytesToQWORD b7 b6 b5 b4 b3 b2 b1 b0).
(*=End *)

(*=readDQWORD *)
Definition bytesToDQWORD (b15 b14 b13 b12 b11 b10 b9 b8 b7 b6 b5 b4 b3 b2 b1 b0: BYTE) : DQWORD :=
  b15 ## b14 ## b13 ## b12 ## b11 ## b10 ## b9 ## b8 ## b7 ## b6 ## b5 ## b4 ## b3 ## b2 ## b1 ## b0.
Instance readDQWORD : Reader DQWORD | 0 :=
  let! b0 = readNext;
  let! b1 = readNext;
  let! b2 = readNext;
  let! b3 = readNext;
  let! b4 = readNext;
  let! b5 = readNext;
  let! b6 = readNext;
  let! b7 = readNext;
  let! b8 = readNext;
  let! b9 = readNext;
  let! b10 = readNext;
  let! b11 = readNext;
  let! b12 = readNext;
  let! b13 = readNext;
  let! b14 = readNext;
  let! b15 = readNext;
  retn (bytesToDQWORD b15 b14 b13 b12 b11 b10 b9 b8 b7 b6 b5 b4 b3 b2 b1 b0).
(*=End *)

(*=readADDRESS *)
Definition bytesToADDRESS (b19 b18 b17 b16 b15 b14 b13 b12 b11 b10 b9 b8 b7 b6 b5 b4 b3 b2 b1 b0: BYTE) : ADDRESS :=
  b19 ## b18 ## b17 ## b16 ## b15 ## b14 ## b13 ## b12 ## b11 ## b10 ## b9 ## b8 ## b7 ## b6 ## b5 ## b4 ## b3 ## b2 ## b1 ## b0.
Instance readADDRESS : Reader ADDRESS | 0 :=
  let! b0 = readNext;
  let! b1 = readNext;
  let! b2 = readNext;
  let! b3 = readNext;
  let! b4 = readNext;
  let! b5 = readNext;
  let! b6 = readNext;
  let! b7 = readNext;
  let! b8 = readNext;
  let! b9 = readNext;
  let! b10 = readNext;
  let! b11 = readNext;
  let! b12 = readNext;
  let! b13 = readNext;
  let! b14 = readNext;
  let! b15 = readNext;
  let! b16 = readNext;
  let! b17 = readNext;
  let! b18 = readNext;
  let! b19 = readNext;
  retn (bytesToADDRESS b19 b18 b17 b16 b15 b14 b13 b12 b11 b10 b9 b8 b7 b6 b5 b4 b3 b2 b1 b0).
(*=End *)

(*=readEVMWORD *)
Definition bytesToEVMWORD (b31 b30 b29 b28 b27 b26 b25 b24 b23 b22 b21 b20 b19 b18 b17 b16 b15 b14 b13 b12 b11 b10 b9 b8 b7 b6 b5 b4 b3 b2 b1 b0: BYTE) : EVMWORD :=
  b31 ## b30 ## b29 ## b28 ## b27 ## b26 ## b25 ## b24 ## b23 ## b22 ## b21 ## b20 ## b19 ## b18 ## b17 ## b16 ## b15 ## b14 ## b13 ## b12 ## b11 ## b10 ## b9 ## b8 ## b7 ## b6 ## b5 ## b4 ## b3 ## b2 ## b1 ## b0.
Instance readEVMWORD : Reader EVMWORD | 0 :=
  let! b0 = readNext;
  let! b1 = readNext;
  let! b2 = readNext;
  let! b3 = readNext;
  let! b4 = readNext;
  let! b5 = readNext;
  let! b6 = readNext;
  let! b7 = readNext;
  let! b8 = readNext;
  let! b9 = readNext;
  let! b10 = readNext;
  let! b11 = readNext;
  let! b12 = readNext;
  let! b13 = readNext;
  let! b14 = readNext;
  let! b15 = readNext;
  let! b16 = readNext;
  let! b17 = readNext;
  let! b18 = readNext;
  let! b19 = readNext;
  let! b20 = readNext;
  let! b21 = readNext;
  let! b22 = readNext;
  let! b23 = readNext;
  let! b24 = readNext;
  let! b25 = readNext;
  let! b26 = readNext;
  let! b27 = readNext;
  let! b28 = readNext;
  let! b29 = readNext;
  let! b30 = readNext;
  let! b31 = readNext;
  retn (bytesToEVMWORD b31 b30 b29 b28 b27 b26 b25 b24 b23 b22 b21 b20 b19 b18 b17 b16 b15 b14 b13 b12 b11 b10 b9 b8 b7 b6 b5 b4 b3 b2 b1 b0).
(*=End *)

(** This must go at a lower level/priority than [readDWORD] and [readBYTE] so it is picked up less eagerly. *)
Instance readVWORD s : Reader (VWORD s) | 1 :=
  match s as s return Reader (VWORD s) with
  | OpSize1 => readBYTE
  | OpSize2 => readWORD
  | OpSize4 => readDWORD
  | OpSize8 => readQWORD
  | OpSize16 => readDQWORD
  | OpSize20 => readADDRESS
  | OpSize32 => readEVMWORD
  end.

Fixpoint readPad (n:nat) : Reader unit :=
  if n is n'.+1
  then do! readBYTE; readPad n'
  else retn tt.

Fixpoint readString (n:nat) : Reader string :=
  if n is n'.+1
  then let! c = readBYTE;
       let! s = readString n';
       retn (String (Ascii.ascii_of_nat (toNat c)) s)
  else retn EmptyString.

Fixpoint readTupleBYTE (n:nat) : Reader (n.-tuple BYTE) :=
  if n is n'.+1
  then let! b = readBYTE;
       let! bs = readTupleBYTE n';
       retn (cons_tuple b bs)
  else retn (nil_tuple _).
Global Existing Instance readTupleBYTE.

(* Here n is the maximum number of characters to read *)
(*Fixpoint readCString : Reader cstring :=
  let! c = readBYTE;
       if c == #0 then retn emptyString
       else
         let! s = readCString;
         retn (cons_cstring (Ascii.ascii_of_nat (toNat c)) s).

Global Existing Instance readCString.
*)

Definition readAlign (m:nat) : Reader unit :=
  let! c = readCursor;
  if c is mkCursor pos
  then readPad (toNat (negB (lowWithZeroExtend m pos)))
  else retn tt.

Fixpoint readSkipPad (n:nat) : Reader unit :=
  if n is n'.+1
  then do! readSkip; readSkipPad n'
  else retn tt.

Definition readSkipAlign (m:nat) : Reader unit :=
  let! c = readCursor;
  if c is mkCursor pos
  then readSkipPad (toNat (negB (lowWithZeroExtend m pos)))
  else retn tt.
