(*========================================================
 Model of the EVM virtual ROM (Read only memory) which is 
 used to store the program code.

 It is a list of BYTEs. 
 When the Ethereum Virtual Machine is initialized, the 
 runiing code is coppied from Ethereum Runtime Environment 
 (ERE) into the EVM's ROM.
 ========================================================*)

 Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrfun ssrbool eqtype ssrnat seq fintype finfun tuple zmodp.

Require Import bitsrep bitsops.
Require Import listhelp.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(*=ROM *)
Definition Rom := list BYTE.
(*=End *)

(* Initialize the rom, no cell is mapped *)
Definition initialRom : Rom := @EmptyPMap BYTE 256.

(* Check the memory region from pointer [p] to just below pointer [p'] in [m]
   consists exactly the bytes in [xs] *)
Fixpoint romIs (ro : Rom) (p p' : PTR) xs :=
  if xs is x::xs then ro p = Some x /\ romIs ro (incB p) p' xs
  else p = p'.

(* Map a byte at [p] with 1-bits *)
Definition reserveRomBYTE (ro : Rom) (p : PTR) : Rom :=
  ro !p := ones 8.

(* Map memory region of [c] bytes at [p] with 1-bits *)
Definition reserveRom (ro : Rom) (p : PTR) (c : EVMWORD) : Rom :=
  bIterFrom p c (fun p ro => ro !p := ones 8) ro.

Definition isRomMapped (p : PTR) (ro : Rom) : bool := ro p.

(* Update BYTE at [p] on [ro] *)
Definition updateRomBYTE (ro : Rom) (p : PTR) (b : BYTE) : option Rom :=
  if isRomMapped p ro then Some (ro !p := b)
  else None.
  

(* Read BYTE at [pos] on [ro].
   It is equivalent to using the [readRom] with [readBYTE].
 *)
Definition readRomBYTE (ro : Rom) (pos : EVMWORDCursor) : readerResult BYTE :=
  if pos is mkCursor p then
    if ro p is Some x then
      readerOk x (next p)
    else readerFail
  else readerWrap.
         
(*------------------------------------------------------------------------------------------
 read on sequences
 ------------------------------------------------------------------------------------------*)
Fixpoint readRom T (r : Reader T) (ro : Rom) (pos : EVMWORDCursor) : readerResult T :=
  match r with
    | readerRetn x => readerOk x pos
    | readerNext rd =>
      if pos is mkCursor p then
        if ro p is Some x then readRom (rd x) ro (next p)
        else readerFail
      else readerWrap
    | readerSkip rd =>
      if pos is mkCursor p then
        if ro p is Some x then readRom rd ro (next p)
        else readerFail
      else readerWrap
    | readerCursor rd =>
      readRom (rd pos) ro pos
  end.

(*--------------------------------------------------------------------------------------------
   writer on sequences
 --------------------------------------------------------------------------------------------*)
Fixpoint writeRomTm (w : WriterTm unit) (ro : Rom) (pos : EVMWORDCursor) : option (EVMWORDCursor * Rom) :=
  match w with
    | writerRetn _ => Some (pos, ro)
    | writerNext byte w =>
      if pos is mkCursor p then
        if isMapped p m then
          writeMemTm w (ro!p := byte) (next p)
        else None
      else None
    | writerSkip w =>
      if pos is mkCursor p then
        if isRomMapped p ro then
          writeRomTm w (ro!p := #0) (next p)
        else None
      else None         
    | writerCursor w =>
        writeRomTm (w pos) ro pos
    | writerFail =>
        None
  end.

Definition writeRom {T} (w : Writer T) (ro : Rom) (pos : EVMWORDCursor) (t : T) : option (EVMWORDCursor * Rom) :=
  writeRomTm (w t) ro pos.

(* Write BYTE at [pos] on [ro].
   If ro p is mapped, update it.
   Otherwise, reserve a byte at p and write
 *)
Definition writeRomBYTE (ro : Rom) (pos : EVMWORDCursor) (b : BYTE) : option (EVMWORDCursor * Rom) :=
  if pos is mkCursor p then
    if ro p is Some x then
      Some ((next p), (ro !p := b))
    else Some ((next p), ((reserveRomBYTE ro p) !p := b))
  else None.

(*-------------------------------------------------------------------------------------------
   Rom layout to string
 -------------------------------------------------------------------------------------------*)
Require Import Coq.Strings.String.
Import Ascii.

(* Rom to string *)
Fixpoint enumRomToString (xs : seq (EVMWORD * BYTE)) :=
  (if xs is (p, b)::xs then
     toHex p ++ ":=" ++ toHex b ++ ", " ++ enumRomToString xs
   else "")%string.

Definition romtoString (ro : Rom) := enumRomToString (enumPMap ro).


