(*===========================================================================
    Model for the EVM memory

    Note that operations are partial, as not all memory is mapped. 
    Each memory cell is a BYTE.
  ===========================================================================*)
  
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrfun ssrbool eqtype ssrnat seq fintype finfun.

Require Import bitsrep bitsops cursor pmap reader writer.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* 256-bit addressable memory of bytes *)
(*=Mem *)
Definition Mem := PMAP BYTE 256.
(*=End*)

Definition PTR := EVMWORD.
Identity Coercion PTRtoEVMWORD : PTR >-> EVMWORD.

(* Initialize the memory, no memory is mapped *)
Definition initialMemory : Mem := @EmptyPMap BYTE 256.

(* Check the memory region from pointer [p] to just below pointer [p'] in [m]
   consists exactly the bytes in [xs] *)
Fixpoint memIs (m : Mem) (p p' : PTR) xs :=
  if xs is x::xs then m p = Some x /\ memIs m (incB p) p' xs
  else p = p'.

(* Map a byte at [p] with 1-bits *)
Definition reserveMemoryBYTE (m : Mem) (p : PTR) : Mem :=
  m !p := ones 8.

(* Map memory region of [c] bytes at [p] with 1-bits *)
Definition reserveMemory (m : Mem) (p : PTR) (c : EVMWORD) : Mem :=
  bIterFrom p c (fun p m => m !p := ones 8) m.

(* Return bytes with most-significant first *)
Definition EVMWORDtoBytes (d : EVMWORD) : BYTE*BYTE*BYTE*BYTE*BYTE*BYTE*BYTE*BYTE*
                                          BYTE*BYTE*BYTE*BYTE*BYTE*BYTE*BYTE*BYTE*
                                          BYTE*BYTE*BYTE*BYTE*BYTE*BYTE*BYTE*BYTE*
                                          BYTE*BYTE*BYTE*BYTE*BYTE*BYTE*BYTE*BYTE :=
  split32 8 8 8 8 8 8 8 8 8 8 8 8 8 8 8 8 8 8 8 8 8 8 8 8 8 8 8 8 8 8 8 8 d.

Definition isMapped (p : PTR) (ms : Mem) : bool := ms p.


(* Update EVMWORD at [p] on [m] *)
Instance MemUpdateOpsEVMWORD : UpdateOps Mem PTR EVMWORD :=
  fun m p v =>
    let '(b31,b30,b29,b28,b27,b26,b25,b24,b23,b22,b21,b20,b19,b18,b17,b16,
          b15,b14,b13,b12,b11,b10,b9,b8,b7,b6,b5,b4,b3,b2,b1,b0) := EVMWORDtoBytes v in
    m !p := b0 !incB p := b1 !incB(incB p) := b2 !incB(incB(incB p)) := b3 !incB(incB(incB(incB p))) := b4 !incB(incB(incB(incB(incB p)))) := b5 !incB(incB(incB(incB(incB(incB p))))) := b6 !incB(incB(incB(incB(incB(incB(incB p)))))) := b7 !incB(incB(incB(incB(incB(incB(incB(incB p))))))) := b8 !incB(incB(incB(incB(incB(incB(incB(incB(incB p)))))))) := b9 !incB(incB(incB(incB(incB(incB(incB(incB(incB(incB p))))))))) := b10 !incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB p)))))))))) := b11 !incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB p))))))))))) := b12 !incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB p)))))))))))) := b13 !incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB p))))))))))))) := b14 !incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB p)))))))))))))) := b15 !incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB p))))))))))))))) := b16 !incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB p)))))))))))))))) := b17 !incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB p))))))))))))))))) := b18 !incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB p)))))))))))))))))) := b19 !incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB p))))))))))))))))))) := b20 !incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB p)))))))))))))))))))) := b21 !incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB p))))))))))))))))))))) := b22 !incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB p)))))))))))))))))))))) := b23 !incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB p))))))))))))))))))))))) := b24 !incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB p)))))))))))))))))))))))) := b25 !incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB p))))))))))))))))))))))))) := b26 !incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB p)))))))))))))))))))))))))) := b27 !incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB p))))))))))))))))))))))))))) := b28 !incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB p)))))))))))))))))))))))))))) := b29 !incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB p))))))))))))))))))))))))))))) := b30 !incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB(incB p)))))))))))))))))))))))))))))) := b31.

(* Update BYTE at [p] on [m] *)
Definition updateBYTE (m : Mem) (p : PTR) (b : BYTE) : option Mem :=
  if isMapped p m then Some (m !p := b)
  else None.

(* Write BYTE at [p] on [m].
   If m p is mapped, update it.
   Otherwise, reserve a byte at p and write
 *)
Definition writeMemBYTE (m : Mem) (p : PTR) (b : BYTE) : Mem :=
  if isMapped p m then
    m !p := b
  else
    (reserveMemoryBYTE m p) !p := b.
  
(*-------------------------------------------------------------------------------------------- 
 "readers of T" type:
   
   read m p = readerFail if memory at p in m is inaccessible for reading T
   read m p = readerWrap if we tried to read beyond the end of memory
   read m p = readerOk x q if memory between p inclusive and q exclusive represents x : T
 --------------------------------------------------------------------------------------------*)
Inductive readerResult T :=
  readerOk (x : T) (q : EVMWORDCursor)
| readerWrap
| readerFail.

Implicit Arguments readerOk [T].
Implicit Arguments readerWrap [T].
Implicit Arguments readerFail [T].

(* Read BYTE at [pos] on [m].
   It is equivalent to using the [readMem] with [readBYTE].
 *)
Definition readMemBYTE (m : Mem) (pos : EVMWORDCursor) : readerResult BYTE :=
  if pos is mkCursor p then
    if m p is Some x then
      readerOk x (next p)
    else readerFail
  else readerWrap.
         
(*------------------------------------------------------------------------------------------
 read on sequences
 ------------------------------------------------------------------------------------------*)
Fixpoint readMem T (r : Reader T) (m : Mem) (pos : EVMWORDCursor) : readerResult T :=
  match r with
    | readerRetn x => readerOk x pos
    | readerNext rd =>
      if pos is mkCursor p then
        if m p is Some x then readMem (rd x) m (next p)
        else readerFail
      else readerWrap
    | readerSkip rd =>
      if pos is mkCursor p then
        if m p is Some x then readMem rd m (next p)
        else readerFail
      else readerWrap
    | readerCursor rd =>
      readMem (rd pos) m pos
  end.

(*--------------------------------------------------------------------------------------------
   writer on sequences
 --------------------------------------------------------------------------------------------*)
Fixpoint writeMemTm (w : WriterTm unit) (m : Mem) (pos : EVMWORDCursor) : option (EVMWORDCursor * Mem) :=
  match w with
    | writerRetn _ => Some (pos, m)
    | writerNext byte w =>
      if pos is mkCursor p then
        if isMapped p m then
          writeMemTm w (m!p := byte) (next p)
        else None
      else None
    | writerSkip w =>
      if pos is mkCursor p then
        if isMapped p m then
          writeMemTm w (m!p := #0) (next p)
        else None
      else None         
    | writerCursor w =>
        writeMemTm (w pos) m pos
    | writerFail =>
        None
  end.

Definition writeMem {T} (w : Writer T) (m : Mem) (pos : EVMWORDCursor) (t : T) : option (EVMWORDCursor * Mem) :=
  writeMemTm (w t) m pos.

Require Import Coq.Strings.String.
Import Ascii.

(* Memory to string *)
Fixpoint enumMemToString (xs : seq (EVMWORD * BYTE)) :=
  (if xs is (p, b)::xs then
     toHex p ++ ":=" ++ toHex b ++ ", " ++ enumMemToString xs
   else "")%string.

Definition memtoString (m : Mem) := enumMemToString (enumPMap m).

(* readerResult to string *)
Fixpoint readerResultToString (n : nat) (rs : readerResult (BITS n)) :=
  match rs with
     | readerFail => ("Inaccessible memory!")%string
     | readerWrap => ("Out of memory!")%string
     | readerOk x q =>
       if q is mkCursor p then
         ("Next cursor:=" ++ toHex p ++ ", " ++ "Content:=" ++ toHex x)%string
       else ("Next curspr:= Top" ++ ", " ++ "Content:=" ++ toHex x)%string
  end.

(*----------------------------------------------------------------------------------------------
 A simple unit test 
 ----------------------------------------------------------------------------------------------*)
Example m: Mem := (@EmptyPMap _ _) ! #5 := (#12 : BYTE) ! #6 := (#10 : BYTE) ! #8 := (#15 : BYTE).
Compute (memtoString m).
        
(* Read a byte at pos 5 *)
Compute (
    let rb := readMemBYTE m (#5) in
    readerResultToString rb
  ).

(* Read a byte at pos 5 with [readMem] *)
Compute (
    let rb := readMem readBYTE m (#5) in
    readerResultToString rb
  ).

(* Read a word at pos 5 *)
Example rw: readerResult WORD := readMem readWORD m (#5).
Compute (
    let rw := readMem readWORD m (#5) in
    readerResultToString rw
  ).

(* Write a byte at pos 6 *)
Compute (
    let omem := writeMem writeBYTE m (#6) (#9 : BYTE) in 
    match omem with
      | Some (c, m) => memtoString m
      | None => ("Write error!")%string
    end
  ).

(* Write a byte at pos 9 -- error since this cell is not mapped yet *)
Compute (
    let omem := writeMem writeBYTE m (#9) (#12 : BYTE) in
    match omem with
      | Some (c, m) => memtoString m
      | None => ("Write error!")%string
    end
  ).

(* Test reserveMemoryByte *)
Compute (
    let m := reserveMemoryBYTE m (#9) in
    let omem := writeMem writeBYTE m (#9) (#12 : BYTE) in
    match omem with
      | Some (c, m) => memtoString m
      | None => ("Write error!")%string
    end
  ).


