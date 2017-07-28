(*===============================================================================
    Model for the EVM storage in EVM execution environment
   
    Note that operations are partial, as not all storage is mapped.
    Each storage cell is a EVMWORD - 256-bits.
  ==============================================================================*)


Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrfun ssrbool eqtype ssrnat seq fintype finfun.

Require Import bitsrep bitsops cursor pmap reader writer mem.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* 256-bit addressable storage of EVMWORD *)
(*=Storage *)
Definition Storage := PMAP EVMWORD 256.
(*= End *)


(* Initialize the storage, no cell is mapped *)
Definition initialStorage : Storage := @EmptyPMap EVMWORD 256.

(* Check the storage region from pointer [p] to just below pointer [p'] in [sto]
   consists exactly the evmwords in [xs] *)
Fixpoint stoIs (sto : Storage) (p p' : PTR) xs :=
  if xs is x::xs then sto p = Some x /\ stoIs sto (incB p) p' xs
  else p = p'.

(* Map an evmword at [p] with 1-bits *)
Definition reserveStorageEVMWORD (sto: Storage) (p : PTR) : Storage :=
  sto !p := ones 256.

(* Map storage region of [c] words at [p] with 1-bits *)
Definition reserveStorage (sto : Storage) (p : PTR) (c : EVMWORD) : Storage :=
  bIterFrom p c (fun p sto => sto !p := ones 256) sto.

Definition isMappedStorage (p : PTR) (sto : Storage) : bool := sto p.

(* Update EVMWORD at [p] on [sto] *)
Definition updateEVMWORD (sto : Storage) (p : PTR) (evmw : EVMWORD) : option Storage :=
  if isMappedStorage p sto then Some (sto !p := evmw)
  else None.

(* Write EVMWORD at [pos] on [sto].
   If sto p is mapped, update it.
   Otherwise, reserve a word at p and write
 *)
Definition writeStorageEVMWORD (sto : Storage) (pos : EVMWORDCursor) (evmw : EVMWORD) : option (EVMWORDCursor * Storage) :=
  if pos is mkCursor p then
    if sto p is Some x then
      Some ((next p), (sto !p := evmw))
    else Some ((next p), ((reserveStorageEVMWORD sto p) !p := evmw))
  else None.


(* Read EVMWORD at [pos] on [sto].
   It is equivalent to using the [readStorage] with [readEVMWORD].
 *)
Definition readStorageEVMWORD (sto : Storage) (pos : EVMWORDCursor) : readerResult EVMWORD :=
  if pos is mkCursor p then
    if sto p is Some x then
      readerOk x (next p)
    else readerFail
  else readerWrap.

(*--------------------------------------------------------------------------------------------
  Storage layout to string
 --------------------------------------------------------------------------------------------*)
Require Import Coq.Strings.String.
Import Ascii.

(* Storage to string *)
Fixpoint enumStorageToString (xs : seq (EVMWORD * EVMWORD)) :=
  (if xs is (p, w)::xs then
     toHex p ++ ":=" ++ toHex w ++ ", " ++ enumStorageToString xs
   else "")%string.

Definition storagetoString (sto : Storage) := enumStorageToString (enumPMap sto).


(*----------------------------------------------------------------------------------------------
 A simple unit test 
 ----------------------------------------------------------------------------------------------*)
Example s: Storage := (@EmptyPMap _ _) ! #5 := (#12 : EVMWORD) ! #6 := (#10 : EVMWORD).
Compute (storagetoString s).
        
(* Read a word at pos 5 *)
Compute (
    let rw := readStorageEVMWORD s (#5) in
    readerResultToString rw
  ).

(* Write a word at pos 9 *)
Compute (
    let os := writeStorageEVMWORD s (#9) (#15 : EVMWORD) in 
    match os with
      | Some (c, s) => storagetoString s
      | None => ("Write error!")%string
    end
  ).
