(*============================================================================================
 The Ethereum Runtime Environment (ERE) for the virtual machine EVM.

 ============================================================================================*)

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrfun ssrbool eqtype ssrnat seq fintype finfun tuple zmodp.

Require Import bitsrep bitsops cursor pmap reader writer mem stack instr program.


(*=Log topic *)
Definition LOGTopic := seq EVMWORD.

Notation "'nilLOGTopic'" := nil.
(*=End *)

(*=Log entry *)
Record LOGEntry :=
  mkLOGEntry {
      a : ADDRESS;
      t : LOGTopic;
      logm : seq BYTE
    }.
(*=End *)

(*-------------------------------------------------------------------------------------------
 Initialize.
 -------------------------------------------------------------------------------------------*)
Definition initialLOGEntry : LOGEntry :=
  mkLOGEntry (#0 : ADDRESS) nilLOGTopic nil.

(*=ERE *)
Record EREnvironment :=
  mkEREnvironment {
      (* address of the contract or contract-to-be that owns the running code *)
      Ia : ADDRESS;
      (* the sender address that sends the message - either equal to origin or a constract *)
      Io : ADDRESS;
      (* Original transactor *)
      Is : ADDRESS;
      (* the price of gas in the transaction *)
      Ip : EVMWORD;
      (* the input data *)
      Id : seq BYTE;
      (* the value *)
      Iv : EVMWORD;
      (* the bytecode *)
      Ib : Program;
      (* the hash of executing code *)
      Ih : EVMWORD;
      
      (* sub-state *)
      As : seq ADDRESS;
      Al : seq LOGEntry;
      Ar : EVMWORD;

      (* the call depth *)
      Ie : EVMWORD
    }.

(*=End *)

(*---------------------------------------------------------------------------------------------
 Initialization.
 ---------------------------------------------------------------------------------------------*)
Definition initialERE : EREnvironment :=
  mkEREnvironment (#0 : ADDRESS)
                  (#0 : ADDRESS)
                  (#0 : ADDRESS)
                  (#0 : EVMWORD)
                  nil
                  (#0 : EVMWORD)
                  initialProgram
                  (#0 : EVMWORD)
                  nil
                  nil
                  (#0 : EVMWORD)
                  (#0 : EVMWORD).

(*---------------------------------------------------------------------------------------------
 Update Ia.
 ---------------------------------------------------------------------------------------------*)
Definition updateIa (newIa : ADDRESS) (e : EREnvironment) : EREnvironment :=
  mkEREnvironment newIa 
                  e.(Io) 
                  e.(Is)
                  e.(Ip)
                  e.(Id) 
                  e.(Iv)
                  e.(Ib) 
                  e.(Ih) 
                  e.(As) 
                  e.(Al) 
                  e.(Ar) 
                  e.(Ie).


(*---------------------------------------------------------------------------------------------
 Update Io.
 ---------------------------------------------------------------------------------------------*)
Definition updateIo (newIo : ADDRESS) (e : EREnvironment) : EREnvironment :=
  mkEREnvironment e.(Ia) 
                  newIo 
                  e.(Is)
                  e.(Ip)
                  e.(Id) 
                  e.(Iv)
                  e.(Ib) 
                  e.(Ih) 
                  e.(As) 
                  e.(Al) 
                  e.(Ar) 
                  e.(Ie).


(*---------------------------------------------------------------------------------------------
 Update Is.
 ---------------------------------------------------------------------------------------------*)
Definition updateIs (newIs : ADDRESS) (e : EREnvironment) : EREnvironment :=
  mkEREnvironment e.(Ia) 
                  e.(Io) 
                  newIs
                  e.(Ip)
                  e.(Id) 
                  e.(Iv)
                  e.(Ib) 
                  e.(Ih) 
                  e.(As) 
                  e.(Al) 
                  e.(Ar) 
                  e.(Ie).


(*---------------------------------------------------------------------------------------------
 Update Ip.
 ---------------------------------------------------------------------------------------------*)
Definition updateIp (newIp : EVMWORD) (e : EREnvironment) : EREnvironment :=
  mkEREnvironment e.(Ia) 
                  e.(Io) 
                  e.(Is)
                  newIp
                  e.(Id) 
                  e.(Iv)
                  e.(Ib) 
                  e.(Ih) 
                  e.(As) 
                  e.(Al) 
                  e.(Ar) 
                  e.(Ie).

(*---------------------------------------------------------------------------------------------
 Update Id.
 Notice that it updates the whole sequence of BYTE in Id.
 ---------------------------------------------------------------------------------------------*)
Definition updateId (newId : seq BYTE) (e : EREnvironment) : EREnvironment :=
  mkEREnvironment e.(Ia) 
                  e.(Io) 
                  e.(Is)
                  e.(Ip)
                  newId 
                  e.(Iv)
                  e.(Ib) 
                  e.(Ih) 
                  e.(As) 
                  e.(Al) 
                  e.(Ar) 
                  e.(Ie).


(*---------------------------------------------------------------------------------------------
 Update Iv.
 ---------------------------------------------------------------------------------------------*)
Definition updateIv (newIv : EVMWORD) (e : EREnvironment) : EREnvironment :=
  mkEREnvironment e.(Ia) 
                  e.(Io) 
                  e.(Is)
                  e.(Ip)
                  e.(Id) 
                  newIv
                  e.(Ib) 
                  e.(Ih) 
                  e.(As) 
                  e.(Al) 
                  e.(Ar) 
                  e.(Ie).

(*---------------------------------------------------------------------------------------------
 Update Ib.
 Notive that it replaces the whole sequence of BYTE in Ib.
 ---------------------------------------------------------------------------------------------*)
Definition updateIb (newIb : Program) (e : EREnvironment) : EREnvironment :=
  mkEREnvironment e.(Ia) 
                  e.(Io) 
                  e.(Is)
                  e.(Ip)
                  e.(Id) 
                  e.(Iv)
                  newIb 
                  e.(Ih) 
                  e.(As) 
                  e.(Al) 
                  e.(Ar) 
                  e.(Ie).

(*---------------------------------------------------------------------------------------------
 Update Ih.
 ---------------------------------------------------------------------------------------------*)
Definition updateIh (newIh : EVMWORD) (e : EREnvironment) : EREnvironment :=
  mkEREnvironment e.(Ia) 
                  e.(Io) 
                  e.(Is)
                  e.(Ip)
                  e.(Id) 
                  e.(Iv)
                  e.(Ib) 
                  newIh 
                  e.(As) 
                  e.(Al) 
                  e.(Ar) 
                  e.(Ie).

(*---------------------------------------------------------------------------------------------
 Update As.
 ---------------------------------------------------------------------------------------------*)
Definition updateAs (newAs : seq ADDRESS) (e : EREnvironment) : EREnvironment :=
  mkEREnvironment e.(Ia) 
                  e.(Io) 
                  e.(Is)
                  e.(Ip)
                  e.(Id) 
                  e.(Iv)
                  e.(Ib) 
                  e.(Ih) 
                  newAs 
                  e.(Al) 
                  e.(Ar) 
                  e.(Ie).

(*---------------------------------------------------------------------------------------------
 Update Al.
 ---------------------------------------------------------------------------------------------*)
Definition updateAl (newAl : seq LOGEntry) (e : EREnvironment) : EREnvironment :=
  mkEREnvironment e.(Ia) 
                  e.(Io) 
                  e.(Is)
                  e.(Ip)
                  e.(Id) 
                  e.(Iv)
                  e.(Ib) 
                  e.(Ih) 
                  e.(As) 
                  newAl 
                  e.(Ar) 
                  e.(Ie).

(*---------------------------------------------------------------------------------------------
 Update Ar.
 ---------------------------------------------------------------------------------------------*)
Definition updateAr (newAr : EVMWORD) (e : EREnvironment) : EREnvironment :=
  mkEREnvironment e.(Ia) 
                  e.(Io) 
                  e.(Is)
                  e.(Ip)
                  e.(Id) 
                  e.(Iv)
                  e.(Ib) 
                  e.(Ih) 
                  e.(As) 
                  e.(Al) 
                  newAr 
                  e.(Ie).

(*---------------------------------------------------------------------------------------------
 Update Ie.
 ---------------------------------------------------------------------------------------------*)
Definition updateIe (newIe : EVMWORD) (e : EREnvironment) : EREnvironment :=
  mkEREnvironment e.(Ia) 
                  e.(Io) 
                  e.(Is)
                  e.(Ip)
                  e.(Id) 
                  e.(Iv)
                  e.(Ib) 
                  e.(Ih) 
                  e.(As) 
                  e.(Al) 
                  e.(Ar) 
                  newIe.
