(*=====================================================================
 The fee schedule is a tuple of 31 scalar values corresponding to the 
 relative costs.
 =====================================================================*)

From Coq Require Import ZArith.ZArith Strings.String.

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrfun ssrbool eqtype ssrnat seq fintype finfun tuple zmodp.

Require Import exceptions bitsrep bitsops.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(*=Fee Schedule *)
Definition Gzero : Z := 0.
Definition Gbase : Z := 2.
Definition Gverylow : Z := 3.
Definition Glow : Z := 5.
Definition Gmid : Z := 8.
Definition Ghigh : Z := 10.
Definition Gext : Z := 20.
Definition Gsload : Z := 50.
Definition Gjumpdest : Z := 1.
Definition Gsset : Z := 20000.
Definition Gsreset : Z := 5000.
Definition Rsclear : Z := 15000.
Definition Rsuicide : Z := 24000.
Definition Gcreate : Z := 32000.
Definition Gcodedeposit : Z := 200.
Definition Gcall : Z := 40.
Definition Gcallvalue : Z := 9000.
Definition Gcallstipend : Z := 2300.
Definition Gcallnewaccount : Z := 25000.
Definition Gexp : Z := 10.
Definition Gexpbyte : Z := 10.
Definition Gmemory : Z := 3.
Definition Gtxcreate : Z := 32000.
Definition Gtxdatazero : Z := 4.
Definition Gtxdatanonzero : Z := 68.
Definition Gtransaction : Z := 21000.
Definition Glog : Z := 375.
Definition Glogdata : Z := 8.
Definition Glogtopic : Z := 375.
Definition Gsha3 : Z := 30.
Definition Gsha3word : Z := 6.
Definition Gcopy : Z := 3.

