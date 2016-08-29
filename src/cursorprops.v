(* Properties of Cursor *)

From mathcomp Require Import all_ssreflect.

Require Import nathelp.

Require Import bitsrep bitsprops bitsops bitsopsprops.

Require Import Coq.omega.Omega.

Require Import cursor.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Lemma nextIsInc n (p q : BITS n) : next p = mkCursor q -> p+#1 = q.
Proof.
  rewrite /next. move => EQ.
  case E: (p == ones n). rewrite E in EQ. done.
  rewrite E in EQ. 
  rewrite addB1.
  congruence.
Qed.