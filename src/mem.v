(*===========================================================================
  Representation of partial finite maps whose domain is BITS n
  We use a representation that is sparse, has O(n) lookup, and is canonical
  so Leibniz equality coincides with extensional equality
  ===========================================================================*)


Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrfun ssrbool eqtype ssrnat seq fintype finfun.

Require Import bitsrep pmap reader writer.

Local Open Scope update_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.




