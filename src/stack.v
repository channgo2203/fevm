(*=====================================================================
    Model for the EVM stack

    Each item on stack is a EVMWORD - 256-bit.
 *====================================================================*)


Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrfun ssrbool eqtype ssrnat seq fintype finfun.

Require Import bitsrep bitsops .

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

