(*===========================================================================
    Model for the EVM memory

    Note that operations are partial, as not all memory is mapped. 
	 Each memory cell is a BYTE.
  ===========================================================================*)
  
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrfun ssrbool eqtype ssrnat seq fintype finfun.

Require Import bitsrep bitsops cursor pmap reader writer.

Local Open Scope update_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.




