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

(* Map memory region of 32 bytes at [p] with 1-bits *)
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

(* Update EVMWORD at [p] on [m] with fixpoint *)
Definition updateBYTE (m : Mem) (p : PTR) (b : BYTE) : option Mem :=
  if isMapped p m then Some (m !p := b)
  else None.
