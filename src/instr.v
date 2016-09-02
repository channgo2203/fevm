(*============================================================================
 EVM Instructions.
 
 ============================================================================*)


Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrfun ssrbool eqtype ssrnat seq fintype tuple zmodp.

Require Import bitsrep bitsops.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(*= Instr *)
Inductive Instr :=
    (* Stop and arithmetic operations *)
| STOP
| ADD
| MUL
| SUB
| DIV
| SDIV
| MOD
| SMOD
| ADDMOD
| MULMOD
| EXP
| SIGNEXTEND
    (* Comparison and bitwise logic operations *)
| LT
| GT
| SLT
| SGT
| EQ
| ISZERO
| AND
| OR
| XOR
| NOT
| BYTE
    (* SHA3 *)
| SHA3
    (* Environmental Information *)
| ADDRESS
| BALANCE
| ORIGIN
| CALLER
| CALLVALUE
| CALLDATALOAD
| CALLDATASIZE
| CALLDATACOPY
| CODESIZE
| CODECOPY
| GASPRICE
| EXTCODESIZE
| EXTCODECOPY
    (* Block Information *)
| BLOCKHASH
| COINBASE
| TIMESTAMP
| NUMBER
| DIFFICULTY
| GASLIMIT
    (* Stack, memory, storage and flow controls *)
| POP
| MLOAD
| MSTORE
| MSTORE8
| SLOAD
| SSTORE
| JUMP
| JUMPI
| PC
| MSIZE
| GAS
| JUMPDEST
    (* Push operations *)
| PUSHN : nat -> Instr
    (* Duplication operations *)
| DUPN : nat -> Instr
    (* Exchange Operations *)
| SWAPN : nat -> Instr
                   (* Logging Operations *)
| LOGN : nat -> Instr
                  (* System Operations *)
| CREATE
| CALL
| CALLCODE
| RETURN
| DELEGATECALL
| SUCIDE.

    
    

