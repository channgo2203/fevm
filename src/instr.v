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
| GETBYTE
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
| PUSH1
| PUSH2
| PUSH3
| PUSH4
| PUSH5
| PUSH6
| PUSH7
| PUSH8
| PUSH9
| PUSH10
| PUSH11
| PUSH12
| PUSH13
| PUSH14
| PUSH15
| PUSH16
| PUSH17
| PUSH18
| PUSH19
| PUSH20
| PUSH21
| PUSH22
| PUSH23
| PUSH24
| PUSH25
| PUSH26
| PUSH27
| PUSH28
| PUSH29
| PUSH30
| PUSH31
| PUSH32
    (* Duplication operations *)
| DUP1
| DUP2
| DUP3
| DUP4
| DUP5
| DUP6
| DUP7
| DUP8
| DUP9
| DUP10
| DUP11
| DUP12
| DUP13
| DUP14
| DUP15
| DUP16
    (* Exchange Operations *)
| SWAP1
| SWAP2
| SWAP3
| SWAP4
| SWAP5
| SWAP6
| SWAP7
| SWAP8
| SWAP9
| SWAP10
| SWAP11
| SWAP12
| SWAP13
| SWAP14
| SWAP15
| SWAP16
    (* Logging Operations *)
| LOG0
| LOG1
| LOG2
| LOG3
| LOG4
    (* System Operations *)
| CREATE
| CALL
| CALLCODE
| RETURN
| DELEGATECALL
| SUCIDE
| BADINSTR.

    
(* From nat to Instr *)
Definition fromNatToInstr (n : nat) : Instr :=
  match n with
    | 0 => STOP
    | 1 => ADD
    | 2 => MUL
    | 3 => SUB
    | 4 => DIV
    | 5 => SDIV
    | 6 => MOD
    | 7 => SMOD
    | 8 => ADDMOD
    | 9 => MULMOD
    | 10 => EXP
    | 11 => SIGNEXTEND
    (* Comparison and bitwise logic operations *)
    | 16 => LT
    | 17 => GT
    | 18 => SLT
    | 19 => SGT
    | 20 => EQ
    | 21 => ISZERO
    | 22 => AND
    | 23 => OR
    | 24 => XOR
    | 25 => NOT
    | 26 => GETBYTE
    (* SHA3 *)
    | 32 => SHA3
    (* Environmental Information *)
    | 48 => ADDRESS
    | 49 => BALANCE
    | 50 => ORIGIN
    | 51 => CALLER
    | 52 => CALLVALUE
    | 53 => CALLDATALOAD
    | 54 => CALLDATASIZE
    | 55 => CALLDATACOPY
    | 56 => CODESIZE
    | 57 => CODECOPY
    | 58 => GASPRICE
    | 59 => EXTCODESIZE
    | 60 => EXTCODECOPY
    (* Block Information *)
    | 64 => BLOCKHASH
    | 65 => COINBASE
    | 66 => TIMESTAMP
    | 67 => NUMBER
    | 68 => DIFFICULTY
    | 69 => GASLIMIT
    (* Stack, memory, storage and flow controls *)
    | 80 => POP
    | 81 => MLOAD
    | 82 => MSTORE
    | 83 =>MSTORE8
    | 84 => SLOAD
    | 85 => SSTORE
    | 86 => JUMP
    | 87 => JUMPI
    | 88 => PC
    | 89 => MSIZE
    | 90 => GAS
    | 91 =>JUMPDEST
    (* Push operations *)
    | 96 => PUSH1
    | 97 => PUSH2
    | 98 => PUSH3
    | 99 => PUSH4
    | 100 => PUSH5
    | 101 => PUSH6
    | 102 => PUSH7
    | 103 => PUSH8
    | 104 => PUSH9
    | 105 => PUSH10
    | 106 => PUSH11
    | 107 => PUSH12
    | 108 => PUSH13
    | 109 => PUSH14
    | 110 => PUSH15
    | 111 => PUSH16
    | 112 => PUSH17
    | 113 => PUSH18
    | 114 => PUSH19
    | 115 => PUSH20
    | 116 => PUSH21
    | 117 => PUSH22
    | 118 => PUSH23
    | 119 => PUSH24
    | 120 => PUSH25
    | 121 => PUSH26
    | 122 => PUSH27
    | 123 => PUSH28
    | 124 => PUSH29
    | 125 => PUSH30
    | 126 => PUSH31
    | 127 => PUSH32
    (* Duplication operations *)
    | 128 => DUP1
    | 129 => DUP2
    | 130 => DUP3
    | 131 => DUP4
    | 132 => DUP5
    | 133 => DUP6
    | 134 => DUP7
    | 135 => DUP8
    | 136 => DUP9
    | 137 => DUP10
    | 138 => DUP11
    | 139 => DUP12
    | 140 => DUP13
    | 141 => DUP14
    | 142 => DUP15
    | 143 => DUP16
    (* Exchange Operations *)
    | 144 => SWAP1
    | 145 => SWAP2
    | 146 => SWAP3
    | 147 => SWAP4
    | 148 => SWAP5
    | 149 => SWAP6
    | 150 => SWAP7
    | 151 => SWAP8
    | 152 => SWAP9
    | 153 => SWAP10
    | 154 => SWAP11
    | 155 => SWAP12
    | 156 => SWAP13
    | 157 => SWAP14
    | 158 => SWAP15
    | 159 => SWAP16
    (* Logging Operations *)
    | 160 => LOG0
    | 161 => LOG1
    | 162 => LOG2
    | 163 => LOG3
    | 164 => LOG4
    (* System Operations *)
    | 240 => CREATE
    | 241 => CALL
    | 242 => CALLCODE
    | 243 => RETURN
    | 244 => DELEGATECALL
    | 255 => SUCIDE            
    | _ => BADINSTR
  end.


