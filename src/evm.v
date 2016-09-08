(*=================================================================================
 The Ethereum Virtual Machine
 =================================================================================*)


Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrfun ssrbool eqtype ssrnat seq fintype finfun tuple zmodp.

Require Import bitsrep bitsops cursor pmap reader writer mem stack storage instr program ere.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(*= EVM Exception *)
Inductive EVMException :=
| BreakPointHit
| BadInstruction
| BadJumpDestination
| OutOfGas
| OutOfStack
| StackUnderflow.
(*=End *)

(*=EVM *)
Record EVMachine :=
  mkEVMachine {
      (* EVM state *)
      g : EVMWORD;
      pc : EVMWORD;
      m :> Mem;
      i : EVMWORD;
      s :> Stack;
      (* external environment *)
      ere : EREnvironment;
      sto : Storage
    }.
(*=End *)

(*----------------------------------------------------------------------------
 Initialize the EVM.
 ----------------------------------------------------------------------------*)
Definition initialEVM : EVMachine :=
  mkEVMachine (#0 : EVMWORD)
              (#0 : EVMWORD)
              initialMemory
              (#0 : EVMWORD)
              initialStack
              initialERE
              initialStorage.

(*----------------------------------------------------------------------------
 Update available gas.
 ----------------------------------------------------------------------------*)
Definition updateGas (newGas : EVMWORD) (s1 : EVMachine) : EVMachine :=
  mkEVMachine newGas
              s1.(pc)
              s1.(m)
              s1.(i)
              s1.(s)
              s1.(ere)
              s1.(sto).


(*----------------------------------------------------------------------------
 Update PC.
 ----------------------------------------------------------------------------*)
Definition updatePC (newPC : EVMWORD) (s1 : EVMachine) : EVMachine :=
  mkEVMachine s1.(g)
              newPC
              s1.(m)
              s1.(i)
              s1.(s)
              s1.(ere)
              s1.(sto).


(*----------------------------------------------------------------------------
 Update memory.
 ----------------------------------------------------------------------------*)
Definition updateMem (newMem : Mem) (s1 : EVMachine) : EVMachine :=
  mkEVMachine s1.(g)
              s1.(pc)
              newMem
              s1.(i)
              s1.(s)
              s1.(ere)
              s1.(sto).


(*----------------------------------------------------------------------------
 Update active memory.
 ----------------------------------------------------------------------------*)
Definition updateActiveMem (newActiveMem : EVMWORD) (s1 : EVMachine) : EVMachine :=
  mkEVMachine s1.(g)
              s1.(pc)
              s1.(m)
              newActiveMem
              s1.(s)
              s1.(ere)
              s1.(sto).


(*----------------------------------------------------------------------------
 Update stack.
 ----------------------------------------------------------------------------*)
Definition updateStack (newStack : Stack) (s1 : EVMachine) : EVMachine :=
  mkEVMachine s1.(g)
              s1.(pc)
              s1.(m)
              s1.(i)
              newStack
              s1.(ere)
              s1.(sto).


(*----------------------------------------------------------------------------
 Update ERE.
 ----------------------------------------------------------------------------*)
Definition updateERE (newERE : EREnvironment) (s1 : EVMachine) : EVMachine :=
  mkEVMachine s1.(g)
              s1.(pc)
              s1.(m)
              s1.(i)
              s1.(s)
              newERE
              s1.(sto).


(*----------------------------------------------------------------------------
 Update Storage.
 ----------------------------------------------------------------------------*)
Definition updateStorage (newStorage : Storage) (s1 : EVMachine) : EVMachine :=
  mkEVMachine s1.(g)
              s1.(pc)
              s1.(m)
              s1.(i)
              s1.(s)
              s1.(ere)
              newStorage.


(*----------------------------------------------------------------------------
 Stop.
 ----------------------------------------------------------------------------*)
Definition eval_STOP (s1 : EVMachine) : (option EVMException) * EVMachine :=
  (None, s1).

(*---------------------------------------------------------------------------
 Arithmetic operations.
 ---------------------------------------------------------------------------*)
Definition eval_ADD (s1 : EVMachine) : (option EVMException) * EVMachine :=
  
  let ores := @add2top s1.(s) in
  match ores with
    | None => (Some StackUnderflow, s1)
    | Some next_stack => (None, updatePC (incB s1.(pc)) (updateStack next_stack s1))
  end.

Definition eval_MUL (s1 : EVMachine) : (option EVMException) * EVMachine :=

  let ores := @mul2top s1.(s) in
  match ores with
    | None => (Some StackUnderflow, s1)
    | Some next_stack => (None, updatePC (incB s1.(pc)) (updateStack next_stack s1))
  end.

Definition eval_SUB (s1 : EVMachine) : (option EVMException) * EVMachine :=

  let ores := @sub2top s1.(s) in
  match ores with
    | None => (Some StackUnderflow, s1)
    | Some next_stack => (None, updatePC (incB s1.(pc)) (updateStack next_stack s1))
  end.

Definition eval_DIV (s1 : EVMachine) : (option EVMException) * EVMachine :=

  let ores := @div2top s1.(s) in
  match ores with
    | None => (Some StackUnderflow, s1)
    | Some next_stack => (None, updatePC (incB s1.(pc)) (updateStack next_stack s1))
  end.

(* TODO: SDIV, MOD, SMOD, ADDMOD, MULMOD, EXP, SIGMEXTENDED *)


(*-----------------------------------------------------------------------------
 Comparison amd bitwise logic operations.
 -----------------------------------------------------------------------------*)
Definition eval_LT (s1 : EVMachine) : (option EVMException) * EVMachine :=
  let ores := @lt2top s1.(s) in
  match ores with
    | None => (Some StackUnderflow, s1)
    | Some next_stack => (None, updatePC (incB s1.(pc)) (updateStack next_stack s1))
  end.


Definition eval_ISZERO (s1 : EVMachine) : (option EVMException) * EVMachine :=
  let ores := @isZero s1.(s) in
  match ores with
    | None => (Some StackUnderflow, s1)
    | Some next_stack => (None, updatePC (incB s1.(pc)) (updateStack next_stack s1))
  end.


(*-----------------------------------------------------------------------------
 SHA3.
 -----------------------------------------------------------------------------*)

(*-----------------------------------------------------------------------------
 Environment information.
 -----------------------------------------------------------------------------*)
Definition eval_CALLDATALOAD (s1 : EVMachine) : (option EVMException) * EVMachine :=
  let oindex := peek s1.(s) in
  match oindex with
    | None => (Some StackUnderflow, s1)
    | Some i => let index := toNat i in 
                let Id := s1.(ere).(Id) in
                if (size Id) < (index + 31) then
                  (None, updatePC (incB s1.(pc)) (updateStack (replace_top (#0 : EVMWORD) s1.(s)) s1))
                else
                  (* Get a word at [index] to [index + 31] in Id *)
                  let dataword := take (index + 31) (drop (index - 1) Id) in
                  let evmw := lowWithZeroExtendToEVMWORD (fromBytes dataword) in
                  (None, updatePC (incB s1.(pc)) (updateStack (replace_top evmw s1.(s)) s1))
  end.

Definition eval_CALLDATASIZE (s1 : EVMachine) : (option EVMException) * EVMachine :=
  (None, updatePC (incB s1.(pc))
                  (updateStack (pushEVMWORD s1.(s) (fromNat (size s1.(ere).(Id)) : EVMWORD)) s1)
  ).

(*-----------------------------------------------------------------------------
 Block information.
 -----------------------------------------------------------------------------*)

(*-----------------------------------------------------------------------------
 Stack, memory, storage, amd flow operations.
 -----------------------------------------------------------------------------*)
(*Definition eval_PUSH1 (s1 : EVMachine) : (option EVMException) * EVMachine :=
 *)

(*-----------------------------------------------------------------------------
 Push operations.
 -----------------------------------------------------------------------------*)

(*-----------------------------------------------------------------------------
 Duplication operations.
 -----------------------------------------------------------------------------*)

(*-----------------------------------------------------------------------------
 Exchange operations.
 -----------------------------------------------------------------------------*)

(*-----------------------------------------------------------------------------
 Loging operations.
 -----------------------------------------------------------------------------*)

(*-----------------------------------------------------------------------------
 System operations.
 -----------------------------------------------------------------------------*)


(*-----------------------------------------------------------------------------
 Operational Semantics of the EVM.
 The evaluation of the bytecode included in [m_ere] takes the [s0] and 
 results the final state or exception.
 If there exits any exception, the final state is the initialized state.
 -----------------------------------------------------------------------------*)
(*
Fixpoint EVMExecution (s0 : EVMachine) : (option EVMException) * EVMachine :=
*)
  

(*-----------------------------------------------------------------------------
 Ethereum Virtual Machine (EVM) layout to string.
 -----------------------------------------------------------------------------*)
