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
      m_ere : EREnvironment;
      m_storage : Storage
    }.
(*=End *)


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
    | Some next_stack => (None, mkEVMachine s1.(g) (incB s1.(pc)) s1.(m) s1.(i) next_stack s1.(m_ere) s1.(m_storage))
  end.

Definition eval_MUL (s1 : EVMachine) : (option EVMException) * EVMachine :=

  let ores := @mul2top s1.(s) in
  match ores with
    | None => (Some StackUnderflow, s1)
    | Some next_stack => (None, mkEVMachine s1.(g) (incB s1.(pc)) s1.(m) s1.(i) next_stack s1.(m_ere) s1.(m_storage))
  end.

Definition eval_SUB (s1 : EVMachine) : (option EVMException) * EVMachine :=

  let ores := @sub2top s1.(s) in
  match ores with
    | None => (Some StackUnderflow, s1)
    | Some next_stack => (None, mkEVMachine s1.(g) (incB s1.(pc)) s1.(m) s1.(i) next_stack s1.(m_ere) s1.(m_storage))
  end.

Definition eval_DIV (s1 : EVMachine) : (option EVMException) * EVMachine :=

  let ores := @div2top s1.(s) in
  match ores with
    | None => (Some StackUnderflow, s1)
    | Some next_stack => (None, mkEVMachine s1.(g) (incB s1.(pc)) s1.(m) s1.(i) next_stack s1.(m_ere) s1.(m_storage))
  end.

(* TODO: SDIV, MOD, SMOD, ADDMOD, MULMOD, EXP, SIGMEXTENDED *)


(*-----------------------------------------------------------------------------
 Comparison amd bitwise logic operations.
 -----------------------------------------------------------------------------*)
Definition eval_LT (s1 : EVMachine) : (option EVMException) * EVMachine :=
  let ores := @lt2top s1.(s) in
  match ores with
    | None => (Some StackUnderflow, s1)
    | Some next_stack => (None, mkEVMachine s1.(g) (incB s1.(pc)) s1.(m) s1.(i) next_stack s1.(m_ere) s1.(m_storage))
  end.


Definition eval_ISZERO (s1 : EVMachine) : (option EVMException) * EVMachine :=
  let ores := @isZero s1.(s) in
  match ores with
    | None => (Some StackUnderflow, s1)
    | Some next_stack => (None, mkEVMachine s1.(g) (incB s1.(pc)) s1.(m) s1.(i) next_stack s1.(m_ere) s1.(m_storage))
  end.


(*-----------------------------------------------------------------------------
 SHA3.
 -----------------------------------------------------------------------------*)

(*-----------------------------------------------------------------------------
 Environment information.
 -----------------------------------------------------------------------------*)

(*-----------------------------------------------------------------------------
 Block information.
 -----------------------------------------------------------------------------*)

(*-----------------------------------------------------------------------------
 Stack, memory, storage, amd flow operations.
 -----------------------------------------------------------------------------*)

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
(*Fixpoint EVMExecution (s0 : EVMachine) : (option EVMException) * EVMachine :=*)
  
