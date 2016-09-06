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
  let current_ere := s1.(m_ere) in
  let current_stack := s1.(s) in
  let ores := @add2top current_stack in
  match ores with
    | None => (Some StackUnderflow, s1)
    | Some next_stack => (None, mkEVMachine s1.(g) (incB s1.(pc)) s1.(m) s1.(i) next_stack s1.(m_ere) s1.(m_storage))
  end.




(*-----------------------------------------------------------------------------
 Operational Semantics of the EVM.
 The evaluation of the bytecode included in [m_ere] takes the [initState] and 
 results the final state or exception.
 If there exits any exception, the final state is the initialized state.
 -----------------------------------------------------------------------------*)
(*Fixpoint EVMEvaluation (initState : EVMachine) : (option EVMException) * EVMachine :=
*)
  
