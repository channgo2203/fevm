(*=================================================================================
 The Ethereum Virtual Machine
 =================================================================================*)


Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrfun ssrbool eqtype ssrnat seq fintype finfun tuple zmodp.

Require Import exceptions bitsrep bitsops cursor pmap reader writer mem stack storage instr program ere.


Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.


(*=EVM *)
Record EVMachine :=
  mkEVMachine {
      (* EVM state *)
      g : EVMWORD;
      pc : EVMWORD;
      m :> Mem;
      (* number of active memory words *)
      i : EVMWORD;
      s :> Stack;
      (* external environment *)
      ere : EREnvironment;
      sto : Storage;
      (* output *)
      output : seq BYTE
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
              initialStorage
              nil.

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
              s1.(sto)
              s1.(output).

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
              s1.(sto)
              s1.(output).


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
              s1.(sto)
              s1.(output).


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
              s1.(sto)
              s1.(output).


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
              s1.(sto)
              s1.(output).


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
              s1.(sto)
              s1.(output).


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
              newStorage
              s1.(output).

(*-----------------------------------------------------------------------------
 Update output.
 -----------------------------------------------------------------------------*)
Definition updateOutput (newOutput : seq BYTE) (s1 : EVMachine) : EVMachine :=
  mkEVMachine s1.(g)
                   s1.(pc)
                        s1.(m)
                             s1.(i)
                                  s1.(s)
                                       s1.(ere)
                                            s1.(sto)
                                                 newOutput.


(*-----------------------------------------------------------------------------
 Check the pc is 0 
 -----------------------------------------------------------------------------*)
Definition is_ZeroPC (s : EVMachine) : bool := (isZeroB s.(pc)).

(*-----------------------------------------------------------------------------
 Get the first instruction
 -----------------------------------------------------------------------------*)
Definition first_Instr (s : EVMachine) : option Instr :=
  match (getCodeAt (#0 : EVMWORD) s.(ere).(Ib)) with
    | None => None
    | Some b => Some (BYTEToOpCode b)
  end.

(*-----------------------------------------------------------------------------
 Get next instruction
 -----------------------------------------------------------------------------*)
Definition next_Instr (s : EVMachine) : option Instr :=
  match (getCodeAt s.(pc) s.(ere).(Ib)) with
    | None => None
    | Some b => Some (BYTEToOpCode b)
  end.

(*-----------------------------------------------------------------------------
 Load the code to be executed into ERE.
 [s] is bytecode compiled from the compiler in Hexadecimal string. If s is not 
 well-formed program then throw an exception and revert to original state [m].
 -----------------------------------------------------------------------------*)
Require Import Coq.Strings.String.
Import Ascii.

Definition loadProgram (s : string) (m : EVMachine) : (option EVMException) * EVMachine :=
  match (hexToProgram s) with
    | (Some e, _) => (Some e, m)
    | (None_, p) => (None, (updateERE (updateIb p m.(ere)) m))
  end.


(*-----------------------------------------------------------------------------
 Ethereum Virtual Machine (EVM) layout to string.
 -----------------------------------------------------------------------------*)
Require Import Coq.Strings.String.
Import Ascii.

Definition evmtoString (evms : EVMachine) :=
  (
    "(Gas available: " ++ toHex evms.(g) ++

    ",PC: " ++ toHex evms.(pc) ++

    ",Memory: " ++ memtoString evms.(m) ++

    ",Active Memory: " ++ toHex evms.(i) ++

    ",Stack: " ++ stacktoString evms.(s) ++

    ",External Running Environment: " ++ eretoString evms.(ere) ++
 
    ",Storage: " ++ storagetoString evms.(sto) ++ ")"
  )%string.


(*----------------------------------------------------------------------------
 EVM Operations provided that the program is well-formed.
 Evaluating each instruction will make the machine to take the corresponding 
 transition from one state to the next state.
 ----------------------------------------------------------------------------*)

Definition eval_STOP (s1 : EVMachine) : (option EVMException) * EVMachine :=
  (None, s1).

Definition eval_ADD (s1 : EVMachine) : (option EVMException) * EVMachine :=
  match add2top s1.(s) with
    | None => (Some StackUnderflow, s1)
    | Some next_s => (None, updatePC (incB s1.(pc)) (updateStack next_s s1))
  end.

Definition eval_MUL (s1 : EVMachine) : (option EVMException) * EVMachine :=
  match mul2top s1.(s) with
    | None => (Some StackUnderflow, s1)
    | Some next_s => (None, updatePC (incB s1.(pc)) (updateStack next_s s1))
  end.

Definition eval_SUB (s1 : EVMachine) : (option EVMException) * EVMachine :=
  match sub2top s1.(s) with
    | None => (Some StackUnderflow, s1)
    | Some next_s => (None, updatePC (incB s1.(pc)) (updateStack next_s s1))
  end.

Definition eval_DIV (s1 : EVMachine) : (option EVMException) * EVMachine :=
  match div2top s1.(s) with
    | None => (Some StackUnderflow, s1)
    | Some next_s => (None, updatePC (incB s1.(pc)) (updateStack next_s s1))
  end.

Definition eval_LT (s1 : EVMachine) : (option EVMException) * EVMachine :=
  match lt2top s1.(s) with
    | None => (Some StackUnderflow, s1)
    | Some next_s => (None, updatePC (incB s1.(pc)) (updateStack next_s s1))
  end.

Definition eval_ISZERO (s1 : EVMachine) : (option EVMException) * EVMachine :=
  match isZero s1.(s) with
    | None => (Some StackUnderflow, s1)
    | Some next_s => (None, updatePC (incB s1.(pc)) (updateStack next_s s1))
  end.

Definition eval_NOT (s1 : EVMachine) : (option EVMException) * EVMachine :=
  match notTop s1.(s) with  
    | None => (Some StackUnderflow, s1)
    | Some next_s => (None, updatePC (incB s1.(pc)) (updateStack next_s s1))
  end.

  
Definition eval_CALLDATALOAD (s1 : EVMachine) : (option EVMException) * EVMachine :=
  match peek s1.(s) with
    | None => (Some StackUnderflow, s1)
    | Some pos => let i := toNat pos in
                  let Id := s1.(ere).(Id) in
                  if (size Id) < (i + 31) then
                    (None, updatePC (incB s1.(pc)) (updateStack (replace_top (#0 : EVMWORD) s1.(s)) s1))
                  else
                    let dataword := rev (take 32 (drop i Id)) in
                    let evmw := lowWithZeroExtendToEVMWORD (fromBytes dataword) in
                    (None, updatePC (incB s1.(pc)) (updateStack (replace_top evmw s1.(s)) s1))
  end.

Definition eval_CALLDATASIZE (s1 : EVMachine) : (option EVMException) * EVMachine :=
  (None, updatePC (incB s1.(pc)) (updateStack (pushEVMWORD (fromNat (size s1.(ere).(Id)) : EVMWORD) s1.(s)) s1)).

Definition eval_SLOAD (s1 : EVMachine) : (option EVMException) * EVMachine :=
  match peek s1.(s) with
    | None => (Some StackUnderflow, s1)
    | Some pos => let readRes := readStorageEVMWORD s1.(sto) pos in
                  match readRes with
                    | readerOk x q => (None, updatePC (incB s1.(pc)) (updateStack (replace_top x s1.(s)) s1))
                    | _ => (None, updatePC (incB s1.(pc)) (updateStack (replace_top (#0 : EVMWORD) s1.(s)) s1))
                  end
  end.

Definition eval_SSTORE (s1 : EVMachine) : (option EVMException) * EVMachine :=
  match s1.(s) with
    | x1::x2::t => match writeStorageEVMWORD s1.(sto) x1 x2 with
                     | None => (Some OutOfRange, s1)
                     | Some (p, next_sto) => (None, updatePC (incB s1.(pc)) (updateStorage next_sto (updateStack (popEVMWORD (popEVMWORD s1.(s))) s1)))
                   end
    | _ => (Some StackUnderflow, s1)
  end.

Definition eval_JUMPI (s1 : EVMachine) : (option EVMException) * EVMachine :=
  match s1.(s) with
    | x1::x2::t => if (isZeroB x2) then (None, updatePC (incB s1.(pc)) s1)
                   else
                     if (size s1.(ere).(Ib)) <= (toNat x1) then
                       (Some BadJumpDestination, s1)
                     else
                       (None, updatePC x1 (updateStack (popEVMWORD (popEVMWORD s1.(s))) s1))
    | _ => (Some StackUnderflow, s1)
  end.

(* It should be that JUMPDEST instruction is a destination of a JUMPI instruction *)
Definition eval_JUMPDEST (s1 : EVMachine) : (option EVMException) * EVMachine :=
  (None, updatePC (incB s1.(pc)) s1).

(* The read tuple of BYTEs need to be reversed due to big edian *)
Definition eval_PUSHn (n : nat) (s1 : EVMachine) : (option EVMException) * EVMachine :=
  let pro := s1.(ere).(Ib) in
  if (size pro) <= (toNat s1.(pc)) + n then
    (None, updatePC (addB s1.(pc) (#(n + 1) : EVMWORD)) (updateStack (pushEVMWORD (#0 : EVMWORD) s1.(s)) s1))
  else
    let data := rev (take n (drop ((toNat s1.(pc)) + 1) pro)) in
    let evmw := lowWithZeroExtendToEVMWORD (fromBytes data) in 
    (None, updatePC (addB s1.(pc) (#(n + 1) : EVMWORD)) (updateStack (pushEVMWORD evmw s1.(s)) s1)).


Definition eval_Instr (i : Instr) (s1 : EVMachine) : (option EVMException) * EVMachine :=
  match i with 
    (* Arithmetic operations *)
    | ADD => eval_ADD s1
                      
    | MUL => eval_MUL s1

    | SUB => eval_SUB s1
                      
    | DIV => eval_DIV s1
                      
    (* Comparison and bitwise logic operations *)
    | LT => eval_LT s1
                    
    | ISZERO => eval_ISZERO s1
                            
    | NOT => eval_NOT s1
                           
    (* SH3 *)
    (* Environment information *)
    | CALLDATALOAD => eval_CALLDATALOAD s1
                                        
    | CALLDATASIZE => eval_CALLDATASIZE s1
                        
    (* Block information *)
    (* Stack, memory, storage and flow operations *)
    | SLOAD => eval_SLOAD s1

    | SSTORE => eval_SSTORE s1
                            
    | JUMPI => eval_JUMPI s1

    | JUMPDEST => eval_JUMPDEST s1
                                
                          
    (* Push operations *)
    | PUSH1 => eval_PUSHn 1 s1
    | PUSH2 => eval_PUSHn 2 s1
    | PUSH3 => eval_PUSHn 3 s1
    | PUSH4 => eval_PUSHn 4 s1
    | PUSH5 => eval_PUSHn 5 s1
    | PUSH6 => eval_PUSHn 6 s1
    | PUSH7 => eval_PUSHn 7 s1
    | PUSH8 => eval_PUSHn 8 s1
    | PUSH9 => eval_PUSHn 9 s1
    | PUSH10 => eval_PUSHn 10 s1
    | PUSH11 => eval_PUSHn 11 s1
    | PUSH12 => eval_PUSHn 12 s1
    | PUSH13 => eval_PUSHn 13 s1
    | PUSH14 => eval_PUSHn 14 s1
    | PUSH15 => eval_PUSHn 15 s1
    | PUSH16 => eval_PUSHn 16 s1
    | PUSH17 => eval_PUSHn 17 s1
    | PUSH18 => eval_PUSHn 18 s1
    | PUSH19 => eval_PUSHn 19 s1
    | PUSH20 => eval_PUSHn 20 s1
    | PUSH21 => eval_PUSHn 21 s1
    | PUSH22 => eval_PUSHn 22 s1
    | PUSH23 => eval_PUSHn 23 s1
    | PUSH24 => eval_PUSHn 24 s1
    | PUSH25 => eval_PUSHn 25 s1
    | PUSH26 => eval_PUSHn 26 s1
    | PUSH27 => eval_PUSHn 27 s1
    | PUSH28 => eval_PUSHn 28 s1
    | PUSH29 => eval_PUSHn 29 s1
    | PUSH30 => eval_PUSHn 30 s1
    | PUSH31 => eval_PUSHn 31 s1
    | PUSH32 => eval_PUSHn 32 s1
                           
    (* Duplication operations *)
    (* Exchange operations *)
    (* Loging operations *)
    (* System operations *)
                           
    (* STOP or Bad instruction *)
    | _ => (None, s1)
  end.

(*-----------------------------------------------------------------------------
 Number of active memory words
 -----------------------------------------------------------------------------*)

(*-----------------------------------------------------------------------------
 Gas consumed by the current instruction
 -----------------------------------------------------------------------------*)
Definition used_Gas (i : Instr) : nat :=
  match i with
    | STOP => 0
    | _ => 1
  end.

(*-----------------------------------------------------------------------------
 Create a new EVM for message call and contract creation
 -----------------------------------------------------------------------------*)
Definition call_NewEVM (s : EVMachine) : EVMachine :=
  updatePC (#0 : EVMWORD) s.

Definition create_NewEVM (s : EVMachine) : EVMachine :=
  updatePC (#0 : EVMWORD) s.


(*-----------------------------------------------------------------------------
 We define the operational semantics of bytecode programs which iterates 
 the application of eval_Instr over the whole programs.
 Notice that the evaluation decreses on the availabe gas argument.
 -----------------------------------------------------------------------------*)
Fixpoint eval_ProgramAux (gas : nat) (i : Instr) (s : EVMachine) : (option EVMException) * EVMachine :=
  let usedGas := (used_Gas i) - 1 in
  match gas with
      | 0 => (Some OutOfGas, s)
      | S gas' => match i with
                    | STOP => (None, s)
                    | CALL => let new_evm := call_NewEVM s in
                              match (next_Instr new_evm) with
                                | Some call_i => let opt_next_s := eval_ProgramAux (gas' - usedGas) call_i new_evm in
                                                 match opt_next_s with
                                                   | (Some e, _) => (Some e, s)
                                                   | (None, next_s) => eval_ProgramAux (gas' - (gas' - (toNat next_s.(g)))) call_i next_s
                                                 end
                                | None => (None, s)
                              end
                    | _ => match eval_Instr i s with
                             | (Some e, error_s) => (Some e, error_s)
                             | (None, next_s) => match (next_Instr next_s) with
                                                   | Some next_i => eval_ProgramAux (gas' - usedGas) next_i next_s
                                                   | None => (None, next_s)
                                                 end
                           end
             end
  end.

(* For test only *)
Fixpoint seqeval_ProgramAux (pro : Program) (s : EVMachine) : (option EVMException) * EVMachine :=
  match pro with
    | nil => (None, s)
    | i::pro' => match (BYTEToOpCode i) with
                   | STOP => (None, s)
                   | _ => match eval_Instr (BYTEToOpCode i) s with
                            | (Some e, error_s) => (Some e, error_s)
                            | (None, next_s) => seqeval_ProgramAux (drop ((toNat next_s.(pc)) - (toNat s.(pc)) - 1) pro') next_s
                          end
                 end                  
  end.


Definition eval_Program (gas : nat) (s : EVMachine) : (option EVMException) * EVMachine :=
  if (checkwellformedProgram s.(ere).(Ib)) then
    if (is_ZeroPC s) then
      match (first_Instr s) with
        | None => (None, s)
        | Some first_i => eval_ProgramAux gas first_i s
      end
    else
      (Some BadInitialEVM, s)
  else
    (Some BadFormProgram, s).


(* TODO: Program evaluation defined as inductive relation *)
Inductive eval : nat -> EVMachine -> (option EVMException) * EVMachine -> Prop :=
| E_O : forall s, eval 0 s (Some OutOfGas, s)
| E_n1 : forall n s0 s1 s2, (eval n s0 (None, s1)) -> (eval (toNat s1.(g)) s1 (None, s2)) -> (eval n s0 (None, s2)).

(* Small-step evaluation relation *)


(*------------------------------------------------------------------------------
 Unit tests.
 ------------------------------------------------------------------------------*)

Example hexpro1 := "6000355419600957005B60203560003555"%string.
Example pro1 := hexToProgram hexpro1.
Example Id := [::
               (#0:BYTE); (#0:BYTE); (#0:BYTE); (#0:BYTE); (#0:BYTE); (#0:BYTE); (#0:BYTE); (#0:BYTE);
               (#0:BYTE); (#0:BYTE); (#0:BYTE); (#0:BYTE); (#0:BYTE); (#0:BYTE); (#0:BYTE); (#0:BYTE);
               (#0:BYTE); (#0:BYTE); (#0:BYTE); (#0:BYTE); (#0:BYTE); (#0:BYTE); (#0:BYTE); (#0:BYTE);
               (#0:BYTE); (#0:BYTE); (#0:BYTE); (#0:BYTE); (#0:BYTE); (#0:BYTE); (#0:BYTE); (#54:BYTE); 
               (#0:BYTE); (#0:BYTE); (#0:BYTE); (#0:BYTE); (#0:BYTE); (#0:BYTE); (#0:BYTE); (#0:BYTE);
               (#0:BYTE); (#0:BYTE); (#0:BYTE); (#0:BYTE); (#0:BYTE); (#0:BYTE); (#0:BYTE); (#0:BYTE);
               (#0:BYTE); (#0:BYTE); (#0:BYTE); (#0:BYTE); (#0:BYTE); (#0:BYTE); (#0:BYTE); (#0:BYTE);
               (#0:BYTE); (#0:BYTE); (#0:BYTE); (#0:BYTE); (#120:BYTE); (#105:BYTE); (#214:BYTE); (#36:BYTE)].

Example s0 := match pro1 with
                | (Some e, _) => updateERE (updateId Id initialERE) initialEVM
                | (None, p) => updateERE (updateIb p (updateId Id initialERE)) initialEVM
              end.

Compute ( evmtoString s0).
  
Compute (
    match pro1 with
      | (Some e, _) => exceptionToString e
      | (None, p) => assemblyDecoder p
    end
  ).


Example finalState := eval_Program 100 s0.

Compute (
    match finalState with
      | (Some e, _) => exceptionToString e
      | (None, s) => evmtoString s
    end
  ).

