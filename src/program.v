(*=====================================================================
 A program is represented as a list of BYTE.
 Note that the program string (e.g., from the Sodility compiler is 
 represented in BE mode. Our formalization "Program" is sequence of BYTEs 
 that are in LE mode.
 =====================================================================*)

From Coq Require Import ZArith.ZArith Strings.String.

From mathcomp Require Import all_ssreflect.

Require Import common_definitions exceptions bitsops bitsrep instr.


(*=Program *)
Definition Program := seq BYTE.
(*=End *)


(*---------------------------------------------------------------------
 Initilize.
 ---------------------------------------------------------------------*)
Definition initialProgram : Program :=
  nil.


(*--------------------------------------------------------------------
 BYTE to OpCode.
 -------------------------------------------------------------------*)
Definition BYTEToOpCode (b : BYTE) : Instr :=
  fromNatToInstr (toNat b).


(*-------------------------------------------------------------------
 Get BYTE at postion [pc], counting from 0.
 -------------------------------------------------------------------*)
Definition getCodeAt (pc : EVMWORD) (pro : Program) : option BYTE :=
  let n := toNat pc in
  if (size pro) <= n then
    None
  else
    Some (nth (#0 : BYTE) pro n).

           
(*---------------------------------------------------------------------
 Add BYTE to the end of a program.
 ---------------------------------------------------------------------*)
Definition addBYTECode (b : BYTE) (pro : Program) : Program :=
  rcons pro b.
  

(*---------------------------------------------------------------------
 Program decoder: from Hex string to Program.
 ---------------------------------------------------------------------*)
Import Ascii.

(* From BITS n to Program, return None if the given sequence of bits is not divided into sequence of bytes *)
Fixpoint BITStoProgram {n} :=
  match n return BITS n -> Program -> option Program with
    | 0 => fun p pro => Some pro
    | 1 => fun p pro => None
    | 2 => fun p pro => None
    | 3 => fun p pro => None
    | 4 => fun p pro => None
    | 5 => fun p pro => None
    | 6 => fun p pro => None
    | 7 => fun p pro => None
    (* Extract 1 BYTE *)
    | _ => fun p pro => let (hi, lo) := split2 _ 8 p in
                           BITStoProgram hi (addBYTECode lo pro)
  end.



(*---------------------------------------------------------------------
 A program is well-formed if
 + It is a sequence of bytes
 + For any byte that is not data of any PUSH instruction, it must be 
   valid OpCode
 + For any PUSH instruction, the number of bytes data is correct
 ---------------------------------------------------------------------*)
Fixpoint checkwellformedProgramAux (pro : Program) (res : bool) : bool :=
  match pro with
    | nil => res
    | b1::pro1 => let bopcode := BYTEToOpCode b1 in
                  match bopcode with
                    | BADINSTR => false
                    | _ => let i_nat := toNat b1 in
                           if (i_nat > 95) && (i_nat < 128) then
                             if (size pro1) < (i_nat - 95) then
                               false
                             else
                               checkwellformedProgramAux (drop (i_nat - 95) pro1) res
                           else
                             checkwellformedProgramAux pro1 res
                  end
  end.

Definition checkwellformedProgram (pro : Program) :=
  checkwellformedProgramAux pro true.


(* From Hex string to Program *)
Fixpoint hexToProgramAux (s : string) (res : Program) : option Program :=
  match s with
    | EmptyString => Some res
    | String c1 EmptyString => None
    | String c1 (String c2 s) => hexToProgramAux s (addBYTECode (joinNibble (charToNibble c1) (charToNibble c2)) res)
  end.


(* from Hex string to BITS n, then to Program *)
Definition hexToBITS_Program (s : string) : (option EVMException) * Program :=
  match (BITStoProgram (fromHex s) nil) with
    | None => (Some BadFormProgram, nil)
    | Some p => if checkwellformedProgram (rev p) then
                  (None, (rev p))
                else
                  (Some BadFormProgram, nil)
  end.

Definition hexToProgram (s : string) : (option EVMException) * Program :=
  match hexToProgramAux s nil with
    | None => (Some BadFormProgram, nil)
    | Some p => if checkwellformedProgram p  then
                  (None, p)
                else
                  (Some BadFormProgram, nil)
  end.


(*---------------------------------------------------------------------
 Program to string.
 ---------------------------------------------------------------------*)
Fixpoint enumProgramToString (pro : Program) :=
  (if pro is b::pro then
    toHex b ++ " " ++ enumProgramToString pro
  else "")%string.

Definition programToString (pro : Program) :=
  enumProgramToString pro.


(*---------------------------------------------------------------------
 EVM Assembly decoder from binary program to opcode. 
 Notice that the program should be well-formed.
 ---------------------------------------------------------------------*)
Fixpoint assemblyDecorderAux (pro : Program) :=
  (match pro with
    | nil => ""
    | b1::pro1 => let i_nat := toNat b1 in
                  if (i_nat > 95) && (i_nat < 128) then
                    (instrToString (BYTEToOpCode b1)) ++ " " ++ (programToString (take (i_nat - 95) pro1)) ++ assemblyDecorderAux (drop (i_nat - 95) pro1)
                  else
                    (instrToString (BYTEToOpCode b1)) ++ " " ++ assemblyDecorderAux pro1
  end)%string.


Definition assemblyDecoder (pro : Program) :=
  assemblyDecorderAux pro.


(*---------------------------------------------------------------------
 Unit test.
 ---------------------------------------------------------------------*)
Example hexpro1 := "6000355419600957005B60203560003555"%string.

Example pro1 := hexToProgram hexpro1.

Compute (
    match pro1 with
      | (_, nil) => "Ill-formed program"%string
      | (_, p) => programToString p
    end
  ).

Compute (
    match pro1 with
      | (_, nil) => "Ill-formed program"%string
      | (_, p) => assemblyDecoder p
    end
  ).

Example hexpro2 := "6060604052609b8060106000396000f360606040526000357c0100000000000000000000000000000000000000000000000000000000900480632fbff5f3146037576035565b005b605460048080359060200190919080359060200190919050506056565b005b6000600060005060008481526020019081526020016000206000505414156096578060006000506000848152602001908152602001600020600050819055505b5b505056"%string.

Example pro2 := hexToProgram hexpro2.

Compute (
    match pro2 with
      | (_, nil) => "Ill-formed program"%string
      | (_, p) => assemblyDecoder p
    end
  ).

Example badhexpro := hexToProgram "6060604052609b8060106000396000f360606040526000357c010000000000000000"%string.

Compute (
    match badhexpro with
      | (_, nil) => "Ill-formed program"%string
      | (_, p) => assemblyDecoder p
    end
  ).

	
