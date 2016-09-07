(*=====================================================================
 A program is represented as a list of BYTE.
 =====================================================================*)

From Coq Require Import ZArith.ZArith Strings.String.

From mathcomp Require Import all_ssreflect.

Require Import common_definitions bitsops bitsrep instr.


(*=Program *)
Definition Program := seq BYTE.
(*=End *)

(* BYTE to OpCode *)
Definition BYTEToOpCode (b : BYTE) : Instr :=
  fromNatToInstr (toNat b).


(* Get BYTE at postion [pc], counting from 0 *)
Definition getCodeAt (pc : EVMWORD) (pro : Program) : option BYTE :=
  let n := toNat pc in
  if (size pro) < (n + 1) then
    None
  else
    Some (nth (#0 : BYTE) pro n).

           
(* Add BYTE to a program *)
Definition addBYTECode (b : BYTE) (pro : Program) : Program :=
  rcons pro b.
  
(*---------------------------------------------------------------------
 Program decoder: from Hex string to Program.
 ---------------------------------------------------------------------*)
Import Ascii.

(* From BITS n to Program 
   Return None (it is not well-formed) if the given sequence of bits 
   is not divided into sequence of bytes
 *)
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


Definition HexToProgram s : option Program :=
  match (BITStoProgram (fromHex s) nil) with
    | None => None
    | Some p => Some (rev p)
  end.
  

(*---------------------------------------------------------------------
 Check a program is well-formed.
 A program is well-formed if
 + It is a sequence of bytes
 + For any byte that is not data of any PUSH instruction, it must be 
   valid OpCode
 + For any PUSH instruction, the number of bytes data is correct
 ---------------------------------------------------------------------*)


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
 EVM Assembly decoder. Notice that the program should be checked 
 for well-formed one first. 
 From Bytecode to OpCode.
 ---------------------------------------------------------------------*)
(* PUSH decoding. [pro] is the rest of program after PUSH *)
Definition PUSHDecoding (n : nat) (pro : Program) : option (Program * Program) :=
  if (size pro) < n then
    None
  else
    Some ((take n pro), (drop n pro)).

  
Fixpoint enumProgramDecoding (pro : Program) :=
  (if pro is b1::pro1 then
     let i := BYTEToOpCode b1 in
     match i with
       | PUSH1 => match pro1 with
                    | b2::pro2 => (instrToString i) ++ " " ++ (toHex b2) ++ " " ++ enumProgramDecoding pro2
                    | nil => "Ill-formed program"
                  end
                    
       | PUSH2 => match pro1 with
                    | b2::b3::pro3 => (instrToString i) ++ " " ++ (toHex b2) ++ " " ++ (toHex b3) ++ " "  ++ enumProgramDecoding pro3
                    | b2::nil => "Ill-formed program"
                    | nil => "Ill-formed program"
                  end
       | PUSH3 => if (size pro1) < 3 then
                    "Ill-formed program"
                  else
                    (instrToString i) ++ " " ++ (programToString (take 3 pro1)) ++ " " ++ enumProgramDecoding (drop 3 pro1)

       | PUSH4 => if (size pro1) < 4 then
                    "Ill-formed program"
                  else
                    (instrToString i) ++ " " ++ (programToString (take 4 pro1)) ++ " " ++ enumProgramDecoding (drop 4 pro1)

       | PUSH5 => if (size pro1) < 5 then
                    "Ill-formed program"
                  else
                    (instrToString i) ++ " " ++ (programToString (take 5 pro1)) ++ " " ++ enumProgramDecoding (drop 5 pro1)

       | PUSH6 => if (size pro1) < 6 then
                    "Ill-formed program"
                  else
                    (instrToString i) ++ " " ++ (programToString (take 6 pro1)) ++ " " ++ enumProgramDecoding (drop 6 pro1)

       | PUSH3 => if (size pro1) < 3 then
                    "Ill-formed program"
                  else
                    (instrToString i) ++ " " ++ (programToString (take 7 pro1)) ++ " " ++ enumProgramDecoding (drop 7 pro1)

       | PUSH3 => if (size pro1) < 3 then
                    "Ill-formed program"
                  else
                    (instrToString i) ++ " " ++ (programToString (take 8 pro1)) ++ " " ++ enumProgramDecoding (drop 8 pro1)

       | PUSH3 => if (size pro1) < 3 then
                    "Ill-formed program"
                  else
                    (instrToString i) ++ " " ++ (programToString (take 9 pro1)) ++ " " ++ enumProgramDecoding (drop 9 pro1)

       | PUSH3 => if (size pro1) < 3 then
                    "Ill-formed program"
                  else
                    (instrToString i) ++ " " ++ (programToString (take 10 pro1)) ++ " " ++ enumProgramDecoding (drop 10 pro1)

       | PUSH3 => if (size pro1) < 3 then
                    "Ill-formed program"
                  else
                    (instrToString i) ++ " " ++ (programToString (take 11 pro1)) ++ " " ++ enumProgramDecoding (drop 11 pro1)

       | PUSH3 => if (size pro1) < 3 then
                    "Ill-formed program"
                  else
                    (instrToString i) ++ " " ++ (programToString (take 12 pro1)) ++ " " ++ enumProgramDecoding (drop 12 pro1)

       | PUSH3 => if (size pro1) < 3 then
                    "Ill-formed program"
                  else
                    (instrToString i) ++ " " ++ (programToString (take 13 pro1)) ++ " " ++ enumProgramDecoding (drop 13 pro1)
       | PUSH3 => if (size pro1) < 3 then
                    "Ill-formed program"
                  else
                    (instrToString i) ++ " " ++ (programToString (take 14 pro1)) ++ " " ++ enumProgramDecoding (drop 14 pro1)
       | PUSH3 => if (size pro1) < 3 then
                    "Ill-formed program"
                  else
                    (instrToString i) ++ " " ++ (programToString (take 15 pro1)) ++ " " ++ enumProgramDecoding (drop 15 pro1)
       | PUSH3 => if (size pro1) < 3 then
                    "Ill-formed program"
                  else
                    (instrToString i) ++ " " ++ (programToString (take 16 pro1)) ++ " " ++ enumProgramDecoding (drop 16 pro1)
       | PUSH3 => if (size pro1) < 3 then
                    "Ill-formed program"
                  else
                    (instrToString i) ++ " " ++ (programToString (take 17 pro1)) ++ " " ++ enumProgramDecoding (drop 17 pro1)
       | PUSH3 => if (size pro1) < 3 then
                    "Ill-formed program"
                  else
                    (instrToString i) ++ " " ++ (programToString (take 18 pro1)) ++ " " ++ enumProgramDecoding (drop 18 pro1)
       | PUSH3 => if (size pro1) < 3 then
                    "Ill-formed program"
                  else
                    (instrToString i) ++ " " ++ (programToString (take 19 pro1)) ++ " " ++ enumProgramDecoding (drop 19 pro1)
       | PUSH3 => if (size pro1) < 3 then
                    "Ill-formed program"
                  else
                    (instrToString i) ++ " " ++ (programToString (take 3 pro1)) ++ " " ++ enumProgramDecoding (drop 20 pro1)
       | PUSH3 => if (size pro1) < 3 then
                    "Ill-formed program"
                  else
                    (instrToString i) ++ " " ++ (programToString (take 3 pro1)) ++ " " ++ enumProgramDecoding (drop 21 pro1)
       | PUSH3 => if (size pro1) < 3 then
                    "Ill-formed program"
                  else
                    (instrToString i) ++ " " ++ (programToString (take 3 pro1)) ++ " " ++ enumProgramDecoding (drop 22 pro1)
       | PUSH3 => if (size pro1) < 3 then
                    "Ill-formed program"
                  else
                    (instrToString i) ++ " " ++ (programToString (take 3 pro1)) ++ " " ++ enumProgramDecoding (drop 23 pro1)
       | PUSH3 => if (size pro1) < 3 then
                    "Ill-formed program"
                  else
                    (instrToString i) ++ " " ++ (programToString (take 3 pro1)) ++ " " ++ enumProgramDecoding (drop 24 pro1)
       | PUSH3 => if (size pro1) < 3 then
                    "Ill-formed program"
                  else
                    (instrToString i) ++ " " ++ (programToString (take 3 pro1)) ++ " " ++ enumProgramDecoding (drop 25 pro1)
       | PUSH3 => if (size pro1) < 3 then
                    "Ill-formed program"
                  else
                    (instrToString i) ++ " " ++ (programToString (take 3 pro1)) ++ " " ++ enumProgramDecoding (drop 26 pro1)
       | PUSH3 => if (size pro1) < 3 then
                    "Ill-formed program"
                  else
                    (instrToString i) ++ " " ++ (programToString (take 3 pro1)) ++ " " ++ enumProgramDecoding (drop 27 pro1)
       | PUSH28 => if (size pro1) < 28 then
                    "Ill-formed program"
                  else
                    (instrToString i) ++ " " ++ (programToString (take 28 pro1)) ++ " " ++ enumProgramDecoding (drop 28 pro1)
       | PUSH29 => if (size pro1) < 29 then
                    "Ill-formed program"
                  else
                    (instrToString i) ++ " " ++ (programToString (take 29 pro1)) ++ " " ++ enumProgramDecoding (drop 29 pro1)
       | PUSH30 => if (size pro1) < 30 then
                    "Ill-formed program"
                  else
                    (instrToString i) ++ " " ++ (programToString (take 30 pro1)) ++ " " ++ enumProgramDecoding (drop 30 pro1)
       | PUSH31 => if (size pro1) < 31 then
                    "Ill-formed program"
                  else
                    (instrToString i) ++ " " ++ (programToString (take 31 pro1)) ++ " " ++ enumProgramDecoding (drop 31 pro1)
       | PUSH32 => if (size pro1) < 32 then
                    "Ill-formed program"
                  else
                    (instrToString i) ++ " " ++ (programToString (take 32 pro1)) ++ " " ++ enumProgramDecoding (drop 32 pro1)
       
       
       | _ => (instrToString i) ++ " " ++ enumProgramDecoding pro1
     end
   else
     "")%string.


                                     
(*---------------------------------------------------------------------
 Unit test.
 ---------------------------------------------------------------------*)
Example pro1 : Program := [::(#96:BYTE); (#0:BYTE); (#53:BYTE); (#84:BYTE);
                           (#25:BYTE); (#96:BYTE); (#9:BYTE); (#87:BYTE);
                           (#0:BYTE); (#91:BYTE); (#96:BYTE); (#32:BYTE);
                           (#53:BYTE); (#96:BYTE); (#0:BYTE); (#53:BYTE);
                           (#85:BYTE)].

Compute (
    let oInstr := getCodeAt (#2:EVMWORD) pro1 in
    match oInstr with
      | Some b => instrToString (BYTEToOpCode b)
      | None => "Out-Of-Bound"%string 
    end
  ).

Example HexProgram := "6000355419600957005B60203560003555"%string.
Example pro := HexToProgram HexProgram.

Compute (
    match pro with
      | None => "Ill-formed program"%string
      | Some p => programToString p
    end
  ).

Compute (
    match pro with
      | None => "Ill-formed program"%string
      | Some p => enumProgramDecoding p
    end
  ).


	
