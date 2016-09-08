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

(* The trivial implementation. However, it may helps the Proof more efficient *)
(* Fixpoint enumProgramDecoding (pro : Program) :=
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
                    (instrToString i) ++ " " ++ (programToString (take 3 pro1)) ++ enumProgramDecoding (drop 3 pro1)

       | PUSH4 => if (size pro1) < 4 then
                    "Ill-formed program"
                  else
                    (instrToString i) ++ " " ++ (programToString (take 4 pro1)) ++ enumProgramDecoding (drop 4 pro1)

       | PUSH5 => if (size pro1) < 5 then
                    "Ill-formed program"
                  else
                    (instrToString i) ++ " " ++ (programToString (take 5 pro1)) ++ enumProgramDecoding (drop 5 pro1)

       | PUSH6 => if (size pro1) < 6 then
                    "Ill-formed program"
                  else
                    (instrToString i) ++ " " ++ (programToString (take 6 pro1)) ++ enumProgramDecoding (drop 6 pro1)

       | PUSH7 => if (size pro1) < 7 then
                    "Ill-formed program"
                  else
                    (instrToString i) ++ " " ++ (programToString (take 7 pro1)) ++ enumProgramDecoding (drop 7 pro1)

       | PUSH8 => if (size pro1) < 8 then
                    "Ill-formed program"
                  else
                    (instrToString i) ++ " " ++ (programToString (take 8 pro1)) ++ enumProgramDecoding (drop 8 pro1)

       | PUSH9 => if (size pro1) < 9 then
                    "Ill-formed program"
                  else
                    (instrToString i) ++ " " ++ (programToString (take 9 pro1)) ++ enumProgramDecoding (drop 9 pro1)

       | PUSH10 => if (size pro1) < 10 then
                    "Ill-formed program"
                  else
                    (instrToString i) ++ " " ++ (programToString (take 10 pro1)) ++ enumProgramDecoding (drop 10 pro1)

       | PUSH11 => if (size pro1) < 11 then
                    "Ill-formed program"
                  else
                    (instrToString i) ++ " " ++ (programToString (take 11 pro1)) ++ enumProgramDecoding (drop 11 pro1)

       | PUSH12 => if (size pro1) < 12 then
                    "Ill-formed program"
                  else
                    (instrToString i) ++ " " ++ (programToString (take 12 pro1)) ++ enumProgramDecoding (drop 12 pro1)

       | PUSH13 => if (size pro1) < 13 then
                    "Ill-formed program"
                  else
                    (instrToString i) ++ " " ++ (programToString (take 13 pro1)) ++ enumProgramDecoding (drop 13 pro1)
       | PUSH14 => if (size pro1) < 14 then
                    "Ill-formed program"
                  else
                    (instrToString i) ++ " " ++ (programToString (take 14 pro1)) ++ enumProgramDecoding (drop 14 pro1)
       | PUSH15 => if (size pro1) < 15 then
                    "Ill-formed program"
                  else
                    (instrToString i) ++ " " ++ (programToString (take 15 pro1)) ++ enumProgramDecoding (drop 15 pro1)
       | PUSH16 => if (size pro1) < 16 then
                    "Ill-formed program"
                  else
                    (instrToString i) ++ " " ++ (programToString (take 16 pro1)) ++ enumProgramDecoding (drop 16 pro1)
       | PUSH17 => if (size pro1) < 17 then
                    "Ill-formed program"
                  else
                    (instrToString i) ++ " " ++ (programToString (take 17 pro1)) ++ enumProgramDecoding (drop 17 pro1)
       | PUSH18 => if (size pro1) < 18 then
                    "Ill-formed program"
                  else
                    (instrToString i) ++ " " ++ (programToString (take 18 pro1)) ++ enumProgramDecoding (drop 18 pro1)
       | PUSH19 => if (size pro1) < 19 then
                    "Ill-formed program"
                  else
                    (instrToString i) ++ " " ++ (programToString (take 19 pro1)) ++ enumProgramDecoding (drop 19 pro1)
       | PUSH20 => if (size pro1) < 20 then
                    "Ill-formed program"
                  else
                    (instrToString i) ++ " " ++ (programToString (take 20 pro1)) ++ enumProgramDecoding (drop 20 pro1)
       | PUSH21 => if (size pro1) < 21 then
                    "Ill-formed program"
                  else
                    (instrToString i) ++ " " ++ (programToString (take 21 pro1)) ++ enumProgramDecoding (drop 21 pro1)
       | PUSH22 => if (size pro1) < 22 then
                    "Ill-formed program"
                  else
                    (instrToString i) ++ " " ++ (programToString (take 22 pro1)) ++ enumProgramDecoding (drop 22 pro1)
       | PUSH23 => if (size pro1) < 23 then
                    "Ill-formed program"
                  else
                    (instrToString i) ++ " " ++ (programToString (take 23 pro1)) ++ enumProgramDecoding (drop 23 pro1)
       | PUSH24 => if (size pro1) < 24 then
                    "Ill-formed program"
                  else
                    (instrToString i) ++ " " ++ (programToString (take 24 pro1)) ++ enumProgramDecoding (drop 24 pro1)
       | PUSH25 => if (size pro1) < 25 then
                    "Ill-formed program"
                  else
                    (instrToString i) ++ " " ++ (programToString (take 25 pro1)) ++ enumProgramDecoding (drop 25 pro1)
       | PUSH26 => if (size pro1) < 26 then
                    "Ill-formed program"
                  else
                    (instrToString i) ++ " " ++ (programToString (take 26 pro1)) ++ enumProgramDecoding (drop 26 pro1)
       | PUSH27 => if (size pro1) < 27 then
                    "Ill-formed program"
                  else
                    (instrToString i) ++ " " ++ (programToString (take 27 pro1)) ++ enumProgramDecoding (drop 27 pro1)
       | PUSH28 => if (size pro1) < 28 then
                    "Ill-formed program"
                  else
                    (instrToString i) ++ " " ++ (programToString (take 28 pro1)) ++ enumProgramDecoding (drop 28 pro1)
       | PUSH29 => if (size pro1) < 29 then
                    "Ill-formed program"
                  else
                    (instrToString i) ++ " " ++ (programToString (take 29 pro1)) ++ enumProgramDecoding (drop 29 pro1)
       | PUSH30 => if (size pro1) < 30 then
                    "Ill-formed program"
                  else
                    (instrToString i) ++ " " ++ (programToString (take 30 pro1)) ++ enumProgramDecoding (drop 30 pro1)
       | PUSH31 => if (size pro1) < 31 then
                    "Ill-formed program"
                  else
                    (instrToString i) ++ " " ++ (programToString (take 31 pro1)) ++ enumProgramDecoding (drop 31 pro1)
       | PUSH32 => if (size pro1) < 32 then
                    "Ill-formed program"
                  else
                    (instrToString i) ++ " " ++ (programToString (take 32 pro1)) ++ enumProgramDecoding (drop 32 pro1)
       
       
       | _ => (instrToString i) ++ " " ++ enumProgramDecoding pro1
     end
   else
     "")%string.
 *)

Fixpoint enumProgramDecoding (pro : Program) :=
  (if pro is b1::pro1 then
     let i_nat := toNat b1 in
     (* b1 is PUSH instruction *)
     if (i_nat > 95) && (i_nat < 128) then
       if (size pro1) < (i_nat - 95) then
         "Ill-formed program"
       else
         (instrToString (BYTEToOpCode b1)) ++ " " ++ (programToString (take (i_nat - 95) pro1)) ++ enumProgramDecoding (drop (i_nat - 95) pro1)
     (* other instruction *)
     else
       (instrToString (BYTEToOpCode b1)) ++ " " ++ enumProgramDecoding pro1
   else
     "")%string.


Definition AssemblyDecoder (pro : Program) :=
  enumProgramDecoding pro.

                                     
(*---------------------------------------------------------------------
 Unit test.
 ---------------------------------------------------------------------*)


Example hexpro1 := "6000355419600957005B72000000000000000000000000000000000000203560003555"%string.

Example pro1 := HexToProgram hexpro1.

Compute (
    match pro1 with
      | None => "Ill-formed program"%string
      | Some p => programToString p
    end
  ).

Compute (
    match pro1 with
      | None => "Ill-formed program"%string
      | Some p => AssemblyDecoder p
    end
  ).

Example hexpro2 := "6060604052609b8060106000396000f360606040526000357c0100000000000000000000000000000000000000000000000000000000900480632fbff5f3146037576035565b005b605460048080359060200190919080359060200190919050506056565b005b6000600060005060008481526020019081526020016000206000505414156096578060006000506000848152602001908152602001600020600050819055505b5b505056"%string.

Example pro2 := HexToProgram hexpro2.

Compute (
    match pro2 with
      | None => "Ill-formed program"%string
      | Some p => AssemblyDecoder p
    end
  ).


	
