(* Test *)

Require Import String.
Require Import List.
Require Import FMapInterface.
Require Import PeanoNat Even NAxioms.

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrbool.

Module Lang.

  Inductive instr := (** partial.  adding those necessary. *)
  | STOP
  | ADD
  | SUB
  | DIV
  | EXP
  | instr_GT
  | instr_EQ
  | AND
  | ISZERO
  | CALLER
  | CALLVALUE
  | CALLDATALOAD
  | CALLDATASIZE
  | CALLDATACOPY
  | TIMESTAMP
  | POP
  | MLOAD
  | MSTORE
  | SLOAD
  | SSTORE
  | JUMP
  | JUMPI
  | JUMPDEST
  | PUSH_N : string -> instr
  | DUP1
  | DUP2
  | DUP3
  | SWAP1
  | SWAP2
  | RETURN
  | SUICIDE
  .

  Fixpoint string_half_len str :=
    match str with
    | String _ (String _ tl) => S (string_half_len tl)
    | _ => O
    end.

  Definition instr_length (i : instr) : nat :=
    match i with
    | PUSH_N str => string_half_len str
    | _ => 1
    end.

  Fixpoint drop_bytes (prog : list instr) (bytes : nat) {struct bytes} :=
    match prog, bytes with
    | _, O => prog
    | PUSH_N str :: tl, S pre =>
      drop_bytes tl (pre - (string_half_len str - 1))
    | _ :: tl, S pre =>
      drop_bytes tl pre
    | nil, S _ => nil
    end.

  Definition example1 : list instr :=
      PUSH_N "0x60" ::
      PUSH_N "0x40" ::
      MSTORE ::
      PUSH_N "0x00" ::
      CALLDATALOAD ::
      PUSH_N "0x0100000000000000000000000000000000000000000000000000000000" ::
      SWAP1 ::
      DIV ::
      DUP1 ::
      PUSH_N "0x4665096d" ::
      instr_EQ ::
      PUSH_N "0x004f" ::
      JUMPI ::
      DUP1 ::
      PUSH_N "0xbe040fb0" ::
      instr_EQ ::
      PUSH_N "0x0070" ::
      JUMPI ::
      DUP1 ::
      PUSH_N "0xdd467064" ::
      instr_EQ ::
      PUSH_N "0x007d" ::
      JUMPI ::
      PUSH_N "0x004d" ::
      JUMP ::
      JUMPDEST ::
      STOP ::
      JUMPDEST ::
      PUSH_N "0x005a" ::
      PUSH_N "0x04" ::
      POP ::
      PUSH_N "0x00a4" ::
      JUMP ::
      JUMPDEST ::
      PUSH_N "0x40" ::
      MLOAD ::
      DUP1 ::
      DUP3 ::
      DUP2 ::
      MSTORE ::
      PUSH_N "0x20" ::
      ADD ::
      SWAP2 ::
      POP ::
      POP ::
      PUSH_N "0x40" ::
      MLOAD ::
      DUP1 ::
      SWAP2 ::
      SUB ::
      SWAP1 ::
      RETURN ::
      JUMPDEST ::
      PUSH_N "0x007b" ::
      PUSH_N "0x04" ::
      POP ::
      PUSH_N "0x0140" ::
      JUMP ::
      JUMPDEST ::
      STOP ::
      JUMPDEST ::
      PUSH_N "0x008e" ::
      PUSH_N "0x04" ::
      DUP1 ::
      CALLDATALOAD ::
      SWAP1 ::
      PUSH_N "0x20" ::
      ADD ::
      POP ::
      PUSH_N "0x00ad" ::
      JUMP ::
      JUMPDEST ::
      PUSH_N "0x40" ::
      MLOAD ::
      DUP1 ::
      DUP3 ::
      DUP2 ::
      MSTORE :: 
      PUSH_N "0x20" ::
      ADD ::
      SWAP2 ::
      POP ::
      POP ::
      PUSH_N "0x40" ::
      MLOAD ::
      DUP1 ::
      SWAP2 ::
      SUB ::
      SWAP1 ::
      RETURN ::
      JUMPDEST ::
      PUSH_N "0x01" ::
      PUSH_N "0x00" ::
      POP ::
      SLOAD ::
      DUP2 ::
      JUMP ::
      JUMPDEST ::
      PUSH_N "0x00" ::
      PUSH_N "0x00" ::
      PUSH_N "0x00" ::
      SWAP1 ::
      SLOAD ::
      SWAP1 ::
      PUSH_N "0x0100" ::
      EXP ::
      SWAP1 ::
      DIV ::
      PUSH_N "0xffffffffffffffffffffffffffffffffffffffff" ::
      AND ::
      PUSH_N "0xffffffffffffffffffffffffffffffffffffffff" ::
      AND ::
      CALLER ::
      PUSH_N "0xffffffffffffffffffffffffffffffffffffffff" ::
      AND ::
      instr_EQ ::
      ISZERO ::
      PUSH_N "0x013a" ::
      JUMPI ::
      TIMESTAMP ::
      DUP3 ::
      instr_GT ::
      DUP1 ::
      ISZERO ::
      PUSH_N "0x0119" ::
      JUMPI ::
      POP ::
      PUSH_N "0x00" ::
      PUSH_N "0x01" ::
      PUSH_N "0x00" ::
      POP ::
      SLOAD ::
      instr_EQ ::
      JUMPDEST ::
      ISZERO ::
      PUSH_N "0x0131" ::
      JUMPI ::
      DUP2 ::
      PUSH_N "0x01" ::
      PUSH_N "0x00" ::
      POP ::
      DUP2 ::
      SWAP1 ::
      SSTORE ::
      POP ::
      PUSH_N "0x01" ::
      SWAP1 ::
      POP ::
      PUSH_N "0x013b" ::
      JUMP ::
      JUMPDEST ::
      PUSH_N "0x00" ::
      SWAP1 ::
      POP ::
      PUSH_N "0x013b" ::
      JUMP ::
      JUMPDEST ::
      JUMPDEST ::
      SWAP2 ::
      SWAP1 ::
      POP ::
      JUMP ::
      JUMPDEST ::
      PUSH_N "0x00" ::
      PUSH_N "0x00" ::
      SWAP1 ::
      SLOAD ::
      SWAP1 ::
      PUSH_N "0x0100" ::
      EXP ::
      SWAP1 ::
      DIV :: 
      PUSH_N "0xffffffffffffffffffffffffffffffffffffffff" ::
      AND ::
      PUSH_N "0xffffffffffffffffffffffffffffffffffffffff" ::
      AND ::
      CALLER ::
      PUSH_N "0xffffffffffffffffffffffffffffffffffffffff" ::
      AND ::
      instr_EQ ::
      ISZERO ::
      PUSH_N "0x01df" ::
      JUMPI ::
      PUSH_N "0x01" ::
      PUSH_N "0x00" ::
      POP ::
      SLOAD ::
      TIMESTAMP ::
      instr_GT ::
      ISZERO ::
      PUSH_N "0x01de" ::
      JUMPI ::
      PUSH_N "0x00" ::
      PUSH_N "0x00" ::
      SWAP1 ::
      SLOAD ::
      SWAP1 ::
      PUSH_N "0x0100" ::
      EXP ::
      SWAP1 ::
      DIV ::
      PUSH_N "0xffffffffffffffffffffffffffffffffffffffff" ::
      AND ::
      PUSH_N "0xffffffffffffffffffffffffffffffffffffffff" ::
      AND ::
      SUICIDE :: (* here, payout occurs *)
      JUMPDEST ::
      JUMPDEST ::
      JUMPDEST ::
      JUMP :: nil.

End Lang.

Module U256.
  Parameter Inline t : Type.
  Parameter Inline eq : t -> t -> Prop.
  Parameter Inline lt : t -> t -> Prop.

  Axiom eq_refl : forall x : t, eq x x.
  Axiom eq_sym : forall x y : t, eq x y -> eq y x.
  Axiom eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.

  Axiom lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
  Axiom lt_not_eq : forall x y: t, lt x y -> ~ eq x y.

  Parameter compare : forall x y : t, Compare lt eq x y.

  Hint Immediate eq_sym.
  Hint Resolve eq_refl eq_trans lt_not_eq lt_trans.
                                                           
End U256.

  
Module EVM (U256:OrderedType).

  Import Lang.
  Import U256.

  Parameter is_zero : U256.t -> bool.
  Parameter zero : U256.t.
  Parameter one  : U256.t.
  Parameter succ : U256.t -> U256.t.
  Parameter to_nat : U256.t -> nat.
  Parameter sub : U256.t -> U256.t -> U256.t.
  Parameter add : U256.t -> U256.t -> U256.t.
  Parameter and : U256.t -> U256.t -> U256.t.

  Definition stack := list U256.t.

  Require Import FMapList.

  Module Memory := FMapList.Make U256.

  Definition memory := Memory.t U256.t.
  
  Definition m T := option (T * memory).

  Definition operation := stack -> memory -> m stack (* maybe with side-effect? *).

  (* trying to encode
     https://etherchain.org/account/0x10ebb6b1607de9c08c61c6f6044b8edc93b8e9c9#codeDisasm
  *)

  Require Import List.

  Definition push_x (d : U256.t) : operation :=
    fun s mem => Some (d :: s, mem).

  Definition pop : operation :=
    fun s mem =>
      match s with
        | nil => None
        | hd :: tl => Some (tl, mem)
      end.

  Definition mstore : operation :=
    fun s mem =>
      match s with
        | nil => None
        | _ :: nil => None
        | a :: b :: l => Some (l, Memory.add a b (* not precise, has to be devided into 32 *) mem)
      end.

  Definition mload : operation :=
    fun s mem =>
      match s with
        | nil => None
        | addr :: l =>
          Some (match Memory.find addr mem with Some b => b | None => zero end :: l, mem)
      end.


  Definition gas remaining_gas : operation :=
    fun s mem => Some (remaining_gas :: s, mem).

  Definition calldatasize size : operation :=
    fun s mem => Some (size :: s, mem).

  Definition callvalue value : operation :=
    fun s mem => Some (value :: s, mem).

  Fixpoint memwrite_n (start_addr : U256.t) (len : nat) (source : list U256.t) (mem : memory) :=
    match len with
      | O => mem
      | S len' =>
        memwrite_n (succ start_addr (* what happens when this overflows? *) ) len'
        (match source with nil => nil | _ :: tl => tl end)
        (Memory.add start_addr (match source with nil => zero | hd :: _ => hd end) mem)
    end.

  Fixpoint drop {A : Type} (n : nat) (lst : list A) :=
    match n, lst with
      | O, _ => lst
      | _, nil => nil
      | S pre, _ :: tl => drop pre tl
    end.

  Definition calldatacopy (input : list U256.t) : operation :=
    fun s mem =>
      match s with
        | m0 :: m1 :: m2 :: l =>
          Some (l, memwrite_n m0 (to_nat m2) (drop (to_nat m1) input) mem)
        | _ => None
      end.

  Definition iszero : operation :=
    fun s mem =>
      match s with
        | nil => None
        | h :: tl =>
          Some ((if is_zero h then one else zero) :: tl, mem)
      end.

  Definition two_two_op (f : U256.t -> U256.t -> (U256.t * U256.t)) : operation :=
    fun s mem =>
      match s with
        | a :: b :: l =>
          Some (fst (f a b) :: snd (f a b) :: l, mem)
        | _ => None
      end.

  Parameter exp : U256.t -> U256.t -> U256.t.

  Definition two_one_op (f : U256.t -> U256.t -> U256.t) : operation :=
    fun s mem =>
      match s with
        | nil => None
        | _ :: nil => None
        | a :: b :: l => Some ((f a b) :: l, mem)
      end.

  Definition exp_op : operation := two_one_op exp.

  Definition and_op : operation := two_one_op and.

  Definition one_one_op (f : U256.t -> U256.t) : operation :=
    fun s mem =>
      match s with
        | nil => None
        | a :: l => Some (f a :: l, mem)
      end.

  Definition sload storage : operation :=
    one_one_op (fun addr => match Memory.find addr storage with Some b => b | None => zero end).

  Definition calldataload (input : list U256.t) : operation :=
    one_one_op (fun n => List.nth (to_nat n) input zero).

  Parameter div : U256.t -> U256.t -> U256.t.

  Definition div_op := two_one_op div.
  Definition add_op := two_one_op add.

  Definition dup1 : operation :=
    fun s mem =>
      match s with
        | a :: l => Some (a :: a :: l, mem)
        | _ => None (* really? *)
      end.

  Definition dup2 : operation :=
    fun s mem =>
      match s with
        | a :: b :: l => Some (b :: a :: b :: l, mem)
        | _ => None
      end.

  Definition dup3 : operation :=
    fun s mem =>
      match s with
        | a :: b :: c :: l => Some (c :: a :: b :: c :: l, mem)
        | _ => None
      end.

  Definition eq_op : operation := two_one_op
    (fun a b => match U256.compare a b with
                | EQ _ => one
                | _ => zero
              end).

  Definition gt : operation := two_one_op
    (fun a b => match U256.compare a b with
                | GT _ => one
                | _ => zero
              end).

  Definition sub_op : operation := two_one_op sub.

  Definition swap1 : operation := two_two_op (fun a b => (b, a)).

  Definition swap2 : operation :=
    fun s mem =>
      match s with
        | a :: b :: c :: l =>
          Some (c :: b :: a :: l, mem)
        | _ => None
      end.

  Record state :=
    {   stc     : stack
      ; mem     : memory
      ; str     : memory
      ; prg_sfx : list instr
      ; program : list instr
      ; caller  : U256.t
      ; value   : U256.t
      ; data    : list U256.t
      ; time    : U256.t
    }.

  Inductive result :=
  | continue : state -> result
  | suicide  : U256.t (* who gets the balance *) -> result
  | returned : state -> result
  | stopped  : state -> result
  | end_of_program : state -> result (* what actually happens? *)
  | failure :  state -> result (* what actually happens? *)
  .

  Definition operation_sem (op : operation) (pre: state) : result :=
    match pre.(prg_sfx) with
      | nil => end_of_program pre
      | _ :: tl =>
        match op pre.(stc) pre.(mem) with
          | None => failure pre
          | Some (s,m) =>
            continue {| stc := s ;
              mem := m ;
              str := pre.(str) ;
              program := pre.(program);
              prg_sfx := tl;
              caller := pre.(caller);
              value := pre.(value);
              data  := pre.(data);
              time  := pre.(time)
            |}
        end
    end.

  Definition reader (f : state -> U256.t) (pre : state) : result :=
    match pre.(prg_sfx) with
      | nil => end_of_program pre
      | _ :: tl =>
        continue {| stc := f pre :: pre.(stc) ;
          mem := pre.(mem) ;
          str := pre.(str) ;
          program := pre.(program);
          prg_sfx := tl;
          caller := pre.(caller);
          value  := pre.(value);
          data   := pre.(data);
          time   := pre.(time)
        |}
    end.

  Parameter U : string -> U256.t.
  Parameter Ulen : forall {a : Type}, list a -> U256.t.

  Definition instr_sem (i : instr) : state -> result :=
    match i with
      | STOP => (fun pre => stopped pre)
      | ADD => operation_sem add_op
      | SUB => operation_sem sub_op
      | DIV => operation_sem div_op
      | EXP => operation_sem exp_op
      | instr_GT  => operation_sem gt
      | instr_EQ => operation_sem eq_op
      | AND => operation_sem and_op
      | ISZERO => operation_sem iszero
      | CALLER => reader caller
      | CALLVALUE => reader value
      | CALLDATALOAD => (fun pre => operation_sem (calldataload pre.(data)) pre)
      | CALLDATASIZE => reader (fun st => Ulen (st.(data)))
      | CALLDATACOPY => (fun pre => operation_sem (calldatacopy pre.(data)) pre)
      | TIMESTAMP => reader time
      | POP =>    operation_sem pop
      | MLOAD  => operation_sem mload
      | MSTORE => operation_sem mstore
      | SLOAD => (fun pre => operation_sem (sload pre.(str)) pre)
      | SSTORE => (fun pre =>
                     match pre.(stc) with
                     | nil => failure pre
                     | _ :: nil => failure pre
                     | addr :: val :: stl =>
                       match pre.(prg_sfx) with
                       | nil => failure pre
                       | _ :: cont => 
                         continue {|
                             stc := stl;
                             mem := pre.(mem);
                             str := Memory.add addr val pre.(str);
                             program := pre.(program);
                             prg_sfx := cont;
                             caller := pre.(caller);
                             value := pre.(value);
                             data := pre.(data);
                             time := pre.(time)
                           |}
                       end
                     end)
      | JUMP => (fun pre =>
                   match pre.(stc) with
                   | nil => failure pre
                   | hd :: tl =>
                     continue {|
                       stc := tl;
                       mem := pre.(mem);
                       str := pre.(str);
                       program := pre.(program);
                       prg_sfx := drop_bytes pre.(program) (to_nat hd);
                       caller := pre.(caller);
                       value := pre.(value);
                       data := pre.(data);
                       time := pre.(time)
                     |}
                   end
                )
      | JUMPI => (fun pre =>
                    match pre.(stc) with
                    | nil => failure pre
                    | hd::nil => failure pre
                    | dst :: cond :: tl_stc =>
                      if is_zero cond then
                        match pre.(prg_sfx) with
                        | nil => failure pre
                        | _ :: tl =>
                          continue {|
                              stc := tl_stc;
                              mem := pre.(mem);
                              str := pre.(str);
                              program := pre.(program);
                              prg_sfx := tl;
                              caller := pre.(caller);
                              value := pre.(value);
                              data := pre.(data);
                              time := pre.(time)
                            |}
                        end
                      else
                        continue {|
                            stc := tl_stc;
                            mem := pre.(mem);
                            str := pre.(str);
                            program := pre.(program);
                            prg_sfx := drop_bytes pre.(program) (to_nat dst);
                            caller := pre.(caller);
                            value := pre.(value);
                            data := pre.(data);
                            time := pre.(time)
                          |}
                    end)
      | JUMPDEST =>
        (fun pre => match pre.(prg_sfx) with
                      | nil => failure pre
                      | _ :: tl =>
                        continue {|
                            stc := pre.(stc);
                            mem := pre.(mem);
                            str := pre.(str);
                            program := pre.(program);
                            prg_sfx := tl;
                            caller := pre.(caller);
                            value := pre.(value);
                            data := pre.(data);
                            time := pre.(time)
                            |}
                    end)
      | PUSH_N str => operation_sem (push_x (U str))
      | DUP1 => operation_sem dup1
      | DUP2 => operation_sem dup2
      | DUP3 => operation_sem dup3
      | SWAP1 => operation_sem swap1
      | SWAP2 => operation_sem swap2
      | RETURN => returned
      | SUICIDE => (fun pre =>
                      match pre.(stc) with
                        | nil => failure pre
                        | hd :: _ => suicide hd
                      end
                   )
    end.

  Fixpoint apply_n (n : nat) (pre : state) : result :=
    match n, pre.(prg_sfx) with
      | O, _ => continue pre
      | S n', hd::_ =>
        match instr_sem hd pre with
          | continue post =>  apply_n n' post
          | x => x
        end
      | S n', nil => end_of_program pre
    end.

  Lemma apply_S : forall n' pre,
    apply_n (S n') pre =
    match pre.(prg_sfx) with
      | hd :: _ => 
        match instr_sem hd pre with
          | continue post =>  apply_n n' post
          | x => x
        end
      | nil => end_of_program pre
    end.
  Proof.
  auto.
  Qed.


  Parameter c : U256.t.
  Parameter v : U256.t.
  Parameter d : list U256.t.
  Parameter current_time : U256.t.
  Parameter s : Memory.t U256.t.

  Definition ex := {|
    stc := nil;
    mem := Memory.empty U256.t;
    str := s;
    program := example1;
    prg_sfx := example1;
    caller := c;
    value := v;
    data := d;
    time := current_time
  |}.


  Parameter tn : (to_nat (U "0x004f")) = 79.
  Parameter hg : (to_nat (U "0x00a4")) = 164.
  Parameter gg : (to_nat (U "0x005a")) = 90.
  Lemma ff_ : U256.eq (U "0x40") (U "0x40").
  Proof. auto.  Qed.
  Parameter ff : U256.compare (U "0x40") (U "0x40") = @EQ U256.t U256.lt U256.eq (U "0x40") (U "0x40") ff_.

  Parameter zz : is_zero zero.

  Parameter somebody : U256.t.

  Definition interesting (r : result) (target : U256.t) :=
    match r with
      | continue _ => False
      | suicide _  => True
      | returned st
      | stopped st  =>
        s <> st.(str) /\ Memory.find zero st.(str) = Some target
      | failure _ => True
      | end_of_program _ => True
    end.

  Ltac run :=
    repeat (rewrite apply_S; compute -[apply_n PeanoNat.div nth drop_bytes interesting]).

  
  Goal interesting (apply_n 1000 ex) somebody -> False.
    run.
    set b0 := is_zero _.
    case_eq b0 => b0_eq.
    {
      run.
      set b1 := is_zero _.
      case_eq b1 => b1_eq.
      {
        run.
        set b2 := is_zero _.
        case_eq b2 => b2_eq.
        {
          run.
          have -> : (to_nat (U "0x004d")) = 77 by admit.
          compute [drop_bytes string_half_len minus].
          run.
          rewrite/interesting/str.
          case => ? _; done.
        }
        {
          rewrite apply_S; compute -[apply_n NPeano.div nth drop_bytes interesting].
          idtac.
          have K : (to_nat (U "0x007d")) = 125 by admit.
          rewrite [in X in drop_bytes _ X] K.
          compute [drop_bytes minus string_half_len].
          progress run.
          have -> : (to_nat (U "0x00ad")) = 173 by admit.
          compute [drop_bytes minus string_half_len].
          rewrite apply_S; compute -[apply_n NPeano.div nth drop_bytes interesting].
          progress run.
          set b3 := is_zero _.
          case_eq b3 => b3_eq; run.
          {
            set b4 := is_zero _.
            case_eq b4 => b4_eq; run.
            {
              set b5 := is_zero _.
              case_eq b5 => b5_eq.
              {
                rewrite apply_S; compute -[apply_n NPeano.div nth drop_bytes interesting].
                rewrite apply_S; compute -[apply_n NPeano.div nth drop_bytes interesting].
                rewrite apply_S; compute -[apply_n NPeano.div nth drop_bytes interesting].
                rewrite apply_S; compute -[apply_n NPeano.div nth drop_bytes interesting].
                rewrite apply_S; compute -[apply_n NPeano.div nth drop_bytes interesting].
                rewrite apply_S; compute -[apply_n NPeano.div nth drop_bytes interesting].
                run.
                have -> : (to_nat (U "0x013b")) = 315 by admit.
                compute [drop_bytes string_half_len minus].

                rewrite apply_S; compute -[apply_n NPeano.div nth drop_bytes interesting].
                run.
                have -> : (to_nat (U "0x008e")) = 142 by admit.
                compute [drop_bytes string_half_len minus].
                run.
                rewrite/interesting.
                rewrite/str.
                move => [_].

(* Stop here to see the conditions for storage[1] change:

  b0 := is_zero
          match
            U256.compare (U "0x4665096d")
              (div (nth (to_nat (U "0x00")) d zero)
                 (U
                    "0x0100000000000000000000000000000000000000000000000000000000"))
          with
          | LT _ => zero
          | EQ _ => one
          | GT _ => zero
          end : bool
  b0_eq : b0 = true
  "input[0] <> ..."

  b1 := is_zero
          match
            U256.compare (U "0xbe040fb0")
              (div (nth (to_nat (U "0x00")) d zero)
                 (U
                    "0x0100000000000000000000000000000000000000000000000000000000"))
          with
          | LT _ => zero
          | EQ _ => one
          | GT _ => zero
          end : bool
  b1_eq : b1 = true
  "input[0] <> ..."

  b2 := is_zero
          match
            U256.compare (U "0xdd467064")
              (div (nth (to_nat (U "0x00")) d zero)
                 (U
                    "0x0100000000000000000000000000000000000000000000000000000000"))
          with
          | LT _ => zero
          | EQ _ => one
          | GT _ => zero
          end : bool
  b2_eq : b2 = false

  "input[0] begins with 0xdd467064".



  K : to_nat (U "0x007d") = 125
  b3 := is_zero
          (if is_zero
                match
                  U256.compare
                    (and (U "0xffffffffffffffffffffffffffffffffffffffff")
                       c)
                    (and (U "0xffffffffffffffffffffffffffffffffffffffff")
                       (and
                          (U "0xffffffffffffffffffffffffffffffffffffffff")
                          (div
                             match
                               (fix find (k : U256.t)
                                         (s : list (U256.t * U256.t))
                                         {struct s} : 
                                option U256.t :=
                                  match s with
                                  | nil => None
                                  | (k', x) :: s' =>
                                      match U256.compare k k' with
                                      | LT _ => None
                                      | EQ _ => Some x
                                      | GT _ => find k s'
                                      end
                                  end) (U "0x00")
                                 (let (this, _) := s in this)
                             with
                             | Some b => b
                             | None => zero
                             end (exp (U "0x0100") (U "0x00")))))
                with
                | LT _ => zero
                | EQ _ => one
                | GT _ => zero
                end
           then one
           else zero) : bool
  b3_eq : b3 = true
  "caller == storage[0]"

  b4 := is_zero
          (if is_zero
                match
                  U256.compare (nth (to_nat (U "0x04")) d zero)
                    current_time
                with
                | LT _ => zero
                | EQ _ => zero
                | GT _ => one
                end
           then one
           else zero) : bool
  b4_eq : b4 = true
  "input[4] > current_time"


  b5 := is_zero
          (if is_zero
                match
                  U256.compare
                    match
                      (fix find (k : U256.t) (s : list (U256.t * U256.t))
                                {struct s} : option U256.t :=
                         match s with
                         | nil => None
                         | (k', x) :: s' =>
                             match U256.compare k k' with
                             | LT _ => None
                             | EQ _ => Some x
                             | GT _ => find k s'
                             end
                         end) (U "0x01") (let (this, _) := s in this)
                    with
                    | Some b => b
                    | None => zero
                    end (U "0x00")
                with
                | LT _ => zero
                | EQ _ => one
                | GT _ => zero
                end
           then one
           else zero) : bool
  b5_eq : b5 = true

  "storage[1] == 0"

*)


                (* storage[1] = input[4] *)
                (* storage at zero has not changed *)
                admit.
              }
              {
                have -> : (to_nat (U "0x0131")) = 305 by admit.
                compute [drop_bytes string_half_len minus].
                run.
                idtac.
                have -> : (to_nat (U "0x013b")) = 315 by admit.
                compute [drop_bytes string_half_len minus].
                run.
                have -> : (to_nat (U "0x008e")) = 142 by admit.
                compute [drop_bytes string_half_len minus].
                (* pushn 40, mload, dup1, dup3, dup2 *)

                run.
                rewrite/interesting/str.

                case => ? _.
                done.
              }
            }
            {
              have -> : (to_nat (U "0x0119")) = 281 by admit.
              compute [drop_bytes string_half_len minus].
              run.
              rewrite-/b4.
              rewrite b4_eq.
              run.
              have -> : (to_nat (U "0x0131")) = 305 by admit.
              compute [drop_bytes string_half_len minus];
              run.
              idtac.
              have -> : (to_nat (U "0x013b")) = 315 by admit.
              compute [drop_bytes string_half_len minus];
              run.
              have -> : (to_nat (U "0x008e")) = 142 by admit.
              compute [drop_bytes string_half_len minus];
              run.

              rewrite/interesting/str.
              by case => ? _.
            }
          }
          {
            run.
            idtac.

            have -> : (to_nat (U "0x013a"))= 314 by admit.
            compute [drop_bytes string_half_len minus];
            run.
            idtac.
            have -> : (to_nat (U "0x008e")) = 142 by admit.
            compute [drop_bytes string_half_len minus];
            run.
            rewrite/interesting/str.
            by move => [? _].
          }
        }
      }
      {
        have -> : (to_nat (U "0x0070")) = 112 by admit.
        compute [drop_bytes string_half_len minus];
        run.
        have -> : (to_nat (U "0x0140")) = 320 by admit.
        compute [drop_bytes string_half_len minus];
        run.
        set b7 := is_zero _.
        case_eq b7 => b7_eq.
        {
          run.
          idtac.
          set b8 := is_zero _.
          case_eq b8 => b8_eq.
          {
            run.

            idtac.
            have -> : (U "0x00") = zero by admit.
            have -> : forall x, (exp x zero) = one by admit.
            have -> : forall y, (div y one)  = y   by admit.
            (* inheritor is find zero s *)

            idtac.

(*
  Stop here to see the conditions for `SUICIDE` to happen.

  b0 := is_zero
          match
            U256.compare (U "0x4665096d")
              (div (nth (to_nat (U "0x00")) d zero)
                 (U
                    "0x0100000000000000000000000000000000000000000000000000000000"))
          with
          | LT _ => zero
          | EQ _ => one
          | GT _ => zero
          end : bool
  b0_eq : b0 = true
  "input[0] <> ..."


  b1 := is_zero
          match
            U256.compare (U "0xbe040fb0")
              (div (nth (to_nat (U "0x00")) d zero)
                 (U
                    "0x0100000000000000000000000000000000000000000000000000000000"))
          with
          | LT _ => zero
          | EQ _ => one
          | GT _ => zero
          end : bool
  b1_eq : b1 = false
  "input[0] begins with 0xbe040fb0"


  b7 := is_zero
          (if is_zero
                match
                  U256.compare
                    (and (U "0xffffffffffffffffffffffffffffffffffffffff")
                       c)
                    (and (U "0xffffffffffffffffffffffffffffffffffffffff")
                       (and
                          (U "0xffffffffffffffffffffffffffffffffffffffff")
                          (div
                             match
                               (fix find (k : U256.t)
                                         (s : list (U256.t * U256.t))
                                         {struct s} : 
                                option U256.t :=
                                  match s with
                                  | nil => None
                                  | (k', x) :: s' =>
                                      match U256.compare k k' with
                                      | LT _ => None
                                      | EQ _ => Some x
                                      | GT _ => find k s'
                                      end
                                  end) (U "0x00")
                                 (let (this, _) := s in this)
                             with
                             | Some b => b
                             | None => zero
                             end (exp (U "0x0100") (U "0x00")))))
                with
                | LT _ => zero
                | EQ _ => one
                | GT _ => zero
                end
           then one
           else zero) : bool
  b7_eq : b7 = true
  "storage[0] == caller"


  b8 := is_zero
          (if is_zero
                match
                  U256.compare current_time
                    match
                      (fix find (k : U256.t) (s : list (U256.t * U256.t))
                                {struct s} : option U256.t :=
                         match s with
                         | nil => None
                         | (k', x) :: s' =>
                             match U256.compare k k' with
                             | LT _ => None
                             | EQ _ => Some x
                             | GT _ => find k s'
                             end
                         end) (U "0x01") (let (this, _) := s in this)
                    with
                    | Some b => b
                    | None => zero
                    end
                with
                | LT _ => zero
                | EQ _ => zero
                | GT _ => one
                end
           then one
           else zero) : bool
  b8_eq : b8 = true
  "current time > storage[1]"
 *)


            (* stop here and see the condition for SUICIDE *)
            (* next question.  how to change the storage? *)
            admit.
          }
          {
            run.
            idtac.
            have -> : (to_nat (U "0x01de")) = 478 by admit.
            compute [drop_bytes string_half_len minus];
              run.
            idtac.
            have -> : (to_nat (U "0x007b")) = 123 by admit.
            compute [drop_bytes string_half_len minus];
              run.

            rewrite/interesting/str.
            case => ? _; done.
          }
        }
        {
          have -> : (to_nat (U "0x01df")) = 479 by admit.
            compute [drop_bytes string_half_len minus];
              run.
          idtac.
            have -> : (to_nat (U "0x007b")) = 123 by admit.
            compute [drop_bytes string_half_len minus];
              run.

            idtac.
            rewrite/interesting/str.
            case => ? _; done.
        }
      }
    }
    {
      rewrite tn.
      compute [drop_bytes string_half_len minus];
        run.
      rewrite hg.
      compute [drop_bytes string_half_len minus];
        run.
      idtac.
      rewrite gg.
      compute [drop_bytes string_half_len minus];
        run.
      rewrite/interesting/str.
      case => ? _; done.
    }
  Qed.

End EVM.
