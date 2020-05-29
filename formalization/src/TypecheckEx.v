(* Compcert imports *)
Add LoadPath "../libs/".
Add LoadPath "../libs/CompCert-Toolkit".
Require Import Coqlib.
Require Import Bits.

(* Illvm imports *)
Require Import Utility.
Require Import IllvmAST.
Require Import TargetData.
Require Import IllvmValues.
Require Import Amem.
Require Import Cmem.
Require Import Interp.
Require Import TypeSystem.
Require Import Typecheck.

(*
int fact <p1> (int*p1 result, int n) {
  p2 = poolinit(int) {
    int*p2 x = poolalloc(p2, int);
    store (int) 1 (int*p2) x;
    if (n > 1) fact<p2>(x, n - 1)
    int y = load (int*p2) x;
    int z = y * n;
    store (int) z (int*p1) result;
    return 1;
  }
}

Regions:
p1 -> 1
p2 -> 2

Locals:
result -> 1
n -> 2
x -> 3
y -> 4
z -> 5
*)

Definition fact_bb1 := mk_block
  (Word.repr 1)
  nil
  nil
  (Insn_nd (Insn_malloc 3%nat (Some Typ_int32) 2%nat (Op_const (Const_int 31 lt_31_MAX_I_BITS (Word.repr 1))) (Word.repr 2))).
Definition gamma1 :=
  Nenv.add 1%nat (Ftyp_ptr Typ_int32 1%nat :: nil)
  (Nenv.add 2%nat (Ftyp_int32 :: nil)
  (Nenv.empty (ftyps))).

Definition fact_bb2 := mk_block
  (Word.repr 2)
  nil
  ((Insn_store Typ_int32 (Op_const (Const_int 31 lt_31_MAX_I_BITS (Word.repr 1))) (Typ_ptr Typ_int32 2%nat) (Op_reg 3%nat))::nil)
  (Insn_term (Insn_br (Op_const (Const_int 0 lt_0_MAX_I_BITS (Word.repr 1))) (Word.repr 3) (Word.repr 4))).
Definition gamma2 :=
  Nenv.add 1%nat (Ftyp_ptr Typ_int32 1%nat :: nil)
  (Nenv.add 2%nat (Ftyp_int32 :: nil)
  (Nenv.add 3%nat (Ftyp_ptr Typ_int32 2%nat :: nil)
  (Nenv.empty (ftyps)))).

Definition fact_bb3 := mk_block
  (Word.repr 3)
  nil
  ((Insn_load 4%nat (Typ_ptr Typ_int32 2%nat) (Op_reg 3%nat)) :: 
  (Insn_binop 5%nat Binop_mul (Op_reg 4%nat) (Op_reg 2%nat)) ::
  (Insn_store Typ_int32 (Op_reg 5%nat) (Typ_ptr Typ_int32 1%nat) (Op_reg 1%nat)) :: nil)
  (Insn_term (Insn_return Typ_int32 (Op_reg 5%nat))).
Definition gamma3 :=
  Nenv.add 1%nat (Ftyp_ptr Typ_int32 1%nat :: nil)
  (Nenv.add 2%nat (Ftyp_int32 :: nil)
  (Nenv.add 3%nat (Ftyp_ptr Typ_int32 2%nat :: nil)
  (Nenv.empty (ftyps)))).

Definition fact_bb4 := mk_block
  (Word.repr 4)
  nil
  nil
  (Insn_nd (Insn_call (Some 6%nat) (Some Typ_int32) (Op_const (Const_fun (Word.repr 1))) (2%nat :: nil) (Op_reg 3%nat::Op_reg 2%nat::nil) (Word.repr 3))).
Definition gamma4 :=
  Nenv.add 1%nat (Ftyp_ptr Typ_int32 1%nat :: nil)
  (Nenv.add 2%nat (Ftyp_int32 :: nil)
  (Nenv.add 3%nat (Ftyp_ptr Typ_int32 2%nat :: nil)
  (Nenv.empty (ftyps)))).

Definition fact_body : (blocks) := fact_bb1 :: fact_bb2 :: fact_bb3 :: fact_bb4 :: nil.

Definition fact := mk_function
  (Word.repr 1)
  (1 :: 2 :: nil)%nat
  (Typ_ptr Typ_int32 1%nat :: Typ_int32 :: nil)
  fact_body
  (Some Typ_int32)
  ((1%nat, Typ_int32) :: nil)
  ((2%nat, Typ_int32) :: nil).

Definition fs := fact :: nil.
Definition lo : layout := mk_layout false 8 8 8 8 4 4.
Definition tenv : tenv_t := Nenv.empty (ftyps * list rgn * bool).

Definition C := mk_config fs lo tenv.
Definition D1 := Nenv.add 1%nat Typ_int32 (Nenv.empty typ).
Definition D2 := Nenv.add 2%nat Typ_int32 D1.
Definition P := 
  (Ienv.add (Word.repr 1) gamma1
  (Ienv.add (Word.repr 2) gamma2
  (Ienv.add (Word.repr 3) gamma3
  (Ienv.add (Word.repr 4) gamma4
  (Ienv.empty Gamma))))).
Definition K := Nenv.empty (ftyps).

(*
Goal False.
  pose (tc_nd C D2 P K gamma1 fact_body (Insn_malloc 3%nat (Typ_ptr Typ_int 2%nat) 2%nat 1%nat (Int.repr 2)) (Int.repr 1) = true).
  unfold tc_nd in P0.
  unfold TSb in P0.
  unfold tc_term in P0.
  unfold tc_junction in P0.
  assert (Ienv.find (Int.repr 2) P = Some gamma2). admit.
  remember (Ienv.find (elt:=Nenv.t (ftyps syn_region)) (Int.repr 2) P) as Hd.
  destruct Hd; try congruence.
  assert (lookup_blk' (Int.repr 2) fact_body = Some fact_bb2). admit.
  destruct (lookup_blk' (Int.repr 2) fact_body); try congruence.
  inversion H0. subst. simpl in P0.
  unfold tc_phi_blk in P0.
  inversion H. subst. symmetry in HeqHd. unfold ftyps in HeqHd. 
  rewrite H in HeqHd. inversion HeqHd. subst.
  Print gamma2.
  Print gamma1.
*)  

Definition test1 := tc_function C D1 D2 P fact.

(*
Extract Inductive nat => int [ "0" "succ" ] "(fun fO fS n -> if n=0 then fO () else fS (n-1))".
Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive Z => int [ "Z0" "Zpos" "Zneg" ].
*)

Set Extraction AccessOpaque.

(* Makes sense to do this stuff *)
Extract Inductive nat => "int"
  [ "0" "(fun x -> x + 1)" ]
    "(fun zero succ n ->
        if n = 0 then zero () else succ (n-1))".
Extract Inductive unit => "unit" [ "()" ].
Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive sumbool => "bool" [ "true" "false" ].
Extract Inductive list => "list" [ "[]" "(::)" ].
Extract Inductive prod => "(*)" [ "(,)" ].
Extract Inductive option => "option" [ "Some" "None" ].

(* Extraction "test4" test1. *)

(* Because of this need to fix Nenv/Ienv to do comparison on strings *)
Extract Constant id => "string".
Extract Constant id_dec => "( = )".
Extract Constant rgn => "string".
Extract Constant rgn_dec => "( = )".
Extract Constant lab => "string".
Extract Constant lab_dec => "( = )".
Extract Constant i2n => "(fun _ x -> x)".
Extract Constant Const0 => "0".
Extract Constant Const4 => "4".
Extract Constant Const8 => "8".
Extract Constant Const31 => "31".
Extract Constant Const63 => "63".
Extract Constant WORDSIZE_BITS => "63".
Extract Constant Typ_int1 => "Typ_int(0)".
Extract Constant Typ_int8 => "Typ_int(7)".
Extract Constant Typ_int16 => "Typ_int(15)".
Extract Constant Typ_int32 => "Typ_int(31)".
Extract Constant Typ_int64 => "Typ_int(63)".
Extract Constant Ftyp_int1 => "Ftyp_int(0)".
Extract Constant Ftyp_int8 => "Ftyp_int(7)".
Extract Constant Ftyp_int16 => "Ftyp_int(15)".
Extract Constant Ftyp_int32 => "Ftyp_int(31)".
Extract Constant Ftyp_int64 => "Ftyp_int(63)".

Extraction "Extraction/tc" tc_functions.
