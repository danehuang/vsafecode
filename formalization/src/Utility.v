(* Coq standard library imports *)
Require Import OrderedTypeEx.
Require Import FMaps.
Require Import FSets.FMapAVL.
Require Import FSets.FMapFacts.

(* Other library imports *)
Add LoadPath "../libs".
Add LoadPath "../libs/CompCert-Toolkit". 
Require Import Bits.
Require Import Fcore.
Require Import Fcore_digits.
Require Import Fcalc_digits.
Require Import Fappli_IEEE.
Require Import Fappli_IEEE_bits.


(* Illvm imports *)
Require Import SimpleEnv.

(* ---------------------------------------------------------------------- *)
Module Nenv := FMapAVL.Make(Nat_as_OT).     (* nat -> 'a *)
Module Ienv := FMapAVL.Make(Int64_OT).      (* int -> 'a *)
Module Zenv := SimpleEnv.Make(Z_as_OT).     (* Z -> 'a *)

Module NFacts := FMapFacts.WFacts_fun(Nat_as_OT)(Nenv).
Module NProp := FMapFacts.WProperties_fun(Nat_as_OT)(Nenv).
Module IFacts := FMapFacts.WFacts_fun(Int64_OT)(Ienv).
Module IProp := FMapFacts.WProperties_fun(Int64_OT)(Ienv).

(* ---------------------------------------------------------------------- *)
Definition domain {A B:Type} (smap:list (A*B)) := map (fun x => fst x) smap.
Definition range {A B:Type} (smap:list (A*B)) := map (fun x => snd x) smap.

(* ---------------------------------------------------------------------- *)
Tactic Notation "destruct_c" constr(E) := 
  destruct E; try congruence.

Ltac try_both :=
  match goal with
    | [ |- {_ = _} + {_ <> _} ] => left; congruence
    | [ |- {_ = _} + {_ <> _} ] => right; congruence
    | [ |- _ ] => idtac
  end.

Ltac t_simp :=
  repeat match goal with
           | [ H: exists _, _ |- _ ] => destruct H
           | [ H: _ /\ _ |- _ ] => destruct H
           | [ H: ?x = ?x |- _ ] => clear H
         end.

Ltac t_dup H :=
  let H' := fresh "H'" in 
    let t := type of H in
      assert (H' : t); [exact H | idtac].

(*
Ltac def_to_eq X HX E :=
  assert (HX : E = X) by reflexivity; clearbody X.

Tactic Notation "cases" constr(E) "as" ident(H) := 
  let X := fresh "TEMP" in 
  set (X := E) in *; def_to_eq X H E;
  destruct X.
*)

(** Specialization for IEEE half precision operations *)
Section B16_Bits.

Definition binary16 := binary_float 11 16.

Let Hprec : (0 < 11)%Z.
apply refl_equal.
Qed.

Let Hprec_emax : (11 < 16)%Z.
apply refl_equal.
Qed.

Definition b16_opp := Bopp 11 16.
Definition b16_plus := Bplus _ _ Hprec Hprec_emax.
Definition b16_minus := Bminus _ _ Hprec Hprec_emax.
Definition b16_mult := Bmult _ _ Hprec Hprec_emax.
Definition b16_div := Bdiv _ _ Hprec Hprec_emax.
Definition b16_sqrt := Bsqrt _ _ Hprec Hprec_emax.

Definition b16_of_bits : Z -> binary16 := binary_float_of_bits 10 5 (refl_equal _) (refl_equal _) (refl_equal _).
Definition bits_of_b16 : binary16 -> Z := bits_of_binary_float 10 5.

End B16_Bits.

(** Specialization for IEEE quad precision operations *)
Section B128_Bits.

Definition binary128 := binary_float 113 16384.

Let Hprec : (0 < 113)%Z.
apply refl_equal.
Qed.

Let Hprec_emax : (113 < 16384)%Z.
apply refl_equal.
Qed.

Definition b128_opp := Bopp 113 16384.
Definition b128_plus := Bplus _ _ Hprec Hprec_emax.
Definition b128_minus := Bminus _ _ Hprec Hprec_emax.
Definition b128_mult := Bmult _ _ Hprec Hprec_emax.
Definition b128_div := Bdiv _ _ Hprec Hprec_emax.
Definition b128_sqrt := Bsqrt _ _ Hprec Hprec_emax.

Definition b128_of_bits : Z -> binary128 := binary_float_of_bits 112 15 (refl_equal _) (refl_equal _) (refl_equal _).
Definition bits_of_b128 : binary128 -> Z := bits_of_binary_float 112 15.

End B128_Bits.

Inductive fprec :=
| Fprec_half : fprec
| Fprec_float : fprec
| Fprec_double : fprec
| Fprec_fp128 : fprec.

Inductive fp :=
| Fp_half : binary16 -> fp
| Fp_float : binary32 -> fp
| Fp_double : binary64 -> fp
| Fp_fp128 : binary128 -> fp.
