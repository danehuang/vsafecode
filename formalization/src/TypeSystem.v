(* Contains definition of SAFEcode typesystem *)

(* Other library imports *)
Add LoadPath "../libs".
Add LoadPath "../libs/CompCert-Toolkit".
Require Import Bits.
Require Import Flocq.Appli.Fappli_IEEE.
Require Import Flocq.Appli.Fappli_IEEE_bits.
Require Import Coqlib.
Require Import Axioms.

(* Illvm imports *)
Require Import Utility.
Require Import IllvmAST.
Require Import TargetData.
Require Import IllvmValues.
Require Import Amem.
Require Import Cmem.
Require Import Interp.


(* ---------------------------------------------------------------------- *)
(** * Contexts *)

Definition Delta := Nenv.t typ.
Definition Gamma := Nenv.t ftyps.         (* type context *)
Definition Epsilon := Nenv.t insn.        (* equational alias context *) 
Definition Psi := Ienv.t (Nenv.t ftyps).  (* code context (checks code labels) *)

(* ---------------------------------------------------------------------- *)
(** * Well-formed Definitions *)

Inductive wf_typ (tenv:tenv_t) : Delta -> typ -> Prop :=
| wf_typ_float : forall D,
  TS tenv Typ_float ->
  wf_typ tenv D Typ_float
| wf_typ_double : forall D,
  TS tenv Typ_double ->
  wf_typ tenv D Typ_double
| wf_typ_int : forall D sz pf,
  TS tenv (Typ_int sz pf) ->
  wf_typ tenv D (Typ_int sz pf)
| wf_typ_ptr : forall D t r t',
  Nenv.find r D = Some t' ->
  wf_typ tenv D t ->
  TS tenv (Typ_ptr t r) ->
  wf_typ tenv D (Typ_ptr t r)
| wf_typ_name : forall D x t lr1 lr2,
  Nenv.find x tenv = Some (t, lr2) ->
  Forall (fun r => exists t, Nenv.find r D = Some t) lr1 ->
  TS tenv (Typ_name x lr1) ->
  wf_typ tenv D (Typ_name x lr1)
| wf_typ_fun : forall D prgn sig r,
  Forall (fun t => wf_tenv_typ prgn t) sig ->
  wf_tenv_typ prgn r ->
  TS tenv (Typ_fun prgn sig (Some r)) ->
  wf_typ tenv D (Typ_fun prgn sig (Some r))
| wf_typ_fun2 : forall D prgn sig,
  Forall (fun t => wf_tenv_typ prgn t) sig ->
  TS tenv (Typ_fun prgn sig None) ->
  wf_typ tenv D (Typ_fun prgn sig None)
| wf_typ_array : forall D t sz,
  sz <> 0%nat ->
  wf_typ tenv D t ->
  TS tenv (Typ_array t sz) ->
  wf_typ tenv D (Typ_array t sz)
| wf_typ_ptrU : forall D sz r t',
  Nenv.find r D = Some t' ->
  TS tenv (Typ_ptrU sz r) ->
  wf_typ tenv D (Typ_ptrU sz r).
Hint Constructors wf_typ.

(* Well-formed ftyp
 * tenv; D |- t 
 * ftyp t is closed under D *)
Inductive wf_ftyp (tenv:tenv_t) : Delta -> ftyp -> Prop :=
| wf_ftyp_float : forall D,
  wf_ftyp tenv D Ftyp_float
| wf_ftyp_double : forall D,
  wf_ftyp tenv D Ftyp_double
| wf_ftyp_int : forall D sz pf,
  wf_ftyp tenv D (Ftyp_int sz pf)
| wf_ftyp_fun : forall D lr ls t,
  Forall (fun t => wf_tenv_typ lr t) ls ->
  wf_tenv_typ lr t ->
  wf_ftyp tenv D (Ftyp_fun lr ls (Some t))
| wf_ftyp_fun2 : forall D lr ls,
  Forall (fun t => wf_tenv_typ lr t) ls ->
  wf_ftyp tenv D (Ftyp_fun lr ls None)
| wf_ftyp_ptr : forall D t r t',
  Nenv.find r D = Some t' ->
  wf_typ tenv D t ->
  wf_ftyp tenv D (Ftyp_ptr t r)
| wf_ftyp_ptrU : forall D sz r t',
  Nenv.find r D = Some t' ->
  wf_ftyp tenv D (Ftyp_ptrU sz r).
Hint Constructors wf_ftyp.

(* Well-formed ftyps
 * tenv; D |- t 
 * fyps t is closed under D *)  
Inductive wf_ftyps (tenv:tenv_t) : Delta -> ftyps -> Prop :=
| wf_ftyps_nil : forall D,
  wf_ftyps tenv D nil
| wf_ftyps_cons : forall D t ts,
  wf_ftyp tenv D t ->
  wf_ftyps tenv D ts ->
  wf_ftyps tenv D (t::ts).
Hint Constructors wf_ftyps.

Inductive wf_undef_ftyp : ftyp -> Prop :=
| wf_undef_ftyp_float :
  wf_undef_ftyp Ftyp_float
| wf_undef_ftyp_double :
  wf_undef_ftyp Ftyp_double
| wf_undef_ftyp_int : forall sz pf,
  wf_undef_ftyp (Ftyp_int sz pf).
Hint Constructors wf_undef_ftyp.

Inductive wf_undef_ftyps : ftyps -> Prop :=
| wf_undef_ftyps_nil :
  wf_undef_ftyps nil
| wf_undef_ftyps_cons : forall t ts,
  wf_undef_ftyp t ->
  wf_undef_ftyps ts ->
  wf_undef_ftyps (t::ts).
Hint Constructors wf_undef_ftyps.

(* Well-formed constant
 * Under a config, code and global context, a constant has typ tau
 * C; P; K |- c : t *)
Inductive wf_const : config -> Delta -> Psi -> const -> ftyps -> Prop :=
| wf_null : forall C D P,
  wf_const C D P (Const_null) (Ftyp_int64 :: nil)
| wf_nullU : forall C D P,
  wf_const C D P (Const_nullU) (Ftyp_int64 :: nil)
| wf_float : forall C D P f,
  wf_const C D P (Const_float f) (Ftyp_float :: nil)
| wf_double : forall C D P d,
  wf_const C D P (Const_double d) (Ftyp_double :: nil)
| wf_int : forall C D P sz pf (i:Word.int sz),
  wf_const C D P (Const_int sz pf i) (Ftyp_int sz pf :: nil)
| wf_fun : forall C D P f,
  lookup_fun (f_lab f) (c_fs C) = Some f ->
  wf_const C D P (Const_fun (f_lab f)) (Ftyp_fun (domain (f_prgn f)) (f_sig f) (f_ret f) :: nil)
| wf_undef : forall C D P ts,
  wf_undef_ftyps ts ->
  wf_const C D P (Const_undef ts) ts.
Hint Constructors wf_const.

(* Well-formed operand
 * Under a config, code, global and typ context, an operand has typ tau
 * C; P; K; G |- op : t *)
Inductive wf_operand : config -> Delta -> Psi -> Gamma -> operand -> ftyps -> Prop :=
| wf_reg : forall C D P G x t,
  Nenv.find x G = Some t ->
  wf_operand C D P G (Op_reg x) t
| wf_val : forall C D P G c t,
  wf_const C D P c t ->
  wf_operand C D P G (Op_const c) t.
Hint Constructors wf_operand.

(* Well-formed instruction
 * Under a config, code and global context, instruction i expects G1 and produces G2
 * C; D; P; K |- i: G1 -> G2 *)
Inductive wf_insn : config -> Delta -> Psi -> insn -> Gamma -> Gamma -> Prop :=
| wf_insn_binop : forall C D P G x bop o1 o2 sz pf1 pf2,
  wf_operand C D P G o1 (Ftyp_int sz pf1 :: nil) ->
  wf_operand C D P G o2 (Ftyp_int sz pf2 :: nil) ->
  wf_insn C D P (Insn_binop x bop o1 o2) G (Nenv.add x (Ftyp_int sz pf1 :: nil) G)
| wf_insn_fbinop : forall C D P G x f o1 o2 t1 t2,
  wf_operand C D P G o1 (t1 :: nil) ->
  wf_operand C D P G o2 (t2 :: nil) ->
  t1 = Ftyp_float \/ t1 = Ftyp_int 31 lt_31_MAX_I_BITS ->
  t2 = Ftyp_float \/ t2 = Ftyp_int 31 lt_31_MAX_I_BITS ->
  wf_insn C D P (Insn_fbinop x f o1 o2) G (Nenv.add x (Ftyp_float :: nil) G)
| wf_insn_fbinop2 : forall C D P G x f o1 o2 t1 t2,
  wf_operand C D P G o1 (t1 :: nil) ->
  wf_operand C D P G o2 (t2 :: nil) ->
  t1 = Ftyp_double \/ t1 = Ftyp_int 63 lt_63_MAX_I_BITS ->
  t2 = Ftyp_double \/ t2 = Ftyp_int 63 lt_63_MAX_I_BITS ->
  wf_insn C D P (Insn_fbinop x f o1 o2) G (Nenv.add x (Ftyp_double :: nil) G)
| wf_insn_icmp : forall C D P G x c o1 o2 t1 t2,
  wf_operand C D P G o1 (t1 :: nil) ->
  wf_operand C D P G o2 (t2 :: nil) ->
  match t1, t2 with
    | Ftyp_int sz1 _, Ftyp_int sz2 _ => sz1 = sz2
    | Ftyp_int sz _, Ftyp_ptr _ _ => sz = WORDSIZE_BITS
    | Ftyp_int sz _, Ftyp_ptrU _ _ => sz = WORDSIZE_BITS
    | Ftyp_ptr _ _, Ftyp_int sz _ => sz = WORDSIZE_BITS
    | Ftyp_ptrU _ _, Ftyp_int sz _ => sz = WORDSIZE_BITS
    | Ftyp_ptr _ _, Ftyp_ptr _ _ => True
    | Ftyp_ptr _ _, Ftyp_ptrU _ _ => True
    | Ftyp_ptrU _ _, Ftyp_ptrU _ _ => True
    | Ftyp_ptrU _ _, Ftyp_ptr _ _ => True
    | _, _ => False
  end ->
  wf_insn C D P (Insn_icmp x c o1 o2) G (Nenv.add x (Ftyp_int1 :: nil) G)
| wf_insn_fcmp : forall C D P G x c o1 o2 t1 t2,
  wf_operand C D P G o1 (t1 :: nil) ->
  wf_operand C D P G o2 (t2 :: nil) ->
  match t1, t2 with
    | Ftyp_float, Ftyp_float => True
    | Ftyp_float, Ftyp_int sz _ => sz = 31%nat
    | Ftyp_int sz _, Ftyp_float => sz = 31%nat
    | Ftyp_double, Ftyp_double => True
    | Ftyp_double, Ftyp_int sz _ => sz = 63%nat
    | Ftyp_int sz _, Ftyp_double => sz = 63%nat
    | Ftyp_int sz1 _, Ftyp_int sz2 _ => sz1 = sz2
    | _, _ => False
  end ->
  wf_insn C D P (Insn_fcmp x c o1 o2) G (Nenv.add x (Ftyp_int1 :: nil) G)

| wf_insn_load : forall C D P G x r t t' o,
  wf_operand C D P G o (Ftyp_ptr t' r :: nil) ->
  wf_typ (c_tenv C) D (Typ_ptr t r) ->
  TS (c_tenv C) t' ->
  ftyps_subset (flatten_typ (c_lo C) (c_tenv C) t) (flatten_typ (c_lo C) (c_tenv C) t') = true ->
  wf_insn C D P (Insn_load x (Typ_ptr t r) o) G (Nenv.add x (flatten_typ (c_lo C) (c_tenv C) t) G)
| wf_insn_loadU : forall C D P G x r o sz,
  (sz >= size_ftyp_nat (c_lo C) Ftyp_int32)%nat ->
  wf_operand C D P G o (Ftyp_ptrU sz r :: nil) ->
  wf_insn C D P (Insn_load x (Typ_ptrU 4 r) o) G (Nenv.add x (Ftyp_int32 :: nil) G)
| wf_insn_loadU2 : forall C D P G x r o sz,
  (sz >= size_ftyp_nat (c_lo C) Ftyp_int64)%nat ->
  wf_operand C D P G o (Ftyp_ptrU sz r :: nil) ->
  wf_insn C D P (Insn_load x (Typ_ptrU 8 r) o) G (Nenv.add x (Ftyp_int64 :: nil) G)
| wf_insn_loadU3 : forall C D P G x r o sz,
  (sz >= size_ftyp_nat (c_lo C) Ftyp_int8)%nat ->
  wf_operand C D P G o (Ftyp_ptrU sz r :: nil) ->
  wf_insn C D P (Insn_load x (Typ_ptrU 1 r) o) G (Nenv.add x (Ftyp_int8 :: nil) G)
| wf_insn_loadU4 : forall C D P G x r o sz,
  (sz >= size_ftyp_nat (c_lo C) Ftyp_int16)%nat ->
  wf_operand C D P G o (Ftyp_ptrU sz r :: nil) ->
  wf_insn C D P (Insn_load x (Typ_ptrU 2 r) o) G (Nenv.add x (Ftyp_int16 :: nil) G)

| wf_insn_store : forall C D P G t r t' o1 o2,
  wf_operand C D P G o2 (Ftyp_ptr t' r :: nil) ->
  wf_operand C D P G o1 (flatten_typ (c_lo C) (c_tenv C) t) ->
  wf_typ (c_tenv C) D (Typ_ptr t' r) ->
  TS (c_tenv C) t' ->
  TS (c_tenv C) t ->
  ftyps_subset2 (flatten_typ (c_lo C) (c_tenv C) t) (flatten_typ (c_lo C) (c_tenv C) t') = true ->
  wf_insn C D P (Insn_store t o1 (Typ_ptr t' r) o2) G G
| wf_insn_storeU : forall C D P G o1 o2 sz sz' r t t',
  wf_operand C D P G o2 (Ftyp_ptrU sz' r :: nil) ->
  wf_operand C D P G o1 t' ->
  size_ftyps (c_lo C) t' <= Z.of_nat sz <= Z.of_nat sz' ->
  wf_insn C D P (Insn_store t o1 (Typ_ptrU sz r) o2) G G

| wf_insn_poolcheck : forall C D P G r t x x2 t',
  wf_operand C D P G (Op_reg x) (Ftyp_ptr t' r :: nil) ->
  wf_typ (c_tenv C) D (Typ_ptr t r) ->
  wf_insn C D P (Insn_poolcheck x2 r t (Op_reg x)) G (Nenv.add x2 (Ftyp_ptr t r :: nil) G)
| wf_insn_poolcheck_int : forall C D P G r t sz pf x x2,
  wf_operand C D P G (Op_reg x) (Ftyp_int sz pf :: nil) ->
  wf_typ (c_tenv C) D (Typ_ptr t r) ->
  (sz <= WORDSIZE_BITS)%nat ->
  wf_insn C D P (Insn_poolcheck x2 r t (Op_reg x)) G (Nenv.add x2 (Ftyp_ptr t r :: nil) G)
| wf_insn_poolcheckU : forall C D P G r sz sz' x x2,
  wf_operand C D P G (Op_reg x) (Ftyp_ptrU sz' r :: nil) ->
  wf_typ (c_tenv C) D (Typ_ptrU sz r) ->
  wf_insn C D P (Insn_poolcheckU x2 r sz (Op_reg x)) G (Nenv.add x2 (Ftyp_ptrU sz r :: nil) G)
| wf_insn_poolcheckU_int : forall C D P G r sz sz' pf' x x2,
  wf_operand C D P G (Op_reg x) (Ftyp_int sz' pf' :: nil) ->
  wf_typ (c_tenv C) D (Typ_ptrU sz r) ->
  (sz' <= WORDSIZE_BITS)%nat ->
  wf_insn C D P (Insn_poolcheckU x2 r sz (Op_reg x)) G (Nenv.add x2 (Ftyp_ptrU sz r :: nil) G)

| wf_insn_free : forall C D P G o t t' r,
  wf_operand C D P G o (Ftyp_ptr t' r :: nil) ->
  wf_typ (c_tenv C) D (Typ_ptr t r) ->  
  wf_insn C D P (Insn_free (Typ_ptr t r) o) G G
| wf_insn_free_int : forall C D P G o t r sz pf,
  wf_operand C D P G o (Ftyp_int sz pf :: nil) ->
  wf_typ (c_tenv C) D (Typ_ptr t r) ->  
  wf_insn C D P (Insn_free (Typ_ptr t r) o) G G
| wf_insn_freeU : forall C D P G o sz sz' r,
  wf_operand C D P G o (Ftyp_ptrU sz' r :: nil) ->
  wf_typ (c_tenv C) D (Typ_ptrU sz r) ->
  wf_insn C D P (Insn_free (Typ_ptrU sz r) o) G G
| wf_insn_freeU_int : forall C D P G o sz r sz' pf',
  wf_operand C D P G o (Ftyp_int sz' pf' :: nil) ->
  wf_typ (c_tenv C) D (Typ_ptrU sz r) ->
  wf_insn C D P (Insn_free (Typ_ptrU sz r) o) G G

| wf_insn_gep_name : forall C D P G x t' t'' o ls r t n ft lr x2 p sz pf i,
  t' = flatten_typ (c_lo C) (c_tenv C) (Typ_name x ls) ->
  t'' = flatten_typ (c_lo C) (c_tenv C) t ->
  t'' <> nil ->
  n = walk_offset3 (c_lo C) (c_tenv C) (nat_of_Z (Word.unsigned i)) (Typ_name x ls) ->
  (n < length t')%nat ->
  ftyps_subset t'' (skipn n t') = true ->
  Nenv.find x (c_tenv C) = Some (ft, lr, p) ->
  wf_operand C D P G o (Ftyp_ptr (Typ_name x ls) r :: nil) ->
  wf_const C D P (Const_int sz pf i) (Ftyp_int sz pf :: nil) ->
  wf_typ (c_tenv C) D t ->
  wf_typ (c_tenv C) D (Typ_ptr (Typ_name x ls) r) ->
  wf_insn C D P (Insn_gep x2 (Typ_ptr (Typ_name x ls) r) o t (Op_const (Const_int sz pf i))) G (Nenv.add x2 (Ftyp_ptr t r :: nil) G)
| wf_insn_gep_name2 : forall C D P G x t' t'' o ls r t ft lr x2 x3 p sz pf,
  t' = flatten_typ (c_lo C) (c_tenv C) (Typ_name x ls) ->
  t'' = flatten_typ (c_lo C) (c_tenv C) t ->
  t'' <> nil ->
  Nenv.find x (c_tenv C) = Some (ft, lr, p) ->
  wf_operand C D P G o (Ftyp_ptr (Typ_name x ls) r :: nil) ->
  wf_operand C D P G (Op_reg x3) (Ftyp_int sz pf :: nil) ->
  wf_typ (c_tenv C) D t ->
  wf_typ (c_tenv C) D (Typ_name x ls) ->
  wf_insn C D P (Insn_gep x2 (Typ_ptr (Typ_name x ls) r) o t (Op_reg x3)) G (Nenv.add x2 (Ftyp_ptr t r :: nil) G)

| wf_insn_gep_array : forall C D P G x o t sz r sz' pf' i,
  wf_operand C D P G o (Ftyp_ptr (Typ_array t sz) r :: nil) ->
  wf_const C D P (Const_int sz' pf' i) (Ftyp_int sz' pf' :: nil) ->
  wf_typ (c_tenv C) D (Typ_ptr (Typ_array t sz) r) ->
  Word.unsigned i < Z.of_nat sz < Word.modulus WORDSIZE_BITS ->
  (sz' <= WORDSIZE_BITS)%nat ->
  wf_insn C D P (Insn_gep x (Typ_ptr (Typ_array t sz) r) o t (Op_const (Const_int sz' pf' i))) G (Nenv.add x (Ftyp_ptr t r :: nil) G)
| wf_insn_gep_array2 : forall C D P G x o t sz r sz' pf' x2,
  wf_operand C D P G o (Ftyp_ptr (Typ_array t sz) r :: nil) ->
  wf_operand C D P G (Op_reg x2) (Ftyp_int sz' pf' :: nil) ->
  wf_typ (c_tenv C) D (Typ_ptr (Typ_array t sz) r) ->
  wf_insn C D P (Insn_gep x (Typ_ptr (Typ_array t sz) r) o t (Op_reg x2)) G (Nenv.add x (Ftyp_int WORDSIZE_BITS lt_63_MAX_I_BITS :: nil) G)

| wf_insn_gep1 : forall C D P G x t r o1 o2 sz pf,
  wf_operand C D P G o1 (Ftyp_ptr t r :: nil) ->
  wf_operand C D P G o2 (Ftyp_int sz pf :: nil) ->
  wf_typ (c_tenv C) D (Typ_ptr t r) ->
  wf_insn C D P (Insn_gep1 x (Typ_ptr t r) o1 o2) G (Nenv.add x (Ftyp_int WORDSIZE_BITS lt_63_MAX_I_BITS :: nil) G)
| wf_insn_gep1_int : forall C D P G x o1 o2 sz pf sz2 pf2 t r,
  wf_operand C D P G o1 (Ftyp_int sz2 pf2 :: nil) ->
  wf_operand C D P G o2 (Ftyp_int sz pf :: nil) ->
  wf_typ (c_tenv C) D (Typ_ptr t r) ->
  wf_insn C D P (Insn_gep1 x (Typ_ptr t r) o1 o2) G (Nenv.add x (Ftyp_int WORDSIZE_BITS lt_63_MAX_I_BITS :: nil) G)
| wf_insn_gep1_int2 : forall C D P G x o1 o2 sz pf sz2 pf2 sz3 pf3,
  wf_operand C D P G o1 (Ftyp_int sz2 pf2 :: nil) ->
  wf_operand C D P G o2 (Ftyp_int sz pf :: nil) ->
  wf_insn C D P (Insn_gep1 x (Typ_int sz3 pf3) o1 o2) G (Nenv.add x (Ftyp_int WORDSIZE_BITS lt_63_MAX_I_BITS :: nil) G)

| wf_insn_gepU : forall C D P G x sz r o sz' pf' i sz'',
  wf_operand C D P G o (Ftyp_ptrU sz'' r :: nil) ->
  wf_operand C D P G (Op_const (Const_int sz' pf' i)) (Ftyp_int sz' pf' :: nil) ->
  wf_typ (c_tenv C) D (Typ_ptrU sz r) ->
  Z.of_nat sz <= Z.of_nat sz'' < Word.modulus WORDSIZE_BITS ->
  wf_insn C D P (Insn_gepU x (Typ_ptrU sz r) o (Op_const (Const_int sz' pf' i))) G (Nenv.add x (Ftyp_ptrU (sz - nat_of_Z (Word.unsigned i)) r :: nil) G)
| wf_insn_gepU2 : forall C D P G x sz r o x2 sz' pf' sz'',
  wf_operand C D P G o (Ftyp_ptrU sz'' r :: nil) ->
  wf_operand C D P G (Op_reg x2) (Ftyp_int sz' pf' :: nil) ->
  wf_typ (c_tenv C) D (Typ_ptrU sz r) ->
  wf_insn C D P (Insn_gepU x (Typ_ptrU sz r) o (Op_reg x2)) G (Nenv.add x (Ftyp_ptrU 0 r :: nil) G)
| wf_insn_gepU3 : forall C D P G x sz1 pf1 r o1 o2 sz2 pf2 sz3,
  wf_operand C D P G o1 (Ftyp_int sz1 pf1 :: nil) ->
  wf_operand C D P G o2 (Ftyp_int sz2 pf2 :: nil) ->
  wf_typ (c_tenv C) D (Typ_ptrU sz3 r) ->
  wf_insn C D P (Insn_gepU x (Typ_ptrU sz3 r) o1 o2) G (Nenv.add x (Ftyp_ptrU 0 r :: nil) G)
| wf_insn_gepU_int : forall C D P G x o1 o2 sz pf sz2 pf2 sz3 pf3,
  wf_operand C D P G o1 (Ftyp_int sz pf :: nil) ->
  wf_operand C D P G o2 (Ftyp_int sz2 pf2 :: nil) ->
  wf_insn C D P (Insn_gepU x (Typ_int sz3 pf3) o1 o2) G (Nenv.add x (Ftyp_int WORDSIZE_BITS lt_63_MAX_I_BITS :: nil) G)
| wf_insn_gepU_int2 : forall C D P G x o1 o2 sz r sz2 pf2 sz3 pf3,
  wf_operand C D P G o1 (Ftyp_ptrU sz r :: nil) ->
  wf_operand C D P G o2 (Ftyp_int sz2 pf2 :: nil) ->
  wf_insn C D P (Insn_gepU x (Typ_int sz3 pf3) o1 o2) G (Nenv.add x (Ftyp_int WORDSIZE_BITS lt_63_MAX_I_BITS :: nil) G)

| wf_insn_insertvalue : forall C D P G x t1 o1 t2 o2 sz pf i t1' t2',
  t1' = flatten_typ (c_lo C) (c_tenv C) t1 ->
  t2' = flatten_typ (c_lo C) (c_tenv C) t2 ->
  wf_operand C D P G o1 t1' ->
  wf_operand C D P G o2 t2' ->
  wf_typ (c_tenv C) D t1 ->
  wf_typ (c_tenv C) D t2 ->
  ftyps_subset2 t2' (skipn (Z.to_nat (Word.unsigned i)) t1') = true ->
  (Z.to_nat (Word.unsigned i) + length t2' <= length t1')%nat ->
  wf_insn C D P (Insn_insertvalue x t1 o1 t2 o2 (Const_int sz pf i)) G (Nenv.add x t1' G)
| wf_insn_extractvalue : forall C D P G x t1 o t2 sz pf i t1' t2',
  t1' = flatten_typ (c_lo C) (c_tenv C) t1 ->
  t2' = flatten_typ (c_lo C) (c_tenv C) t2 ->
  wf_operand C D P G o t1' ->
  wf_typ (c_tenv C) D t1 ->
  wf_typ (c_tenv C) D t2 ->
  ftyps_subset t2' (skipn (Z.to_nat (Word.unsigned i)) t1') = true ->
  (Z.to_nat (Word.unsigned i) + length t2' <= length t1')%nat ->
  wf_insn C D P (Insn_extractvalue x t1 o t2 (Const_int sz pf i)) G (Nenv.add x t2' G)

| wf_insn_iconv : forall C D P G x t c o sz2 pf2,
  wf_operand C D P G o (flatten_typ (c_lo C) (c_tenv C) t) ->
  match c, t with
    | Iconv_trunc, Typ_int sz1 _ => (sz2 < sz1)%nat
    | Iconv_zext, Typ_int sz1 _ => (sz1 < sz2)%nat
    | Iconv_sext, Typ_int sz1 _ => (sz1 < sz2)%nat
    | Iconv_fptoui, Typ_float => True (* sz2 = 31%nat *)
    | Iconv_fptoui, Typ_double => True (* sz2 = 63%nat *)
    | Iconv_fptosi, Typ_float => True (* sz2 = 31%nat *)
    | Iconv_fptosi, Typ_double => True (* sz2 = 63%nat *)
    | _, _ => False
  end ->
  wf_insn C D P (Insn_iconv x c t o (Typ_int sz2 pf2)) G (Nenv.add x (Ftyp_int sz2 pf2 :: nil) G)

| wf_insn_fconv : forall C D P G x t c o,
  wf_operand C D P G o (flatten_typ (c_lo C) (c_tenv C) t) ->
  match t with
    | Typ_float => True
    | Typ_double => True
    | Typ_int _ _ => True
    | _ => False
  end ->
  wf_insn C D P (Insn_fconv x c t o Typ_float) G (Nenv.add x (Ftyp_float :: nil) G)
| wf_insn_fconv2 : forall C D P G x t c o,
  wf_operand C D P G o (flatten_typ (c_lo C) (c_tenv C) t) ->
  match t with
    | Typ_float => True
    | Typ_double => True
    | Typ_int _ _ => True
    | _ => False
  end ->
  wf_insn C D P (Insn_fconv x c t o Typ_double) G (Nenv.add x (Ftyp_double :: nil) G)

| wf_insn_bitcast : forall C D P G x o t1 t2 r,
  wf_operand C D P G o (Ftyp_ptr t1 r :: nil) ->
  wf_typ (c_tenv C) D (Typ_ptr t1 r) ->
  wf_typ (c_tenv C) D (Typ_ptr t2 r) ->
  ftyps_subset (flatten_typ (c_lo C) (c_tenv C) t2) (flatten_typ (c_lo C) (c_tenv C) t1) = true ->
  wf_insn C D P (Insn_bitcast x (Typ_ptr t1 r) o (Typ_ptr t2 r)) G (Nenv.add x (Ftyp_ptr t2 r :: nil) G)
| wf_insn_bitcastU : forall C D P G x o sz1 sz2 r,
  wf_operand C D P G o (Ftyp_ptrU sz1 r :: nil) ->
  wf_typ (c_tenv C) D (Typ_ptrU sz1 r) ->
  wf_typ (c_tenv C) D (Typ_ptrU sz2 r) ->
  Z.of_nat sz2 <= Z.of_nat sz1 ->
  wf_insn C D P (Insn_bitcast x (Typ_ptrU sz1 r) o (Typ_ptrU sz2 r)) G (Nenv.add x (Ftyp_ptrU sz2 r :: nil) G)

| wf_insn_ptrtoint : forall C D P G x t r o,
  wf_operand C D P G o (Ftyp_ptr t r :: nil) ->
  wf_typ (c_tenv C) D (Typ_ptr t r) ->
  wf_insn C D P (Insn_ptrtoint x (Typ_ptr t r) o Typ_int64) G (Nenv.add x (Ftyp_int64 :: nil) G)
| wf_insn_ptrtointU : forall C D P G x sz r o,
  wf_operand C D P G o (Ftyp_ptrU sz r :: nil) ->
  wf_typ (c_tenv C) D (Typ_ptrU sz r) ->
  wf_insn C D P (Insn_ptrtoint x (Typ_ptrU sz r) o Typ_int64) G (Nenv.add x (Ftyp_int64 :: nil) G)

| wf_insn_inttoptr : forall C D P G x o t r,
  wf_operand C D P G o (Ftyp_int64 :: nil) ->
  wf_typ (c_tenv C) D (Typ_ptr t r) ->
  wf_insn C D P (Insn_inttoptr x Typ_int64 o (Typ_ptr t r)) G (Nenv.add x (Ftyp_ptr t r :: nil) G)
| wf_insn_inttoptrU : forall C D P G x o sz r,
  wf_operand C D P G o (Ftyp_int64 :: nil) ->
  wf_typ (c_tenv C) D (Typ_ptrU sz r) ->
  wf_insn C D P (Insn_inttoptr x Typ_int64 o (Typ_ptrU sz r)) G (Nenv.add x (Ftyp_ptrU sz r :: nil) G)

| wf_insn_select : forall C D P G x t o o1 o2 t1 t2 t',
  wf_operand C D P G o (Ftyp_int1 :: nil) ->
  t' = flatten_typ (c_lo C) (c_tenv C) t ->
  wf_operand C D P G o1 t1 ->
  wf_operand C D P G o2 t2 ->
  wf_typ (c_tenv C) D t ->
  ftyps_weaken t1 t' = true ->
  ftyps_weaken t2 t' = true ->
  wf_insn C D P (Insn_select x Typ_int1 o t o1 t o2) G (Nenv.add x t' G)

| wf_insn_exit : forall C D P G,
  wf_insn C D P (Insn_exit) G G.
Hint Constructors wf_insn.

(* Well-formed phinode arguments
 * Makes sure that the phi node is well-formed for the label that we branch to
 * C; D; P; K; G |- phiargs @ l, t *)
Inductive wf_phi_args : config -> Delta -> Psi -> Gamma -> list (operand*lab) -> lab -> ftyps -> Prop :=
| wf_phi_args_match_ptr : forall C D P G o l ls t t' r,
  (* Note that we don't explicitly check that the operand is actually in the block
   * pointed to by the corresponding label. *)
  wf_operand C D P G o (Ftyp_ptr t' r :: nil) ->
  ftyps_subset (flatten_typ (c_lo C) (c_tenv C) t) (flatten_typ (c_lo C) (c_tenv C) t') = true ->
  wf_ftyp (c_tenv C) D (Ftyp_ptr t r) ->
  TS (c_tenv C) t ->
  TS (c_tenv C) t' ->
  wf_phi_args C D P G ((o,l)::ls) l (Ftyp_ptr t r :: nil)
| wf_phis_args_match_ptrU : forall C D P G o l ls sz sz' r,
  wf_operand C D P G o (Ftyp_ptrU sz' r :: nil) ->
  (sz' >= sz)%nat ->
  wf_ftyp (c_tenv C) D (Ftyp_ptrU sz r) ->
  wf_phi_args C D P G ((o,l)::ls) l (Ftyp_ptrU sz r :: nil)
| wf_phis_args_match : forall C D P G o l ls t t',
  wf_operand C D P G o t' ->
  ftyps_weaken t' t = true ->
  wf_phi_args C D P G ((o,l)::ls) l t
| wf_phi_args_nmatch : forall C D P G o l l' ls t,
  l <> l' ->
  wf_phi_args C D P G ls l t ->
  wf_phi_args C D P G ((o,l')::ls) l t.
Hint Constructors wf_phi_args.

(* Well-formed phinode
 * Under a config, code and global context, a phi instruction expects G1 and 
 * produces G2 at label l
 * C; D; P; K |- phinode : G1 -> G2 @ l *)
Inductive wf_phinode : config -> Delta -> Psi -> phinode -> lab -> Gamma -> Gamma -> Prop :=
| wf_phi : forall C D P G ls t t' x l,
  t' = (flatten_typ (c_lo C) (c_tenv C) t) ->
  wf_phi_args C D P G ls l t' ->
  wf_phinode C D P (Insn_phi x t ls) l G (Nenv.add x t' G).
Hint Constructors wf_phinode. 

(* Well-formed phiblock
 * Under a config, code and global context, a phi block has precondition G1 
 * and postcondition G2 at label l
 * C; D; P; K |- phiblock : G1 -> G2 @ l *)
Inductive wf_phi_blk : config -> Delta -> Psi -> phiblock -> lab -> Gamma -> Gamma -> Prop :=
| wf_phi_blk_nil : forall C D P G l,
  wf_phi_blk C D P nil l G G
| wf_phi_blk_cons : forall C D P G1 G2 G3 l phi phis,
  wf_phinode C D P phi l G1 G2 ->
  wf_phi_blk C D P phis l G2 G3 ->
  wf_phi_blk C D P (phi::phis) l G1 G3.
Hint Constructors wf_phi_blk.

(* G1 subset G2 *)
Definition extends_gamma (G1 G2:Gamma) : Prop :=
  forall x t,
    Nenv.find x G1 = Some t ->
    Nenv.find x G2 = Some t.

(* Well-formed junction point
 * Under a config, code, global, typ context, and function body, a branch to 
 * l2 coming from l1 is well-formed
 * C; P; K; G; bs |- l2 @ l1 *)
Definition wf_junction (C:config) (D:Delta) (P:Psi) (G1:Gamma) (bs:blocks) (l1 l2:lab) : Prop :=
  exists G2, exists G3, exists b, 
    Ienv.find l2 P = Some G2 /\
    lookup_blk l2 bs = Some b /\
    extends_gamma G2 G3 /\
    wf_phi_blk C D P (b_phis b) l1 G1 G3.

Inductive wf_switch_arms : config -> Delta -> Psi -> Gamma -> blocks -> typ -> lab -> list (typ * const * lab) -> Prop :=
| wf_switch_arms_nil : forall C D P G bs sz pf l,
  wf_switch_arms C D P G bs (Typ_int sz pf) l nil
| wf_switch_arms_cons : forall C D P G bs sz pf i l l' ls,
  wf_junction C D P G bs l l' ->
  wf_switch_arms C D P G bs (Typ_int sz pf) l ls ->
  wf_switch_arms C D P G bs (Typ_int sz pf) l ((Typ_int sz pf,(Const_int sz pf i),l')::ls).
Hint Constructors wf_switch_arms.

Inductive wf_indirect_br_arms : config -> Delta -> Psi -> Gamma -> blocks -> lab -> list lab -> Prop :=
| wf_indirect_br_arms_nil : forall C D P G bs l,
  wf_indirect_br_arms C D P G bs l nil
| wf_indirect_br_arms_cons : forall C D P G bs l l' ls,
  wf_junction C D P G bs l l' ->
  wf_indirect_br_arms C D P G bs l ls ->
  wf_indirect_br_arms C D P G bs l (l'::ls).
Hint Constructors wf_indirect_br_arms.

(* Well-formed terminator instruction
 * Under a config, code, global, typ context, and function body, a terminator 
 * is well-formed at label l
 * C; D; P; K; G; bs |- term @ l *)
Inductive wf_term : config -> Delta -> Psi -> Gamma -> blocks -> lab -> terminator -> Prop :=
| wf_insn_return : forall C D P G o t t' l bs,
  t' = flatten_typ (c_lo C) (c_tenv C) t ->
  wf_operand C D P G o t' ->
  wf_typ (c_tenv C) D t ->
  wf_term C D P G bs l (Insn_return t o)
| wf_insn_return_void : forall C D P G l bs,
  wf_term C D P G bs l Insn_return_void
| wf_br_uncond : forall C D P G l l' bs,
  wf_junction C D P G bs l l' ->
  wf_term C D P G bs l (Insn_br_uncond l')
| wf_br : forall C D P G l l1 l2 o bs,
  wf_junction C D P G bs l l1 ->
  wf_junction C D P G bs l l2 ->
  wf_operand C D P G o (Ftyp_int1 :: nil) ->
  wf_term C D P G bs l (Insn_br o l1 l2)
| wf_switch : forall C D P G o ldef ls sz (i:Word.int sz) pf l bs,
  wf_junction C D P G bs l ldef ->
  wf_switch_arms C D P G bs (Typ_int sz pf) l ls ->
  wf_operand C D P G o (Ftyp_int sz pf :: nil) ->
  wf_term C D P G bs l (Insn_switch (Typ_int sz pf) o ldef ls)
| wf_indirect_br : forall C D P G ls o l bs r,
  wf_indirect_br_arms C D P G bs l ls ->
  match o with
    | Op_reg x => Nenv.find x G = Some (Ftyp_ptr Typ_int8 r :: nil)
    | Op_const (Const_baddr _ _) => True
    | _ => False
  end ->
  wf_term C D P G bs l (Insn_indirect_br (Typ_ptr Typ_int8 r) o ls)
| wf_unreachable : forall C D P G bs l,
  wf_term C D P G bs l (Insn_unreachable).
Hint Constructors wf_term.

(* Well-formed argument list
 * Under a config, code, global and typ context, the arguments list matches
 * the signature
 * C; D; P; K; G; rmap |- args : sig *)
Inductive wf_args : config -> Delta -> Psi -> Gamma -> Nenv.t rgn -> list operand -> list typ -> Prop :=
| wf_arg_nil : forall fs lo tenv D P G rmap,
  wf_args (mk_config fs lo tenv) D P G rmap nil nil
| wf_arg_cons : forall fs lo tenv D P G args' t' t t'' o sig' rmap,
  t' = sigma rmap (flatten_typ lo tenv t) -> 
  ftyps_weaken t'' t' = true ->
  wf_operand (mk_config fs lo tenv) D P G o t'' ->
  wf_args (mk_config fs lo tenv) D P G rmap args' sig' ->
  wf_args (mk_config fs lo tenv) D P G rmap (o :: args') (t :: sig').
Hint Constructors wf_args.

(* Well-formed polymorphic instatiation *)
Inductive wf_prgn_inst : Delta -> list rgn -> Prop :=
| wf_prgn_inst_nil : forall D,
  wf_prgn_inst D nil
| wf_prgn_inst_cons : forall D prgn prgns t,
  Nenv.find prgn D = Some t ->
  wf_prgn_inst D prgns ->
  wf_prgn_inst D (prgn::prgns).
Hint Constructors wf_prgn_inst.

(* Well-formed non-deterministic instruction
 * Under a config, code, typ, global context, and function body, a non-deterministic 
 * instruction is well-formed at label l
 * C; D; P; K; G; bs |- nd @ l *)
Inductive wf_nd : config -> Delta -> Psi -> Gamma -> blocks -> insn_nd -> lab -> Prop :=
| wf_insn_call : forall fs lo tenv D P x o args l t' l' t fprgns prgns sig G bs t'',
  ftyps_weaken t' (flatten_typ lo tenv t'') = true ->
  t' = sigma (inst_prgn fprgns prgns) (flatten_typ lo tenv t) ->
  wf_ftyps tenv D t' ->
  wf_args (mk_config fs lo tenv) D P G (inst_prgn fprgns prgns) args sig ->
  wf_prgn_inst D prgns ->
  wf_operand (mk_config fs lo tenv) D P G o (Ftyp_fun fprgns sig (Some t) :: nil) ->
  wf_term (mk_config fs lo tenv) D P (Nenv.add x (flatten_typ lo tenv t'') G) bs l' (Insn_br_uncond l) ->
  length fprgns = length prgns ->
  wf_nd (mk_config fs lo tenv) D P G bs (Insn_call (Some x) (Some t'') o prgns args l) l'
| wf_insn_call_void : forall fs lo tenv D P o args l l' fprgns prgns sig G bs,
  wf_args (mk_config fs lo tenv) D P G (inst_prgn fprgns prgns) args sig ->
  wf_prgn_inst D prgns ->
  wf_operand (mk_config fs lo tenv) D P G o (Ftyp_fun fprgns sig None :: nil) ->
  wf_term (mk_config fs lo tenv) D P G bs l' (Insn_br_uncond l) ->
  length fprgns = length prgns ->
  wf_nd (mk_config fs lo tenv) D P G bs (Insn_call None None o prgns args l) l'
| wf_insn_malloc : forall fs lo tenv D P G x r t l l' bs o sz pf,
  wf_operand (mk_config fs lo tenv) D P G o (Ftyp_int sz pf :: nil) ->
  wf_typ tenv D t ->
  Nenv.find r D = Some t ->
  wf_term (mk_config fs lo tenv) D P (Nenv.add x (Ftyp_ptr t r :: nil) G) bs l' (Insn_br_uncond l) ->
  wf_nd (mk_config fs lo tenv) D P G bs (Insn_malloc x (Some t) r o l) l'
| wf_insn_mallocU : forall fs lo tenv D P G x r l l' bs x2 sz pf,
  wf_operand (mk_config fs lo tenv) D P G (Op_reg x2) (Ftyp_int sz pf :: nil) ->
  wf_term (mk_config fs lo tenv) D P (Nenv.add x (Ftyp_ptrU 0 r :: nil) G) bs l' (Insn_br_uncond l) ->
  wf_nd (mk_config fs lo tenv) D P G bs (Insn_malloc x None r (Op_reg x2) l) l'
| wf_insn_mallocU2 : forall fs lo tenv D P G x r l l' bs sz pf i,
  wf_operand (mk_config fs lo tenv) D P G (Op_const (Const_int sz pf i)) (Ftyp_int sz pf :: nil) ->
  wf_term (mk_config fs lo tenv) D P (Nenv.add x (Ftyp_ptrU (nat_of_Z (Word.unsigned i)) r :: nil) G) bs l' (Insn_br_uncond l) ->
  wf_nd (mk_config fs lo tenv) D P G bs (Insn_malloc x None r (Op_const (Const_int sz pf i)) l) l'
| wf_insn_unsafe_call_bind : forall fs lo tenv D P G bs x t op os l l',
  wf_term (mk_config fs lo tenv) D P (Nenv.add x (flatten_typ lo tenv t) G) bs l' (Insn_br_uncond l) ->
  wf_nd (mk_config fs lo tenv) D P G bs (Insn_unsafe_call (Some(x, t)) op os l) l'
| wf_insn_unsafe_call : forall fs lo tenv D P G bs op os l l',
  wf_nd (mk_config fs lo tenv) D P G bs (Insn_unsafe_call None op os l) l'.
Hint Constructors wf_nd.

(* Well-formed instruction sequence
 * Under a config, code, global context, and function body, an instruction
 * sequence has a precondition G at label l
 * C; D; P; K; bs |- insns, ndterm : G @ l*)
Inductive wf_insns_ndterm : config -> Delta -> Psi -> blocks -> lab -> list insn -> insn_nd_term -> Gamma -> Prop :=
| wf_insns_nil_nd : forall C D P G nd l bs,
  wf_nd C D P G bs nd l ->
  wf_insns_ndterm C D P bs l nil (Insn_nd nd) G
| wf_insns_nil_term : forall C D P G t l bs,
  wf_term C D P G bs l t ->
  wf_insns_ndterm C D P bs l nil (Insn_term t) G
| wf_insns_cons : forall C D P G1 G2 i insns' t l bs,
  wf_insn C D P i G1 G2 ->
  wf_insns_ndterm C D P bs l insns' t G2 ->
  wf_insns_ndterm C D P bs l (i::insns') t G1.
Hint Constructors wf_insns_ndterm.

(* Well-formed function body
 * Under a config, code and global context, check that the function body is
 * well-formed
 * C; D1; D2; P; K |- f *)
Definition wf_fbody (C:config) (D1 D2:Delta) (P:Psi) (f:function) : Prop :=
  (forall l G, Ienv.find l P = Some G -> 
    exists b, lookup_blk l (f_body f) = Some b) /\
  (forall l b, lookup_blk l (f_body f) = Some b -> 
    exists G, Ienv.find l P = Some G) /\
  (forall l G, Ienv.find l P = Some G ->
    (exists b,
      lookup_blk l (f_body f) = Some b /\
      wf_insns_ndterm C D2 P (f_body f) (b_lab b) (b_insns b) (b_nd_term b) G /\
      (match b_nd_term b with
         | Insn_term (Insn_return t x) => (f_ret f) = Some t /\ wf_ftyps (c_tenv C) D1 (flatten_typ (c_lo C) (c_tenv C) t)
         | Insn_term Insn_return_void => f_ret f = None
         | _ => True
       end))).

(* Well-formed function parameters
 * Under a config and typ context, checks that the function parameters 
 * have the correct signature
 * C; D; G |- params : sig *)
Inductive wf_fparams : config -> Delta -> list id -> list typ -> Gamma -> Prop :=
| wf_fparams_nil : forall C D G,
  Nenv.Equal G (Nenv.empty ftyps) ->
  wf_fparams C D nil nil G
| wf_fparams_cons : forall C D x ids tls G t t' G',
  t' = (flatten_typ (c_lo C) (c_tenv C) t) ->
  wf_ftyps (c_tenv C) D t' ->
  Nenv.Equal G' (Nenv.add x t' G) ->
  wf_fparams C D ids tls G ->
  wf_fparams C D (x::ids) (t::tls) G'.
Hint Constructors wf_fparams.

(* Well-formed polymorphic regions *)
Inductive wf_prgns : list (rgn*typ) -> Delta -> Prop :=
| wf_prgns_nil : forall D,
  Nenv.Equal D (Nenv.empty typ) ->
  wf_prgns nil D
| wf_prgns_cons : forall r t rgns D D',
  wf_prgns rgns D ->
  Nenv.Equal D' (Nenv.add r t D) ->
  wf_prgns ((r,t)::rgns) D'.
Hint Constructors wf_prgns.

(* Well-formed local regions *)
Inductive wf_lrgns : config -> list (rgn*typ) -> Delta -> Delta -> Prop :=
| wf_lrgns_nil : forall C D,
  wf_lrgns C nil D D
| wf_lrgns_cons : forall C D1 D2 r t rgns,
  Nenv.find r D2 = None ->
  wf_lrgns C rgns D1 D2 ->
  wf_lrgns C ((r,t)::rgns) D1 (Nenv.add r t D2).
Hint Constructors wf_lrgns.

(* Well-formed function
 * Under a config, code, global context, a function is well-formed
 * C; D1; D2; P; K |- f *)
Definition wf_function (C:config) (D1 D2:Delta) (P:Psi) (f:function) : Prop :=
  exists G, Ienv.find (f_lab f) P = Some G /\
    exists G', exists D1', exists D2',
      Nenv.Equal G G' /\
      Nenv.Equal D1 D1' /\
      Nenv.Equal D2 D2' /\
      wf_fparams C D1 (f_params f) (f_sig f) G' /\
      list_disjoint (domain (f_lrgn f)) (domain (f_prgn f)) /\
      list_norepet (domain (f_prgn f)) /\
      list_norepet (domain (f_lrgn f)) /\
      wf_prgns (f_prgn f) D1' /\
      wf_lrgns C (f_lrgn f) D1' D2' /\
      Forall (fun t => wf_ftyps (c_tenv C) D2 (flatten_typ (c_lo C) (c_tenv C) t)) (range (f_lrgn f)) /\
      wf_fbody C D1 D2 P f.

(* Well-formed code context (checks all the basic blocks and make sure
 * they belong to a function body)
 * C; K |- FS : (FT, FD) *)
Definition wf_functions (C:config) (FT:Ienv.t Psi) (FD:Ienv.t (Delta*Delta)): Prop :=
  (forall f, lookup_fun (f_lab f) (c_fs C) = Some f ->
    exists D1, exists D2, Ienv.find (f_lab f) FD = Some (D1,D2) /\
      exists P, Ienv.find (f_lab f) FT = Some P /\
          wf_function C D1 D2 P f).
