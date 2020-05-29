(* Coq standard library imports *)
Require Import Znumtheory.


(* Other library imports *)
Add LoadPath "../libs".
Add LoadPath "../libs/CompCert-Toolkit".
Require Import Coqlib.
Require Import Axioms.
Require Import Tactics.
Require Import Consider.

(* Illvm imports *)
Require Import Utility.
Require Import IllvmAST.


(* ---------------------------------------------------------------------- *)
(* Layout *)

(* The layout only tracks alignment of primitive types. Size of primitive
 * types could be parameterized here as well, but our very concrete semantics
 * will assume 64-bit pointers. Thus, functions also are 64-bits *)
Record layout := mk_layout {
  endian : bool;
  lo_float_half_info : nat;    (* alignment *)
  lo_float_float_info : nat;  (* alignment *)
  lo_float_double_info : nat;  (* alignment *)
  lo_float_fp128_info : nat;   (* alignment *)
  lo_ptr_info : nat;           (* alignment *)
  lo_fun_info : nat            (* alignment *)
}.

(* ---------------------------------------------------------------------- *)
(* Size of a primitive type in bytes. *)
Definition size_ftyp (lo:layout) (ft:ftyp) : Z :=
  match ft with
    | Ftyp_float => 4
    | Ftyp_double => 8
    | Ftyp_int sz pf => (Z_of_nat sz / 8 + 1)
    | Ftyp_ptr _ _ => WORDSIZE
    | Ftyp_fun _ _ _ => WORDSIZE
    | Ftyp_ptrU _ _ => WORDSIZE
  end.
Definition size_ftyp_nat (lo:layout) (ft:ftyp) : nat :=
  nat_of_Z (size_ftyp lo ft).

(* Cumulative size of a list of primitive typs *)
Fixpoint size_ftyps (lo:layout) (ftls:ftyps) : Z :=
  match ftls with
    | nil => 0
    | ft'::ftls' => size_ftyp lo ft' + size_ftyps lo ftls'
  end.
Definition size_ftyps_nat (lo:layout) (ftls:ftyps) : nat :=
  nat_of_Z (size_ftyps lo ftls).

Definition ftyp_max := 32.

Definition align_ftyp (lo:layout) (ft:ftyp) : Z :=
  match ft with
    | Ftyp_float => Z_of_nat (lo_float_float_info lo)
    | Ftyp_double => Z_of_nat (lo_float_double_info lo)
    | Ftyp_int sz pf => Z_of_nat sz / 8 + 1
    | Ftyp_ptr _ _ => Z_of_nat (lo_ptr_info lo)
    | Ftyp_fun _ _ _ => Z_of_nat (lo_fun_info lo)
    | Ftyp_ptrU _ _ => Z_of_nat (lo_ptr_info lo)
  end.

(* ---------------------------------------------------------------------- *)
Lemma size_ptr_fun_same : forall lo t r lr ls ret,
  size_ftyp lo (Ftyp_ptr t r) = size_ftyp lo (Ftyp_fun lr ls ret).
Proof.
  unfold size_ftyp; crush.
Qed.

Lemma size_ftyp_nonneg : forall lo t,
  size_ftyp lo t >= 0.
Proof.
  induction t; simpl; unfold WORDSIZE; crush.
  assert (8 > 0). omega.
  assert (0 <= Z.of_nat sz). omega.
  specialize (Z_div_pos (Z.of_nat sz) 8 H H0); intros. omega.
Qed.

Lemma size_ftyps_nonneg : forall lo t,
  size_ftyps lo t >= 0.
Proof.
  induction t; crush. assert (size_ftyp lo a >= 0). apply size_ftyp_nonneg. omega.
Qed.

Lemma size_ftyp_max : forall lo t,
  size_ftyp lo t < ftyp_max.
Proof.
  unfold ftyp_max; induction t; simpl; unfold WORDSIZE; crush. 
  unfold MAX_I_BITS in *.
  assert (Z.of_nat sz < 128). omega.
  assert (0 < 8). omega.
  assert (Z.of_nat sz < 8 * 16). omega.
  eapply Z.div_lt_upper_bound in H1; eauto. omega.
Qed.

(* ---------------------------------------------------------------------- *)  
(* Region instantiation *)

(* rmap(r) *)
Definition alpha (rmap:Nenv.t rgn) (r:rgn) : rgn :=
  match Nenv.find r rmap with
    | Some r' => r'
    | None => r
  end.

(* t[rmap] *)
Fixpoint sigma'' (rmap:Nenv.t rgn) (t:typ) :=
  match t with
    | Typ_ptr t' r' => Typ_ptr (sigma'' rmap t') (alpha rmap r')
    | Typ_name x lr => Typ_name x (map (alpha rmap) lr)
    | Typ_array t' sz => Typ_array (sigma'' rmap t') sz
    | Typ_ptrU sz r' => Typ_ptrU sz (alpha rmap r')
    | _ => t
  end.
Definition sigma' (rmap:Nenv.t rgn) (t:ftyp) : ftyp :=
  match t with
    | Ftyp_ptr t' r' => Ftyp_ptr (sigma'' rmap t') (alpha rmap r')
    | Ftyp_ptrU sz r' => Ftyp_ptrU sz (alpha rmap r')
    | _ => t
  end.
Definition sigma (rmap:Nenv.t rgn) (t:ftyps) : ftyps :=
  map (sigma' rmap) t.

(* Instantiate a polymophic region map *)
Fixpoint inst_prgn (prgn1 prgn2:list rgn) : (Nenv.t rgn) :=
  match prgn1, prgn2 with
    | p1::prgn1', p2::prgn2' => Nenv.add p1 p2 (inst_prgn prgn1' prgn2')
    | _, _ => Nenv.empty rgn
  end.

(* ---------------------------------------------------------------------- *)  
(* Name environment *)

(* name -> (primitive type list, polymoprhic regions, packed *)
Definition tenv_t := Nenv.t (ftyps * list rgn * bool).

Definition align_Z (n m:Z) : Z :=
  if (zeq (n mod m) 0) then n else n + m - (n mod m).

Fixpoint pad_ftyps (lo:layout) (ts:ftyps) : ftyps :=
  match ts with
    | nil => nil
    | t::ts => let n := nat_of_Z ((align_Z (size_ftyp lo t) (align_ftyp lo t))) in
      t :: (list_repeat (n - (size_ftyp_nat lo t)) Ftyp_int8) ++ pad_ftyps lo ts
  end.

(* Flattens a typ to a list of typs, or a singleton if it is not an aggregate typ *)
Fixpoint flatten_typ (lo:layout) (tenv:tenv_t) (t:typ) : ftyps :=
  match t with
    | Typ_float => Ftyp_float :: nil
    | Typ_double => Ftyp_double :: nil
    | Typ_int sz pf => Ftyp_int sz pf :: nil
    | Typ_ptr t' r => Ftyp_ptr t' r :: nil
    | Typ_name x lr1 => 
      match Nenv.find x tenv with
        | Some (t', lr2, packed) => 
          if packed
            then (sigma (inst_prgn lr2 lr1) t')
            else pad_ftyps lo (sigma (inst_prgn lr2 lr1) t')
        | None => nil
      end
    | Typ_fun lr ls t => Ftyp_fun lr ls t :: nil
    | Typ_array t' sz => 
      let t'' := flatten_typ lo tenv t' in
        (fix go (sz:nat) :=
        match sz with
          | O => nil
          | S sz => t'' ++ go sz
        end) sz
    | Typ_ptrU sz r => Ftyp_ptrU sz r :: nil
  end.

Lemma sigma_nil : forall t rmap,
  sigma rmap t = nil ->
  t = nil.
Proof.
  induction t; simpl; intros; auto. inv H.
Qed.

Lemma sigma_not_nil : forall t rmap,
  t <> nil ->
  sigma rmap t <> nil.
Proof.
  induction t; simpl; intros; eauto. destruct t; crush.
Qed.

Lemma size_ftyp_sigma_inv : forall t lo rmap, 
  size_ftyp lo (sigma' rmap t) = size_ftyp lo t.
Proof.
  induction t; crush.
Qed.

Lemma size_ftyps_sigma_inv : forall t lo rmap, 
  size_ftyps lo (sigma rmap t) = size_ftyps lo t.
Proof.
  induction t; simpl; intros; auto.
  rewrite IHt. rewrite size_ftyp_sigma_inv. auto.
Qed.

Lemma align_ftyp_sigma_inv : forall t lo rmap, 
  align_ftyp lo (sigma' rmap t) = align_ftyp lo t.
Proof.
  induction t; crush.
Qed.

Lemma pad_ftyps_sigma_comm_byte : forall n rmap,
  list_repeat n Ftyp_int8 = map (sigma' rmap) (list_repeat n Ftyp_int8).
Proof.
  induction n; crush.
Qed.

Lemma pad_ftyps_sigma_comm : forall t lo rmap,
  pad_ftyps lo (sigma rmap t) = sigma rmap (pad_ftyps lo t).
Proof.
  induction t; crush. f_equal. unfold sigma. rewrite list_append_map. f_equal.
  rewrite size_ftyp_sigma_inv. unfold size_ftyp_nat.
  rewrite align_ftyp_sigma_inv. rewrite size_ftyp_sigma_inv.
  apply pad_ftyps_sigma_comm_byte.
Qed.

Lemma bytes_sigma_inv : forall sz rmap,
  list_repeat sz Ftyp_int8 = sigma rmap (list_repeat sz Ftyp_int8).
Proof.
  induction sz; crush.
Qed.

Lemma size_ftyps_linear : forall t1 t2 lo,
  size_ftyps lo (t1 ++ t2) = size_ftyps lo t1 + size_ftyps lo t2.
Proof.
  induction t1; simpl; intros; auto. rewrite IHt1. omega.
Qed.

(* ---------------------------------------------------------------------- *)
(* Well-formed type environment type *)

Inductive wf_tenv_typ : list rgn -> typ -> Prop :=
| wf_tenv_typ_float : forall D,
  wf_tenv_typ D (Typ_float)
| wf_tenv_typ_double : forall D,
  wf_tenv_typ D (Typ_double)
| wf_tenv_typ_int : forall D sz pf,
  wf_tenv_typ D (Typ_int sz pf)
| wf_tenv_typ_ptr : forall D t r,
  In r D ->
  wf_tenv_typ D t ->
  wf_tenv_typ D (Typ_ptr t r)
| wf_tenv_typ_name : forall D x lr1,
  Forall (fun r => In r D) lr1 ->
  wf_tenv_typ D (Typ_name x lr1)
| wf_tenv_typ_fun : forall D prgn sig t,
  Forall (fun t => wf_tenv_typ prgn t) sig ->
  wf_tenv_typ prgn t ->
  wf_tenv_typ D (Typ_fun prgn sig (Some t))
| wf_tenv_typ_fun2 : forall D prgn sig,
  Forall (fun t => wf_tenv_typ prgn t) sig ->
  wf_tenv_typ D (Typ_fun prgn sig None)
| wf_tenv_typ_array : forall D t sz,
  wf_tenv_typ D t ->
  wf_tenv_typ D (Typ_array t sz)
| wf_tenv_typ_ptrU : forall D sz r,
  In r D ->
  wf_tenv_typ D (Typ_ptrU sz r).
Hint Constructors wf_tenv_typ.

Inductive wf_tenv_ftyp : list rgn -> ftyp -> Prop :=
| wf_tenv_ftyp_float : forall D,
  wf_tenv_ftyp D (Ftyp_float)
| wf_tenv_ftyp_double : forall D,
  wf_tenv_ftyp D (Ftyp_double)
| wf_tenv_ftyp_int : forall D sz pf,
  wf_tenv_ftyp D (Ftyp_int sz pf)
| wf_tenv_ftyp_ptr : forall D t r,
  In r D ->
  wf_tenv_typ D t ->
  wf_tenv_ftyp D (Ftyp_ptr t r)
| wf_tenv_ftyp_fun : forall D prgn sig t,
  Forall (fun t => wf_tenv_typ prgn t) sig ->
  wf_tenv_typ prgn t ->
  wf_tenv_ftyp D (Ftyp_fun prgn sig (Some t))
| wf_tenv_ftyp_fun2 : forall D prgn sig,
  Forall (fun t => wf_tenv_typ prgn t) sig ->
  wf_tenv_ftyp D (Ftyp_fun prgn sig None)
| wf_tenv_ftyp_ptrU : forall D sz r,
  In r D ->
  wf_tenv_ftyp D (Ftyp_ptrU sz r).
Hint Constructors wf_tenv_ftyp.

Inductive wf_tenv_ftyps : list rgn -> ftyps -> Prop :=
| wf_tenv_ftyps_nil : forall D,
  wf_tenv_ftyps D nil
| wf_tenv_ftyps_cons : forall D t ts,
  wf_tenv_ftyp D t ->
  wf_tenv_ftyps D ts ->
  wf_tenv_ftyps D (t::ts).
Hint Constructors wf_tenv_ftyps.

Lemma wf_tenv_typ_live_ext : forall live rgns t,
  wf_tenv_typ live t ->
  wf_tenv_typ (rgns ++ live) t.
Proof.
  induction 1; auto; crush. 
  constructor. generalize dependent rgns.
  induction lr1; crush. inv H. constructor; crush. 
Qed.

Lemma wf_tenv_ftyp_live_ext : forall live rgns t,
  wf_tenv_ftyp live t ->
  wf_tenv_ftyp (rgns ++ live) t.
Proof.
  induction 1; auto; crush.
  constructor; crush. apply wf_tenv_typ_live_ext; auto.
Qed.

(* -------------------------------------------------------------------------- *)

(* Well-formed typ environment *)
Definition wf_tenv (tenv:tenv_t) : Prop :=
  forall x t lr2 p,
    Nenv.find x tenv = Some (t, lr2, p) ->
    wf_tenv_ftyps lr2 t /\ t <> nil.

(* Type scheme for checking name application is correct *)
Fixpoint TS (tenv:tenv_t) (t:typ) : Prop :=
  match t with
    | Typ_name x lr1 => 
      match Nenv.find x tenv with
        | Some (t, lr2, _) => length lr1 = length lr2
        | None => False
      end
    | Typ_array t _ => TS tenv t
    | Typ_ptr t _ => TS tenv t
    | _ => True
  end.

Lemma alpha_comm : forall lr2 rmap r lr1,
  length lr1 = length lr2 ->
  In r lr2 ->
  alpha rmap (alpha (inst_prgn lr2 lr1) r) = alpha (inst_prgn lr2 (map (alpha rmap) lr1)) r.
Proof.
  induction lr2; destruct lr1; unfold alpha in *; crush.
  { rewrite NFacts.add_eq_o; crush. rewrite NFacts.add_eq_o; crush. }
  { destruct (eq_nat_dec r a); subst.
    rewrite NFacts.add_eq_o in *; crush.
    rewrite NFacts.add_eq_o in *; crush.
    rewrite NFacts.add_neq_o in *; crush.
    rewrite NFacts.add_neq_o in *; crush. }
Qed.

Lemma typ_sigma_comm : forall rmap t lr2 lr1,
  length lr1 = length lr2 ->
  wf_tenv_typ lr2 t ->
  sigma'' rmap (sigma'' (inst_prgn lr2 lr1) t) = sigma'' (inst_prgn lr2 (map (alpha rmap) lr1)) t.
Proof.
  induction t; crush.
  { inv H0. f_equal; auto. apply alpha_comm; auto. }
  { inv H0. f_equal; auto. 
    induction lr; crush. inv H3. f_equal; auto. apply alpha_comm; auto. }
  { inv H0. f_equal; auto. }
  { inv H0. f_equal; auto. apply alpha_comm; auto. }
Qed.

Lemma ftyp_sigma_comm : forall rmap t lr2 lr1,
  length lr1 = length lr2 ->
  wf_tenv_ftyp lr2 t ->
  sigma' rmap (sigma' (inst_prgn lr2 lr1) t) = sigma' (inst_prgn lr2 (map (alpha rmap) lr1)) t.
Proof.
  induction t; crush. 
  { inv H0. f_equal. apply typ_sigma_comm; auto. apply alpha_comm; auto. }
  { inv H0. f_equal. apply alpha_comm; auto. }
Qed.

Lemma ftyps_sigma_comm : forall rmap t lr2 lr1,
  length lr1 = length lr2 ->
  wf_tenv_ftyps lr2 t ->
  sigma rmap (sigma (inst_prgn lr2 lr1) t) = sigma (inst_prgn lr2 (map (alpha rmap) lr1)) t.
Proof.
  induction t; simpl; intros; auto.
  inv H0. f_equal; auto. apply ftyp_sigma_comm; auto.
Qed.

(* We can commute flattening and instantiating regions. *) 
Lemma flatten_sigma_comm : forall lo tenv t rmap,
  wf_tenv tenv ->
  TS tenv t ->
  (sigma rmap (flatten_typ lo tenv t)) = flatten_typ lo tenv (sigma'' rmap t).
Proof.
  induction t; simpl; intros; auto. 
  { case_eq (Nenv.find x tenv); auto; intros. destruct p; auto. destruct p; auto.
    rewrite H1 in H0. unfold wf_tenv in H. apply H in H1. destruct H1.
    eapply ftyps_sigma_comm in H1; eauto. erewrite <- H1. 
    destruct b; auto. erewrite <- pad_ftyps_sigma_comm; eauto. }
  { induction sz; auto. unfold sigma in *.
    rewrite map_app. f_equal; eauto. }
Qed.

(* -------------------------------------------------------------------------- *)
Ltac size_ftyp_prop :=
  repeat
  match goal with
    | [H: context [ size_ftyp ?lo ?t ] |- _ ] =>
      match goal with
        | [ _ : size_ftyp ?lo ?t >= 0 |- _ ] => idtac
        | [ H: _ |- _ ] => specialize (size_ftyp_nonneg lo t); intros
      end
    | [H: context [ size_ftyps ?lo ?t ] |- _ ] =>
      match goal with
        | [ _ : size_ftyps ?lo ?t >= 0 |- _ ] => idtac
        | [ H: _ |- _ ] => specialize (size_ftyps_nonneg lo t); intros
      end
    | [ |- context [ size_ftyp ?lo ?t ] ] =>
      match goal with
        | [ _ : size_ftyp ?lo ?t >= 0 |- _ ] => idtac
        | [ H: _ |- _ ] => specialize (size_ftyp_nonneg lo t); intros
      end
    | [ |- context [ size_ftyps ?lo ?t ] ] =>
      match goal with
        | [ _ : size_ftyps ?lo ?t >= 0 |- _ ] => idtac
        | [ H: _ |- _ ] => specialize (size_ftyps_nonneg lo t); intros
      end
  end.

(* -------------------------------------------------------------------------- *)
(* Width subtyping (arguments are in order of subset inclusion)
 * ts1 = {int; int} :> {int; int; int} = ts2
 * *)
Fixpoint ftyps_subset (ts1 ts2 : ftyps) :=
  match ts1, ts2 with
    | t1::ts1, t2::ts2 => if ftyp_eq_dec t1 t2 then ftyps_subset ts1 ts2 else false
    | nil, _ => true
    | _, _ => false
  end.

Lemma ftyps_subset_sigma : forall t' t rmap,
  ftyps_subset t' t = true ->
  ftyps_subset (sigma rmap t') (sigma rmap t) = true.
Proof.
  induction t'; destruct t; crush.
  destruct_c ftyp_eq_dec. destruct_c ftyp_eq_dec. eauto.
Qed.

Lemma ftyps_subset_ls_repeat : forall sz1 sz2 t,
  (sz2 <= sz1)%nat ->
  ftyps_subset (list_repeat sz2 t) (list_repeat sz1 t) = true.
Proof.
  induction sz1; simpl; intros.
  { assert (sz2 = 0%nat). omega. rewrite H0. simpl. auto. }
  { destruct sz2; simpl; auto. destruct_c ftyp_eq_dec. apply IHsz1. omega. }
Qed.

(* -------------------------------------------------------------------------- *)
(* Depth subtyping (arguments are in covariant order)
 * t1 <: t2
 * ptr(t, r) <: int
 * ptrU(sz, r) <: int
 * ptrU(sz1, r) <: ptrU(sz2, r) if sz1 >= sz2
 *) 
Definition ftyp_sub (t1 t2:ftyp) : bool :=
  match t1, t2 with
    | Ftyp_ptr t1 r1, Ftyp_int sz pf =>
      if eq_nat_dec sz WORDSIZE_BITS then true else false
    | Ftyp_ptrU _ _, Ftyp_int sz _ =>
      if eq_nat_dec sz WORDSIZE_BITS then true else false
    | Ftyp_ptrU sz1 r1, Ftyp_ptrU sz2 r2 =>
      if rgn_dec r1 r2 then
        if zle (Z.of_nat sz2) (Z.of_nat sz1) then
          true else false else false
    | Ftyp_double, Ftyp_int sz _ =>
      if eq_nat_dec sz 63 then true else false
    | Ftyp_int sz _, Ftyp_double =>
      if eq_nat_dec sz 63 then true else false
    | Ftyp_float, Ftyp_int sz _ =>
      if eq_nat_dec sz 31 then true else false
    | Ftyp_int sz _, Ftyp_float =>
      if eq_nat_dec sz 31 then true else false
    | _, _ => if ftyp_eq_dec t1 t2 then true else false
  end.

Lemma ftyp_sub_sigma : forall t' t rmap,
  ftyp_sub t' t = true ->
  ftyp_sub (sigma' rmap t') (sigma' rmap t) = true.
Proof.
  induction t'; simpl; unfold sigma'; intros; destruct_c ftyp_eq_dec; subst; 
    repeat match goal with
             | [ |- context [ ftyp_eq_dec ?a ?b ] ] => destruct_c (ftyp_eq_dec a b)
             | [ t: ftyp |- _ ] => destruct_c t
             | [ H: context [ rgn_dec ?a ?b ] |- _ ] => destruct_c (rgn_dec a b)
             | [ |- context [ rgn_dec ?a ?b ] ] => destruct_c (rgn_dec a b)
             | [ H: context [ zle ?a ?b ] |- _ ] => destruct_c (zle a b)
           end. 
Qed.

Lemma size_ftyp_sub_same : forall t1 t2 lo,
  ftyp_sub t1 t2 = true ->
  size_ftyp lo t1 = size_ftyp lo t2.
Proof.
  induction t1; destruct t2; unfold ftyp_sub; intros; simpl; try reflexivity;
    match goal with
      | [ H: context [ ftyp_eq_dec ?a ?b ] |- _ ] => destruct_c (ftyp_eq_dec a b)
      | [ H: context [ eq_nat_dec ?a ?b ] |- _ ] => destruct_c (eq_nat_dec a b)
      | _ => idtac
    end; subst; simpl; try reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Depth and width subtyping (arguments are in order of subset inclusion) 
 * {t_a; t_b} :> {t_c; t_d; t_e}
 * t_a <: t_c    t_b <: t_d
 *)
Fixpoint ftyps_subset2 (ts1 ts2 : ftyps) :=
  match ts1, ts2 with
    | t1::ts1, t2::ts2 => if ftyp_sub t1 t2 then ftyps_subset2 ts1 ts2 else false
    | nil, _ => true
    | _, _ => false
  end.

Lemma ftyps_subset2_sigma : forall t' t rmap,
  ftyps_subset2 t' t = true ->
  ftyps_subset2 (sigma rmap t') (sigma rmap t) = true.
Proof.
  induction t'; destruct t; simpl; intros; auto.
  consider (ftyp_sub a f); intros; try congruence.
  consider (ftyp_sub (sigma' rmap a) (sigma' rmap f)); intros; try congruence.
  eapply IHt'; eauto. eapply ftyp_sub_sigma in H; eauto. 
Qed.

(* -------------------------------------------------------------------------- *)
(* Depth and width subtyping (arguments are in order of subset inclusion) 
 * {t_a; t_b; t_c} <: {t_d; t_e}
 * t_a <: t_d    t_b <: t_e
 *)
Fixpoint ftyps_weaken (t ts : ftyps) :=
  match t, ts with
    | t1::t', t2::ts' => if ftyp_sub t1 t2 then ftyps_weaken t' ts' else false
    | _, nil => true
    | _, _ => false
  end. 

Lemma ftyps_weaken_sigma : forall t' t rmap,
  ftyps_weaken t' t = true ->
  ftyps_weaken (sigma rmap t') (sigma rmap t) = true.
Proof.
  induction t'; destruct t; simpl; intros; auto.
  consider (ftyp_sub a f); intros; try congruence.
  consider (ftyp_sub (sigma' rmap a) (sigma' rmap f)); intros; try congruence.
  eapply IHt'; eauto. eapply ftyp_sub_sigma in H; eauto. 
Qed.

(* -------------------------------------------------------------------------- *)

(* Calculate the nth offset in typ t *)
Fixpoint walk_offset (lo:layout) (n:nat) (t:ftyps) : Z :=
  match n, t with
    | O, _ => 0
    | S n', t'::ts => walk_offset lo n' ts + size_ftyp lo t'
    | _, _ => 0
  end.

(* Calculate the additional offsets as a result of padding *)
Fixpoint walk_offset2 (lo:layout) (ts:ftyps) : nat :=
  match ts with
    | nil => 0
    | t::ts => let n := (nat_of_Z (align_Z (size_ftyp lo t) (align_ftyp lo t))) in
      n - (size_ftyp_nat lo t) + walk_offset2 lo ts
  end%nat.

(* Calculate the actual offset, accounting for padding, in a flattend typ *) 
Definition walk_offset3 (lo:layout) (tenv:tenv_t) (n:nat) (t:typ) : nat :=
  match t with
    | Typ_name x lr1 => match Nenv.find x tenv with
                          | Some (t', lr2, _) => (n + walk_offset2 lo t')%nat
                          | None => O
                        end
    | _ => n
  end.

Lemma walk_offset_sigma_inv : forall n ft lo lr ls rmap,
  walk_offset lo n (sigma (inst_prgn lr ls) ft) =
  walk_offset lo n (sigma rmap (sigma (inst_prgn lr ls) ft)).
Proof.
  induction n; destruct ft; crush. f_equal. eapply IHn; eauto. destruct f; crush.
Qed.

Lemma walk_offset_nonneg : forall n t lo,
  walk_offset lo n t >= 0.
Proof.
  induction n; destruct t; crush. size_ftyp_prop. specialize (IHn t lo). omega.
Qed.

Fixpoint array_offset (lo:layout) (ts:ftyps) (n:nat) : Z :=
  match n with
    | O => 0
    | S n' => size_ftyps lo ts + array_offset lo ts n'
  end.

Lemma array_offset_nonneg : forall lo t n,
  array_offset lo t n >= 0.
Proof.
  induction n; simpl; intros. omega.
  assert (size_ftyps lo t >= 0). apply size_ftyps_nonneg. omega.
Qed.

Lemma array_offset_less : forall n sz lo tenv t,
  (n < sz)%nat ->
  array_offset lo (flatten_typ lo tenv t) n <= size_ftyps lo (flatten_typ lo tenv (Typ_array t sz)).
Proof.
  induction n; simpl; intros.
  assert (((fix go (sz0 : nat) : list ftyp :=
         match sz0 with
         | 0%nat => nil
         | S sz1 => flatten_typ lo tenv t ++ go sz1
         end) sz) = flatten_typ lo tenv (Typ_array t sz)). simpl. auto.
  rewrite H0. 
  specialize (size_ftyps_nonneg lo (flatten_typ lo tenv (Typ_array t sz))); intros. omega.
  destruct sz. omegaContradiction.
  assert (n < sz)%nat. omega. apply IHn with (lo := lo) (tenv := tenv) (t := t) in H0.
  assert (((fix go (sz0 : nat) : list ftyp :=
         match sz0 with
         | 0%nat => nil
         | S sz1 => flatten_typ lo tenv t ++ go sz1
         end) sz) = flatten_typ lo tenv (Typ_array t sz)). simpl. auto.
  rewrite H1. rewrite size_ftyps_linear. omega.
Qed.
