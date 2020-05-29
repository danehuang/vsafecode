(* Standard library imports *)
Require Import FMaps.
Require Import FSets.FMapAVL.
Require Import OrderedTypeEx.

(* Other library imports *)
Add LoadPath "../libs".
Add LoadPath "../libs/CompCert-Toolkit".
Require Import Tactics.
Require Import Consider.

Require Import Bits.
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
Require Import TypeSystem.


Definition ftyps_eq_dec := list_eq_dec ftyp_eq_dec.

(* ---------------------------------------------------------------------- *)
Fixpoint TSb (tenv:tenv_t) (t:typ) : bool :=
  match t with
    | Typ_name x lr1 =>
      match Nenv.find x tenv with
        | Some (_, lr2, _) => if eq_nat_dec (length lr1) (length lr2) then true else false
        | None => false
      end
    | Typ_array t sz => TSb tenv t
    | Typ_ptr t _ => TSb tenv t
    | _ => true
  end.

Lemma TSb_correct : forall tenv t,
  TSb tenv t = true ->
  TS tenv t.
Proof.
  induction t; simpl; intros; auto.
  destruct_c (Nenv.find x tenv). destruct p. destruct p. destruct_c eq_nat_dec.
Qed.

(* ---------------------------------------------------------------------- *)
Fixpoint tc_tenv_typ (D:list rgn) (t:typ) : bool :=
  match t with
    | Typ_float => true
    | Typ_double => true
    | Typ_int _ _ => true
    | Typ_ptr t r => if in_dec rgn_dec r D then tc_tenv_typ D t else false
    | Typ_name x lr => fold_left (fun a b => if in_dec rgn_dec b D then a else false) lr true
    | Typ_fun prgn sig ret => 
      match ret with
        | None => fold_left (fun a b => if tc_tenv_typ prgn b then a else false) sig true
        | Some t => 
          if tc_tenv_typ prgn t
            then (fold_left (fun a b => if tc_tenv_typ prgn b then a else false) sig true)
            else false
      end
    | Typ_array t sz => tc_tenv_typ D t
    | Typ_ptrU sz r => if in_dec rgn_dec r D then true else false
  end.

Lemma tc_tenv_typ_correct_ls : forall D lr b,
  fold_left (fun a b => if in_dec rgn_dec b D then a else false) lr b = true ->
  b = true.
Proof.
  induction lr; intros; auto. simpl in H. destruct in_dec; crush.
Qed.

Lemma tc_tenv_typ_correct_ls2 : forall D lr b,
  fold_left (fun a b => if tc_tenv_typ D b then a else false) lr b = true ->
  b = true.
Proof.
  induction lr; intros; auto. simpl in H. destruct tc_tenv_typ; crush.
Qed.

Lemma tc_tenv_typ_correct : forall t D,
  tc_tenv_typ D t = true ->
  wf_tenv_typ D t.
Proof.
  induction t; simpl; intros; auto.
  { destruct in_dec; crush. }
  { induction lr; crush. repeat constructor. t_dup H. apply tc_tenv_typ_correct_ls in H.
    destruct in_dec; crush. t_dup H. apply tc_tenv_typ_correct_ls in H.
    destruct in_dec; crush. inv H0. assumption. }
  { destruct t; crush. 
    remember (tc_tenv_typ lr t) as Hd. destruct Hd; crush.
    symmetry in HeqHd. eapply X0 in HeqHd. constructor; auto.
    induction ls; crush.
    t_dup H. apply tc_tenv_typ_correct_ls2 in H.
    constructor; auto. inv X. 
    remember (tc_tenv_typ lr a) as Hd. destruct Hd; crush.
    inv X. eapply IHls; eauto. rewrite H in H'. auto.
    constructor.
    induction ls; crush.
    t_dup H. apply tc_tenv_typ_correct_ls2 in H.
    constructor; auto. inv X.
    remember (tc_tenv_typ lr a) as Hd. destruct Hd; crush.
    inv X. eapply IHls; eauto. rewrite H in H'. auto. }
  { destruct in_dec; crush. }
Qed.

Lemma tc_tenv_typ_fun : forall ls lr b,
  fold_left (fun a b => if tc_tenv_typ lr b then a else false) ls b = true ->
  Forall (fun t : typ => wf_tenv_typ lr t) ls.
Proof.
  induction ls; crush. constructor; auto.
  { apply tc_tenv_typ_correct_ls2 in H. 
    consider (tc_tenv_typ lr a); intros; subst; try congruence.
    apply tc_tenv_typ_correct; auto. } 
  { t_dup H. apply tc_tenv_typ_correct_ls2 in H. rewrite H in H'. eauto. }
Qed.

(* ---------------------------------------------------------------------- *)
Definition tc_tenv_ftyp (D:list rgn) (t:ftyp) : bool :=
  match t with
    | Ftyp_float => true
    | Ftyp_double => true
    | Ftyp_int _ _ => true
    | Ftyp_ptr t r => if in_dec rgn_dec r D then tc_tenv_typ D t else false
    | Ftyp_fun prgn sig ret =>
      match ret with
        | None => fold_left (fun a b => if tc_tenv_typ prgn b then a else false) sig true
        | Some t => 
          if tc_tenv_typ prgn t
            then (fold_left (fun a b => if tc_tenv_typ prgn b then a else false) sig true)
            else false
      end
    | Ftyp_ptrU sz r => if in_dec rgn_dec r D then true else false
  end.

Lemma tc_tenv_ftyp_correct : forall D t,
  tc_tenv_ftyp D t = true ->
  wf_tenv_ftyp D t.
Proof.
  destruct t; simpl; intros; auto.
  { destruct in_dec; crush. econstructor; eauto. eapply tc_tenv_typ_correct; eauto. }
  { destruct_c o. consider (tc_tenv_typ l t); intros; try congruence.
    apply tc_tenv_typ_correct in H. constructor; auto. eapply tc_tenv_typ_fun; eauto. 
    constructor; auto. eapply tc_tenv_typ_fun; eauto. }
  { destruct in_dec; crush. }
Qed.

Fixpoint tc_tenv_ftyps (D:list rgn) (t:ftyps) : bool :=
  match t with
    | nil => true
    | t::ts => andb (tc_tenv_ftyp D t) (tc_tenv_ftyps D ts)
  end.

Lemma tc_tenv_ftyps_correct : forall D t,
  tc_tenv_ftyps D t = true ->
  wf_tenv_ftyps D t.
Proof.
  induction t; simpl; intros; econstructor; eauto.
  { rewrite andb_true_iff in H. destruct H. eapply tc_tenv_ftyp_correct; eauto. }
  { rewrite andb_true_iff in H. crush. }
Qed.

(* ---------------------------------------------------------------------- *)
Fixpoint tc_typ (tenv:tenv_t) (D:Delta) (t:typ) : bool :=
  TSb tenv t &&
  match t with
    | Typ_float => true
    | Typ_double => true
    | Typ_int _ _ => true
    | Typ_ptr t r => 
      match Nenv.find r D with
        | Some t' => tc_typ tenv D t 
        | None => false
      end 
    | Typ_name x lr1 =>
      match Nenv.find x tenv with
        | Some (t, lr2) =>
          fold_left (fun a b => andb a (match Nenv.find b D with
                                          | Some t => true
                                          | None => false
                                        end)) lr1 true
        | None => false
      end
    | Typ_fun prgn sig r => 
      match r with
        | None => fold_left (fun a b => if tc_tenv_typ prgn b then a else false) sig true
        | Some t => 
          if tc_tenv_typ prgn t
            then (fold_left (fun a b => if tc_tenv_typ prgn b then a else false) sig true)
            else false
      end
    | Typ_array t sz => 
      if eq_nat_dec sz O then false else tc_typ tenv D t
    | Typ_ptrU sz r =>
      match Nenv.find r D with
        | Some t' => true
        | None => false
      end
  end.

Lemma tc_typ_correct_ls2 : forall lr b (D:Nenv.t typ),
  fold_left (fun a b => a && match Nenv.find b D with
                               | Some _ => true
                               | None => false
                             end) lr b = true ->
  b = true.
Proof.
  induction lr; crush. eapply IHlr in H. rewrite andb_true_iff in H. destruct H. auto.
Qed.

Lemma tc_typ_correct_ls : forall (D:Nenv.t typ) lr,
  fold_left (fun a b => a && match Nenv.find b D with
                               | Some _ => true
                               | None => false
                             end) lr true = true ->
  Forall (fun r => exists t, Nenv.find r D = Some t) lr.
Proof.
  induction lr; crush. inv H. econstructor; eauto.
  destruct (Nenv.find a D); crush; eauto.
  clear -H1. induction lr; crush.
  eapply IHlr; eauto. t_dup H1.
  eapply tc_typ_correct_ls2 in H1; auto. rewrite H1 in H'. auto.
Qed.

Lemma tc_typ_correct : forall t D tenv,
  tc_typ tenv D t = true ->
  wf_typ tenv D t.
Proof.
  induction t; simpl; intros; auto.
  { econstructor; eauto. eapply TSb_correct; eauto. }
  { econstructor; eauto. eapply TSb_correct; eauto. }
  { econstructor; eauto. eapply TSb_correct; eauto. }
  { rewrite andb_true_iff in H. destruct H.
    remember (Nenv.find r D) as Hd. destruct_c Hd. econstructor; eauto. 
    eapply TSb_correct; eauto. }
  { rewrite andb_true_iff in H. destruct H. 
    remember (Nenv.find x tenv) as Hd. destruct_c Hd. destruct p. destruct p.
    eapply tc_typ_correct_ls in H0. econstructor; eauto. simpl. 
    rewrite <- HeqHd. destruct_c eq_nat_dec. }
  { destruct t; crush.
    remember (tc_tenv_typ lr t) as Hd. destruct Hd; crush.
    symmetry in HeqHd. apply tc_tenv_typ_correct in HeqHd.
    constructor; auto. eapply tc_tenv_typ_fun; eauto. eapply TSb_correct; eauto.
    constructor; auto. eapply tc_tenv_typ_fun; eauto. }
  { rewrite andb_true_iff in H. destruct H. destruct_c eq_nat_dec. econstructor; eauto.
    eapply TSb_correct; eauto. }
  { remember (Nenv.find r D) as Hd. destruct_c Hd. econstructor; eauto. 
    eapply TSb_correct; eauto. }
Qed.  

(* ---------------------------------------------------------------------- *)
Definition tc_ftyp (tenv:tenv_t) (D:Delta) (t:ftyp) : bool :=
  match t with
    | Ftyp_float => true
    | Ftyp_double => true
    | Ftyp_int _ _ => true
    | Ftyp_fun lr ls t => 
      match t with
        | None => fold_left (fun a b => if tc_tenv_typ lr b then a else false) ls true
        | Some t => 
          if tc_tenv_typ lr t
            then (fold_left (fun a b => if tc_tenv_typ lr b then a else false) ls true)
            else false
      end
    | Ftyp_ptr t r => 
      match Nenv.find r D with
        | Some t' => tc_typ tenv D t 
        | None => false
      end
    | Ftyp_ptrU sz r =>
      match Nenv.find r D with
        | Some t' => true
        | None => false
      end
  end.

Lemma tc_ftyp_correct : forall tenv D t,
  tc_ftyp tenv D t = true ->
  wf_ftyp tenv D t.
Proof.
  induction t; simpl; intros; auto.
  { remember (Nenv.find r D) as Hd. destruct_c Hd. econstructor; eauto. 
    eapply tc_typ_correct; eauto. }
  { destruct o; crush.
    remember (tc_tenv_typ l t) as Hd. destruct Hd; crush. symmetry in HeqHd.
    apply tc_tenv_typ_correct in HeqHd. 
    constructor; auto. eapply tc_tenv_typ_fun; eauto.
    constructor; auto. eapply tc_tenv_typ_fun; eauto. }
  { remember (Nenv.find r D) as Hd. destruct_c Hd. econstructor; eauto. }
Qed.

(* ---------------------------------------------------------------------- *)
Fixpoint tc_ftyps (tenv:tenv_t) (D:Delta) (t:ftyps) : bool :=
  match t with
    | nil => true
    | t::ts => andb (tc_ftyp tenv D t) (tc_ftyps tenv D ts)
  end.

Lemma tc_ftyps_correct : forall tenv D t,
  tc_ftyps tenv D t = true ->
  wf_ftyps tenv D t.
Proof.
  induction t; crush. rewrite andb_true_iff in H. destruct H. 
  econstructor; eauto. eapply tc_ftyp_correct; eauto.
Qed.

(* ---------------------------------------------------------------------- *)
Definition tc_undef_ftyp (t:ftyp) : bool :=
  match t with
    | Ftyp_float => true
    | Ftyp_double => true
    | Ftyp_int _ _ => true
    | _ => false
  end.

Fixpoint tc_undef_ftyps (ts:ftyps) : bool :=
  match ts with
    | nil => true
    | t::ts => tc_undef_ftyp t && tc_undef_ftyps ts
  end.

Lemma tc_undef_ftyp_correct : forall t,
  tc_undef_ftyp t = true ->
  wf_undef_ftyp t.
Proof.
  induction t; simpl; intros; try congruence; try constructor; auto.
Qed.

Lemma tc_undef_ftyps_correct : forall t,
  tc_undef_ftyps t = true ->
  wf_undef_ftyps t.
Proof.
  induction t; simpl; intros.
  { constructor. }
  { rewrite andb_true_iff in H. destruct H. constructor; auto.
    apply tc_undef_ftyp_correct; auto. }
Qed.

(* ---------------------------------------------------------------------- *)
Definition tc_const (C:config) (D:Delta) (P:Psi) (c:IllvmAST.const) : option ftyps :=
  match c with
    | Const_null => Some (Ftyp_int64 :: nil) (* Some (Ftyp_ptr Typ_int32 O :: nil) *)
    | Const_nullU => Some (Ftyp_int64 :: nil) (* Some (Ftyp_ptrU O O :: nil) *)
    | Const_float f => Some (Ftyp_float :: nil)
    | Const_double d => Some (Ftyp_double :: nil)
    | Const_int sz pf i => Some (Ftyp_int sz pf :: nil)
    | Const_fun fid =>
      match lookup_fun fid (c_fs C) with
        | Some f => 
          Some (Ftyp_fun (domain (f_prgn f)) (f_sig f) (f_ret f) :: nil)
        | _ => None
      end
    | Const_undef t => if tc_undef_ftyps t then Some t else None
    | Const_baddr _ _ => None
  end.

Lemma tc_const_correct : forall C D P c t,
  tc_const C D P c = Some t ->
  wf_const C D P c t.
Proof.
  destruct c; simpl; intros. 
  { inv H. econstructor; eauto. }
  { inv H. econstructor; eauto. }
  { inv H. econstructor; eauto. }
  { inv H. econstructor; eauto. }
  { inv H. econstructor; eauto. }
  { remember (lookup_fun l (c_fs C)) as Hd. destruct_c Hd.
    assert (l = f_lab f). symmetry in HeqHd. eapply lookup_fun_spec in HeqHd; eauto.
    symmetry in HeqHd. eapply lookup_fun_spec2 in HeqHd; eauto. subst.
    inv H. econstructor; eauto. }
  { consider (tc_undef_ftyps f); intros; try congruence. inv H0.
    econstructor; eauto. apply tc_undef_ftyps_correct; auto. }
  { inv H. }
Qed.

(* ---------------------------------------------------------------------- *)
Definition tc_op (C:config) (D:Delta) (P:Psi) (G:Gamma) (o:operand) : option ftyps :=
  match o with
    | Op_reg x => Nenv.find x G
    | Op_const c => tc_const C D P c
  end.

Lemma tc_op_correct : forall C D P G o t,
  tc_op C D P G o = Some t ->
  wf_operand C D P G o t.
Proof.
  destruct o; crush. econstructor; eauto. eapply tc_const_correct; eauto.
Qed.

(* ---------------------------------------------------------------------- *)
Definition i2n {sz:nat} (i:Word.int sz) := nat_of_Z (Word.unsigned i).
Definition Const0 := 0%nat.
Definition Const4 := 4%nat.
Definition Const8 := 8%nat.
Definition Const31 := 31%nat.
Definition Const63 := 63%nat.

Definition tc_insn (C:config) (D:Delta) (P:Psi) (i:insn) (G:Gamma) : option Gamma :=
  match i with
    | Insn_binop x bop o1 o2 =>
      match tc_op C D P G o1, tc_op C D P G o2 with
        | Some (Ftyp_int sz1 pf1 :: nil), Some (Ftyp_int sz2 pf2 :: nil) => 
          if eq_nat_dec sz1 sz2 then
            Some (Nenv.add x (Ftyp_int sz1 pf1 :: nil) G)
            else None
        | _, _ => None
      end

    | Insn_fbinop x c o1 o2 =>
      match tc_op C D P G o1, tc_op C D P G o2 with
        | Some (Ftyp_float :: nil), Some (Ftyp_float :: nil) =>
          Some (Nenv.add x (Ftyp_float :: nil) G)
        | Some (Ftyp_int sz _ :: nil), Some (Ftyp_float :: nil) =>
          if eq_nat_dec sz Const31 then
            Some (Nenv.add x (Ftyp_float :: nil) G) else None
        | Some (Ftyp_float :: nil), Some (Ftyp_int sz _ :: nil) =>
          if eq_nat_dec sz Const31 then
            Some (Nenv.add x (Ftyp_float :: nil) G) else None
        | Some (Ftyp_double :: nil), Some (Ftyp_double :: nil) =>
          Some (Nenv.add x (Ftyp_double :: nil) G)
        | Some (Ftyp_int sz _ :: nil), Some (Ftyp_double :: nil) =>
          if eq_nat_dec sz Const63 then
            Some (Nenv.add x (Ftyp_double :: nil) G) else None
        | Some (Ftyp_double :: nil), Some (Ftyp_int sz _ :: nil) =>
          if eq_nat_dec sz Const63 then
            Some (Nenv.add x (Ftyp_double :: nil) G) else None
        | Some (Ftyp_int sz1 _ :: nil), Some (Ftyp_int sz2 _ :: nil) =>
          if eq_nat_dec sz1 sz2 then
            ( if eq_nat_dec sz1 Const31 then
                Some (Nenv.add x (Ftyp_float :: nil) G)
              else if eq_nat_dec sz1 Const63 then
                Some (Nenv.add x (Ftyp_double :: nil) G)
              else
                None
            )
          else 
            None
            
        | _, _ => None
      end
    | Insn_icmp x c o1 o2 =>
      match tc_op C D P G o1, tc_op C D P G o2 with
        | Some (Ftyp_int sz1 pf1 :: nil), Some (Ftyp_int sz2 pf2 :: nil) => 
          if eq_nat_dec sz1 sz2 then
            Some (Nenv.add x (Ftyp_int1 :: nil) G)
            else None
        | Some (Ftyp_int sz _ :: nil), Some (Ftyp_ptr _ _ :: nil) =>
          if eq_nat_dec sz WORDSIZE_BITS then
            Some (Nenv.add x (Ftyp_int1 :: nil) G)
            else None
        | Some (Ftyp_int sz _ :: nil), Some (Ftyp_ptrU _ _ :: nil) =>
          if eq_nat_dec sz WORDSIZE_BITS then
            Some (Nenv.add x (Ftyp_int1 :: nil) G)
            else None
        | Some (Ftyp_ptr _ _ :: nil), Some (Ftyp_int sz _ :: nil) =>
          if eq_nat_dec sz WORDSIZE_BITS then
            Some (Nenv.add x (Ftyp_int1 :: nil) G)
            else None
        | Some (Ftyp_ptrU _ _ :: nil), Some (Ftyp_int sz _ :: nil) =>
          if eq_nat_dec sz WORDSIZE_BITS then
            Some (Nenv.add x (Ftyp_int1 :: nil) G)
            else None
        | Some (Ftyp_ptr _ _ :: nil), Some (Ftyp_ptr _ _ :: nil) => 
          Some (Nenv.add x (Ftyp_int1 :: nil) G)
        | Some (Ftyp_ptr _ _ :: nil), Some (Ftyp_ptrU _ _ :: nil) =>
          Some (Nenv.add x (Ftyp_int1 :: nil) G)
        | Some (Ftyp_ptrU _ _ :: nil), Some (Ftyp_ptr _ _ :: nil) =>
          Some (Nenv.add x (Ftyp_int1 :: nil) G)
        | Some (Ftyp_ptrU _ _ :: nil), Some (Ftyp_ptrU _ _ :: nil) =>
          Some (Nenv.add x (Ftyp_int1 :: nil) G)
        | _, _ => None
      end
    | Insn_fcmp x c o1 o2 =>
      match tc_op C D P G o1, tc_op C D P G o2 with
        | Some (Ftyp_float :: nil), Some (Ftyp_float :: nil) => 
          Some (Nenv.add x (Ftyp_int1 :: nil) G)
        | Some (Ftyp_float :: nil), Some (Ftyp_int sz _ :: nil) => 
          if eq_nat_dec sz Const31 then
            Some (Nenv.add x (Ftyp_int1 :: nil) G)
            else None
        | Some (Ftyp_int sz _ :: nil), Some (Ftyp_float :: nil) => 
          if eq_nat_dec sz Const31 then
            Some (Nenv.add x (Ftyp_int1 :: nil) G)
            else None
        | Some (Ftyp_double :: nil), Some (Ftyp_double :: nil) => 
          Some (Nenv.add x (Ftyp_int1 :: nil) G)
        | Some (Ftyp_double :: nil), Some (Ftyp_int sz _ :: nil) => 
          if eq_nat_dec sz Const63 then
            Some (Nenv.add x (Ftyp_int1 :: nil) G)
            else None
        | Some (Ftyp_int sz _ :: nil), Some (Ftyp_double :: nil) => 
          if eq_nat_dec sz Const63 then
            Some (Nenv.add x (Ftyp_int1 :: nil) G)
            else None
        | Some (Ftyp_int sz1 _ :: nil), Some (Ftyp_int sz2 _ :: nil) => 
          if eq_nat_dec sz1 sz2 then
            Some (Nenv.add x (Ftyp_int1 :: nil) G)
            else None
        | _, _ => None
      end
    | Insn_load x (Typ_ptr t r) o => 
      let ft := flatten_typ (c_lo C) (c_tenv C) t in
      match tc_op C D P G o with
        | Some (Ftyp_ptr t' r' :: nil) =>
          if rgn_dec r r' then
            if tc_typ (c_tenv C) D (Typ_ptr t r) then
              if TSb (c_tenv C) t' then
                if ftyps_subset (flatten_typ (c_lo C) (c_tenv C) t) (flatten_typ (c_lo C) (c_tenv C) t') then
                  Some (Nenv.add x ft G)
                  else None else None else None else None
        | _ => None
      end
    | Insn_load x (Typ_ptrU sz r) o =>
      match tc_op C D P G o with
        | Some (Ftyp_ptrU sz' r' :: nil) =>
          if rgn_dec r r' then
            if ge_dec sz' sz then
              match sz with
                | 1%nat => Some (Nenv.add x (Ftyp_int8 :: nil) G)
                | 2%nat => Some (Nenv.add x (Ftyp_int16 :: nil) G)
                | 4%nat => Some (Nenv.add x (Ftyp_int32 :: nil) G)
                | 8%nat => Some (Nenv.add x (Ftyp_int64 :: nil) G)
                | _ => None
              end
              else None else None
        | _ => None
      end
    | Insn_store t1 o1 (Typ_ptr t2 r) o2 =>
      let ft := flatten_typ (c_lo C) (c_tenv C) t1 in
        match tc_op C D P G o1, tc_op C D P G o2 with
          | Some ft', Some (Ftyp_ptr t2' r' :: nil) =>
            if typ_eq_dec t2 t2' then
              if ftyps_eq_dec ft ft' then
                if ftyps_subset2 ft (flatten_typ (c_lo C) (c_tenv C) t2') then 
                  if rgn_dec r r' then
                    if tc_typ (c_tenv C) D (Typ_ptr t2 r) then
                      if TSb (c_tenv C) t2' then
                        if TSb (c_tenv C) t1 then
                          if tc_typ (c_tenv C) D t1 then Some G else None
                          (*
                          match o1 with
                            | Op_const Const_null => Some G
                            | Op_const Const_nullU => Some G
                            | _ => if tc_typ (c_tenv C) D t1 then Some G else None
                          end
                          *)
                          else None else None else None else None else None else None else None
          | _, _ => None
        end
    | Insn_store t o1 (Typ_ptrU sz r) o2 =>
      match tc_op C D P G o1, tc_op C D P G o2 with
        | Some ft', Some (Ftyp_ptrU sz' r' :: nil) =>
          if rgn_dec r r' then
            if zle (Z.of_nat sz) (Z.of_nat sz') then
              if zle (size_ftyps (c_lo C) ft') (Z.of_nat sz) then
                Some G else None else None else None
        | _, _ => None
      end
    | Insn_poolcheck x2 r t (Op_reg x) =>
      match tc_op C D P G (Op_reg x) with
        | Some (Ftyp_ptr t' r' :: nil) =>
          if tc_typ (c_tenv C) D (Typ_ptr t r) then
              if rgn_dec r r' then
                Some (Nenv.add x2 (Ftyp_ptr t r :: nil) G) else None else None 
        | Some (Ftyp_int sz pf :: nil) =>
          if tc_typ (c_tenv C) D (Typ_ptr t r) then
            if le_dec sz WORDSIZE_BITS then
              Some (Nenv.add x2 (Ftyp_ptr t r :: nil) G) else None else None
        | _ => None
      end
    | Insn_poolcheckU x2 r sz (Op_reg x) =>
      match tc_op C D P G (Op_reg x) with
        | Some (Ftyp_ptrU sz' r' :: nil) =>
          if tc_typ (c_tenv C) D (Typ_ptrU sz r) then
            if rgn_dec r r' then
              Some (Nenv.add x2 (Ftyp_ptrU sz r :: nil) G) else None else None
        | Some (Ftyp_int sz' pf' :: nil) =>
          if tc_typ (c_tenv C) D (Typ_ptrU sz r) then
            if le_dec sz' WORDSIZE_BITS then
              Some (Nenv.add x2 (Ftyp_ptrU sz r :: nil) G) else None else None
        | _ => None
      end
    | Insn_free (Typ_ptr t r) o => 
      match tc_op C D P G o with
        | Some (Ftyp_ptr t' r' :: nil) =>
            if rgn_dec r r' then
              if tc_typ (c_tenv C) D (Typ_ptr t r) then
                Some G else None else None
        | Some (Ftyp_int _ _ :: nil) =>
          if tc_typ (c_tenv C) D (Typ_ptr t r) then
            Some G else None
        | _ => None
      end
    | Insn_free (Typ_ptrU sz r) o =>
      match tc_op C D P G o with
        | Some (Ftyp_ptrU sz' r' :: nil) =>
          if rgn_dec r r' then
            if tc_typ (c_tenv C) D (Typ_ptrU sz r) then
              Some G else None else None
        | Some (Ftyp_int _ _ :: nil) =>
          if tc_typ (c_tenv C) D (Typ_ptrU sz r) then
            Some G else None
        | _ => None
      end
    | Insn_bitcast x (Typ_ptr t1 r1) o (Typ_ptr t2 r2) =>
      match tc_op C D P G o with
        | Some (Ftyp_ptr t1' r1' :: nil) =>
          if typ_eq_dec t1 t1' then
            if rgn_dec r1 r1' then
              if rgn_dec r1 r2 then
                if ftyps_subset (flatten_typ (c_lo C) (c_tenv C) t2) (flatten_typ (c_lo C) (c_tenv C) t1) then
                  if tc_typ (c_tenv C) D (Typ_ptr t1 r1) then
                    if tc_typ (c_tenv C) D (Typ_ptr t2 r2) then
                      Some (Nenv.add x (Ftyp_ptr t2 r2 :: nil) G)
                      else None else None else None else None else None else None
        | _ => None
      end  
    | Insn_bitcast x (Typ_ptrU sz1 r1) o (Typ_ptrU sz2 r2) =>
      match tc_op C D P G o with
        | Some (Ftyp_ptrU sz3 r3 :: nil) =>
          if eq_nat_dec sz1 sz3 then
              if rgn_dec r1 r2 then
                if rgn_dec r2 r3 then
                  if tc_typ (c_tenv C) D (Typ_ptrU sz1 r1) then
                    if tc_typ (c_tenv C) D (Typ_ptrU sz2 r2) then
                      if zle (Z.of_nat sz2) (Z.of_nat sz1) then
                        Some (Nenv.add x (Ftyp_ptrU sz2 r2 :: nil) G)
                        else None else None else None else None else None else None
        | _ => None
      end
    | Insn_ptrtoint x (Typ_ptr t r) o (Typ_int sz _) =>
      match tc_op C D P G o with
        | Some (Ftyp_ptr t' r' :: nil) =>
          if eq_nat_dec sz WORDSIZE_BITS then
            if typ_eq_dec t t' then
              if rgn_dec r r' then
                if tc_typ (c_tenv C) D (Typ_ptr t r) then
                  Some (Nenv.add x (Ftyp_int64 :: nil) G)
                  else None else None else None else None
        | _ => None
      end
    | Insn_ptrtoint x (Typ_ptrU sz1 r) o (Typ_int sz2 _) =>
      match tc_op C D P G o with
        | Some (Ftyp_ptrU sz1' r' :: nil) =>
          if eq_nat_dec sz2 WORDSIZE_BITS then
            if rgn_dec r r' then
              if tc_typ (c_tenv C) D (Typ_ptrU sz1' r') then
                if eq_nat_dec sz1 sz1' then
                  Some (Nenv.add x (Ftyp_int64 :: nil) G) else None else None else None else None
        | _ => None
      end   
    | Insn_inttoptr x (Typ_int sz1 _) o (Typ_ptr t r) =>
      match tc_op C D P G o with
        | Some (Ftyp_int sz2 _ :: nil) =>
          if eq_nat_dec sz1 sz2 then
          if eq_nat_dec sz2 WORDSIZE_BITS then
            if tc_typ (c_tenv C) D (Typ_ptr t r) then
                Some (Nenv.add x (Ftyp_ptr t r :: nil) G)
                else None else None else None
        | _ => None
      end
    | Insn_inttoptr x (Typ_int sz1 _) o (Typ_ptrU sz r) =>
      match tc_op C D P G o with
        | Some (Ftyp_int sz2 _ :: nil) =>
          if eq_nat_dec sz1 sz2 then
            if eq_nat_dec sz2 WORDSIZE_BITS then
              if tc_typ (c_tenv C) D (Typ_ptrU sz r) then
                Some (Nenv.add x (Ftyp_ptrU sz r :: nil) G)
                else None else None else None 
        | _ => None
      end
    | Insn_gep x2 (Typ_ptr (Typ_name x ls) r) o t (Op_const (Const_int sz pf i)) =>
      let t' := flatten_typ (c_lo C) (c_tenv C) (Typ_name x ls) in
      let t'' := flatten_typ (c_lo C) (c_tenv C) t in
      let n := walk_offset3 (c_lo C) (c_tenv C) (i2n i) (Typ_name x ls) in
      match Nenv.find x (c_tenv C) with
        | Some (ft, lr) =>
          if ftyps_eq_dec t'' nil then None else
            if lt_dec n (length t') then
              if ftyps_subset t'' (skipn n t') then
                match tc_op C D P G o, tc_const C D P (Const_int sz pf i) with
                  | Some (Ftyp_ptr (Typ_name x3 ls3) r' :: nil), Some (Ftyp_int sz' _ :: nil) =>
                    if eq_nat_dec sz sz' then
                    if typ_eq_dec (Typ_name x ls) (Typ_name x3 ls3) then
                      if rgn_dec r r' then
                        if tc_typ (c_tenv C) D t then
                          if tc_typ (c_tenv C) D (Typ_ptr (Typ_name x ls) r) then
                            Some (Nenv.add x2 (Ftyp_ptr t r :: nil) G)
                            else None else None else None else None else None
                  | _, _ => None
                    end
                else None else None
        | None => None
      end
    | Insn_gep x2 (Typ_ptr (Typ_name x ls) r) o t (Op_reg x3) =>
      let t' := flatten_typ (c_lo C) (c_tenv C) (Typ_name x ls) in
      let t'' := flatten_typ (c_lo C) (c_tenv C) t in
      match Nenv.find x (c_tenv C) with
        | Some (ft, lr) =>
          if ftyps_eq_dec t'' nil then None else
            match tc_op C D P G o, tc_op C D P G (Op_reg x3) with
              | Some (Ftyp_ptr (Typ_name x3 ls3) r' :: nil), Some (Ftyp_int sz _ :: nil) =>
                if typ_eq_dec (Typ_name x ls) (Typ_name x3 ls3) then
                  if rgn_dec r r' then
                    if tc_typ (c_tenv C) D t then
                      if tc_typ (c_tenv C) D (Typ_name x ls) then
                        Some (Nenv.add x2 (Ftyp_ptr t r :: nil) G)
                        else None else None else None else None
              | _, _ => None
            end
        | None => None
      end
    | Insn_gep x (Typ_ptr (Typ_array t1 sz1) r) o t2 (Op_const (Const_int sz' pf' i)) =>
      match tc_op C D P G o, tc_const C D P (Const_int sz' pf' i) with
        | Some (Ftyp_ptr (Typ_array t1' sz1') r' :: nil), Some (Ftyp_int sz'' pf'' :: nil) =>
          if rgn_dec r r' then
            if typ_eq_dec t1 t1' then
              if typ_eq_dec t1 t2 then
                if eq_nat_dec sz1 sz1' then
                  if eq_nat_dec sz' sz'' then
                    if tc_typ (c_tenv C) D (Typ_ptr (Typ_array t1 sz1) r) then
                      if lt_dec (i2n i) sz1 then
                        if zlt (Z.of_nat sz1) (Word.modulus WORDSIZE_BITS) then
                          if le_dec sz' WORDSIZE_BITS then
                            Some (Nenv.add x (Ftyp_ptr t1 r :: nil) G)
                            else None else None else None else None else None else None else None else None else None
        | _, _ => None
      end
    | Insn_gep x (Typ_ptr (Typ_array t1 sz1) r) o t2 (Op_reg x2) =>
      match tc_op C D P G o, tc_op C D P G (Op_reg x2) with
        | Some (Ftyp_ptr (Typ_array t1' sz1') r' :: nil), Some (Ftyp_int sz'' pf'' :: nil) =>
          if rgn_dec r r' then
            if typ_eq_dec t1 t1' then
              if typ_eq_dec t1 t2 then
                if eq_nat_dec sz1 sz1' then
                  if tc_typ (c_tenv C) D (Typ_ptr (Typ_array t1 sz1) r) then
                    Some (Nenv.add x (Ftyp_int WORDSIZE_BITS lt_63_MAX_I_BITS :: nil) G)
                    else None else None else None else None else None

        | _, _ => None
      end

    | Insn_gep1 x (Typ_ptr t1 r) o1 o2 =>
      match tc_op C D P G o1, tc_op C D P G o2 with
        | Some (Ftyp_ptr t1' r' :: nil), Some (Ftyp_int sz _ :: nil) =>
          if typ_eq_dec t1 t1' then
            if rgn_dec r r' then
              if tc_typ (c_tenv C) D (Typ_ptr t1 r) then
                Some (Nenv.add x (Ftyp_int WORDSIZE_BITS lt_63_MAX_I_BITS :: nil) G)
                else None else None else None
        | Some (Ftyp_int _ _ :: nil), Some (Ftyp_int _ _ :: nil) =>
          if tc_typ (c_tenv C) D (Typ_ptr t1 r) then
            Some (Nenv.add x (Ftyp_int WORDSIZE_BITS lt_63_MAX_I_BITS :: nil) G)
                else None
        | _, _ => None
      end
    | Insn_gep1 x (Typ_int _ _) o1 o2 =>
      match tc_op C D P G o1, tc_op C D P G o2 with
        | Some (Ftyp_int _ _ :: nil), Some (Ftyp_int _ _ :: nil) =>
          Some (Nenv.add x (Ftyp_int WORDSIZE_BITS lt_63_MAX_I_BITS :: nil) G)
        | _, _ => None
      end
    | Insn_gepU x (Typ_ptrU sz1 r) o (Op_const (Const_int sz2 pf2 i)) =>
      match tc_op C D P G o, tc_op C D P G (Op_const (Const_int sz2 pf2 i)) with
        | Some (Ftyp_ptrU sz1' r' :: nil), Some (Ftyp_int sz2' _ :: nil) =>
          if le_dec sz1 sz1' then
            if eq_nat_dec sz2 sz2' then
              if rgn_dec r r' then
                if tc_typ (c_tenv C) D (Typ_ptrU sz1 r) then
                  if zlt (Z.of_nat sz1') (Word.modulus Const63) then 
                    Some (Nenv.add x (Ftyp_ptrU (sz1 - (i2n i)) r :: nil) G) else None else None else None else None else None
        | Some (Ftyp_int _ _ :: nil), Some (Ftyp_int sz2' _ :: nil) =>
          if tc_typ (c_tenv C) D (Typ_ptrU sz1 r) then
            Some (Nenv.add x (Ftyp_ptrU 0 r :: nil) G) else None 
        | _, _ => None
      end
    | Insn_gepU x (Typ_ptrU sz r) o (Op_reg x2) =>
      match tc_op C D P G o, tc_op C D P G (Op_reg x2) with
        | Some (Ftyp_ptrU sz' r' :: nil), Some (Ftyp_int _ _ :: nil) =>
            if rgn_dec r r' then
              if tc_typ (c_tenv C) D (Typ_ptrU sz r) then
                Some (Nenv.add x (Ftyp_ptrU 0 r :: nil) G) else None else None
        | Some (Ftyp_int _ _ :: nil), Some (Ftyp_int sz2' _ :: nil) =>
          if tc_typ (c_tenv C) D (Typ_ptrU sz r) then
            Some (Nenv.add x (Ftyp_ptrU 0 r :: nil) G) else None 
        | _, _ => None
      end
    | Insn_gepU x (Typ_int sz pf) o1 o2 =>
      match tc_op C D P G o1, tc_op C D P G o2 with
        | Some (Ftyp_int _ _ :: nil), Some (Ftyp_int _ _ :: nil) =>
          Some (Nenv.add x (Ftyp_int WORDSIZE_BITS lt_63_MAX_I_BITS :: nil) G) 
        | Some (Ftyp_ptrU _ _ :: nil), Some (Ftyp_int _ _ :: nil) =>
          Some (Nenv.add x (Ftyp_int WORDSIZE_BITS lt_63_MAX_I_BITS :: nil) G) 
        | _, _ => None
      end

    | Insn_extractvalue x t1 o t2 (Const_int _ _ i) =>
      match tc_op C D P G o with
        | Some t1'' =>
          let t1' := flatten_typ (c_lo C) (c_tenv C) t1 in
          let t2' := flatten_typ (c_lo C) (c_tenv C) t2 in
          if ftyps_eq_dec t1' t1'' then
            if tc_typ (c_tenv C) D t1 then
              if tc_typ (c_tenv C) D t2 then
                if ftyps_subset t2' (skipn (i2n i) t1') then
                  (* if ftyps_subset t2' (skipn (Z.to_nat (Word.unsigned i)) t1') then *)
                  if le_dec (i2n i + (length t2'))%nat ((length t1')) then
                  (* if le_dec (Z.to_nat (Word.unsigned i) + (length t2'))%nat ((length t1')) then *)
                    Some (Nenv.add x t2' G)
                    else None else None else None else None else None
        | None => None
      end
    | Insn_insertvalue x t1 o1 t2 o2 (Const_int _ _ i) =>
      match tc_op C D P G o1, tc_op C D P G o2 with
        | Some t1'', Some t2'' =>
          let t1' := flatten_typ (c_lo C) (c_tenv C) t1 in
          let t2' := flatten_typ (c_lo C) (c_tenv C) t2 in
          if ftyps_eq_dec t1' t1'' then
            if ftyps_eq_dec t2' t2'' then
              if tc_typ (c_tenv C) D t1 then
                if tc_typ (c_tenv C) D t2 then
                  if ftyps_subset2 t2' (skipn (i2n i) t1') then
                  (* if ftyps_subset2 t2' (skipn (Z.to_nat (Word.unsigned i)) t1') then *)
                    if le_dec (i2n i + (length t2'))%nat ((length t1')) then
                    (* if le_dec (Z.to_nat (Word.unsigned i) + (length t2'))%nat ((length t1')) then *)
                      Some (Nenv.add x t1' G)
                      else None else None else None else None else None else None
        | _, _ => None
      end

    | Insn_iconv x c t o (Typ_int sz2 pf2) =>
      match c with
        | Iconv_trunc => 
          match tc_op C D P G o with
            | Some (Ftyp_int sz3 pf3 :: nil) =>
              match t with
                | Typ_int sz1 pf1 => 
                  if eq_nat_dec sz3 sz1 then
                    if lt_dec sz2 sz1 then
                      Some (Nenv.add x (Ftyp_int sz2 pf2 :: nil) G) else None else None
                | _ => None 
              end
            | _ => None
          end
        | Iconv_zext => 
          match tc_op C D P G o with
            | Some (Ftyp_int sz3 pf3 :: nil) =>
              match t with
                | Typ_int sz1 pf1 => 
                  if eq_nat_dec sz3 sz1 then
                    if lt_dec sz1 sz2 then
                      Some (Nenv.add x (Ftyp_int sz2 pf2 :: nil) G) else None else None
                | _ => None 
              end
            | _ => None
          end
        | Iconv_sext => 
          match tc_op C D P G o with
            | Some (Ftyp_int sz3 pf3 :: nil) =>
              match t with
                | Typ_int sz1 pf1 => 
                  if eq_nat_dec sz3 sz1 then
                    if lt_dec sz1 sz2 then
                      Some (Nenv.add x (Ftyp_int sz2 pf2 :: nil) G) else None else None
                | _ => None 
              end
            | _ => None
          end
        | Iconv_fptoui => 
          match tc_op C D P G o with
            | Some (Ftyp_float :: nil) => 
              match t with
                | Typ_float => Some (Nenv.add x (Ftyp_int sz2 pf2 :: nil) G)
                | _ => None
              end
            | Some (Ftyp_double :: nil) => 
              match t with
                | Typ_double => Some (Nenv.add x (Ftyp_int sz2 pf2 :: nil) G)
                | _ => None
              end
            | _ => None
          end
        | Iconv_fptosi => 
          match tc_op C D P G o with
            | Some (Ftyp_float :: nil) =>
              match t with
                | Typ_float => Some (Nenv.add x (Ftyp_int sz2 pf2 :: nil) G)
                | _ => None
              end
            | Some (Ftyp_double :: nil) =>
              match t with
                | Typ_double => Some (Nenv.add x (Ftyp_int sz2 pf2 :: nil) G)
                | _ => None
              end
            | _ => None
          end          
      end

    | Insn_fconv x c t o Typ_float =>
      match t, tc_op C D P G o with
        | Typ_double, Some (Ftyp_double :: nil) =>
          Some (Nenv.add x (Ftyp_float :: nil) G) 
        | Typ_float, Some (Ftyp_float :: nil) =>
          Some (Nenv.add x (Ftyp_float :: nil) G) 
        | Typ_int sz1 _, Some (Ftyp_int sz2 _ :: nil) =>
          if eq_nat_dec sz1 sz2 then
            Some (Nenv.add x (Ftyp_float :: nil) G) 
            else None
        | _, _ => None
      end
    | Insn_fconv x c t o Typ_double =>
      match t, tc_op C D P G o with
        | Typ_double, Some (Ftyp_double :: nil) =>
          Some (Nenv.add x (Ftyp_double :: nil) G) 
        | Typ_float, Some (Ftyp_float :: nil) =>
          Some (Nenv.add x (Ftyp_double :: nil) G) 
        | Typ_int sz1 _, Some (Ftyp_int sz2 _ :: nil) =>
          if eq_nat_dec sz1 sz2 then
            Some (Nenv.add x (Ftyp_double :: nil) G) 
            else None
        | _, _ => None 
      end

    | Insn_select x (Typ_int sz1 pf1) c t1 o1 t2 o2 =>
      match tc_op C D P G c, tc_op C D P G o1, tc_op C D P G o2 with
        | Some (Ftyp_int sz2 pf2 :: nil), Some t1', Some t2' =>
          if eq_nat_dec sz1 sz2 then
            if typ_eq_dec t1 t2 then
              if ftyps_weaken t1' (flatten_typ (c_lo C) (c_tenv C) t1) then
                if ftyps_weaken t2' (flatten_typ (c_lo C) (c_tenv C) t1) then
                  if tc_typ (c_tenv C) D t1 then
                    if eq_nat_dec 0 sz2 then
                      Some (Nenv.add x (flatten_typ (c_lo C) (c_tenv C) t1) G) else None else None else None else None else None else None
        | _, _, _ => None
      end
    | Insn_exit => Some G
    | _ => None
  end.

Ltac tc_simpl :=
  repeat
    match goal with
      | [ H: Some _ = Some _ |- _ ] => inv H
      | [ H: None = Some _ |- _ ] => inv H
      | [ H: tc_op ?C ?D ?P ?G ?o = Some ?t |- _ ] => 
        rewrite H in *; specialize (tc_op_correct C D P G o t H); clear H; simpl in *; intros
      | [ H: tc_op ?C ?D ?P ?G ?o = None |- _ ] => 
        rewrite H in *; clear H; simpl in *; try congruence
      | [ H: context [ match ?a with
                         | nil => _
                         | _ :: _ => _
                       end ] |- _ ] => destruct a; try congruence
      | [ H: context [ match ?t with
                         | Ftyp_float => _
                         | Ftyp_double => _
                         | Ftyp_int _ _ => _
                         | Ftyp_ptr _ _ => _
                         | Ftyp_fun _ _ _ => _
                         | Ftyp_ptrU _ _ => _
                       end ] |- _ ] => destruct t; try congruence
      | [ H: context [ match ?t with
                         | Typ_float => _
                         | Typ_double => _
                         | Typ_int _ _ => _
                         | Typ_ptr _ _ => _ 
                         | Typ_name _ _ => _
                         | Typ_fun _ _ _ => _ 
                         | Typ_array _ _ => _
                         | Typ_ptrU _ _ => _
                       end ] |- _ ] => destruct t; try congruence
      | [ H: context [ match ?o with
                         | Op_reg _ => _
                         | Op_const _ => _
                       end ] |- _ ] => destruct o; try congruence
      | [ H: context [ match ?c with
                         | Const_null => _
                         | Const_nullU => _
                         | Const_float _ => _
                         | Const_double _ => _
                         | Const_int _ _ _ => _
                         | Const_fun _ => _
                         | Const_undef _ => _
                         | Const_baddr _ _ => _
                       end ] |- _ ] => destruct c; try congruence
      | [ H: context [ let (_, _) := ?p in _ ] |- _ ] => destruct p
      | [ H: Nenv.find ?r ?D = Some ?t |- _ ] =>
        rewrite H in *; simpl in *
      | [ H: Nenv.find ?r ?D = None |- _ ] =>
        rewrite H in *; try congruence
      | [ H: context [ typ_eq_dec ?t1 ?t2 ] |- _ ] =>
        destruct (typ_eq_dec t1 t2); try congruence; subst
      | [ H: context [ rgn_dec ?r1 ?r2 ] |- _ ] =>
        destruct (rgn_dec r1 r2); try congruence; subst
      | [ H: context [ ftyps_eq_dec ?t1 ?t2 ] |- _ ] =>
        destruct (ftyps_eq_dec t1 t2); try congruence; subst
      | [ H: context [ le_dec ?a ?b ] |- _ ] =>
        destruct (le_dec a b); try congruence
      | [ H: context [ lt_dec ?a ?b ] |- _ ] =>
        destruct (lt_dec a b); try congruence
      | [ H: context [ ge_dec ?a ?b ] |- _ ] =>
        destruct (ge_dec a b); try congruence
      | [ H: context [ eq_nat_dec ?n1 ?n2 ] |- _ ] =>
        destruct (eq_nat_dec n1 n2); try congruence; subst
      | [ H: context [ lab_dec ?l1 ?l2 ] |- _ ] =>
        destruct (lab_dec l1 l2); try congruence; subst
      | [ H: TSb ?tenv ?t = true |- _ ] =>
        rewrite H in *; specialize (TSb_correct tenv t H); clear H; simpl in *; intros; try congruence
      | [ H: context [ if ftyps_subset ?t ?t' then _ else _ ] |- _ ] =>
        let H' := fresh "H'" in 
          case_eq (ftyps_subset t t'); intros H'; rewrite H' in *; simpl in *; try congruence
      | [ H: context [ if ftyps_subset2 ?t ?t' then _ else _ ] |- _ ] =>
        let H' := fresh "H'" in 
          case_eq (ftyps_subset2 t t'); intros H'; rewrite H' in *; simpl in *; try congruence
      | [ H: TSb ?tenv ?t = false |- _ ] =>
        rewrite H in *; clear H; try congruence
      | [ H: tc_typ ?tenv ?D ?t = true |- _ ] =>
        rewrite H in *; specialize (tc_typ_correct t D tenv H); clear H; simpl in *; intros; try congruence
      | [ H: tc_typ ?tenv ?D ?t = false |- _ ] =>
        rewrite H in *; clear H; try congruence
      | [ H: context [ tc_op ?C ?D ?P ?G ?o ] |- _ ] => 
        case_eq (tc_op C D P G o); intros
      | [ H: context [ TSb ?tenv ?t ] |- _ ] =>
        case_eq (TSb tenv t); intros
      | [ H: context [ match Nenv.find ?r ?D with
                         | Some _ => _ 
                         | None => _
                       end] |- _ ] =>
        case_eq (Nenv.find r D); intros
      | [ H: context [ tc_typ ?tenv ?D ?t ] |- _ ] =>
        case_eq (tc_typ tenv D t); intros
      | [ H: context [ if false && false then _ else _ ] |- _ ] =>
        simpl in H
    end.

Ltac tc_simpl_pro :=
  repeat
    match goal with
      | [ H: tc_op ?C ?D ?P ?G ?o = Some ?t |- _ ] => 
        specialize (tc_op_correct C D P G o t H); clear H; simpl in *; intros
      | [ H: Some ?a = Some ?b |- _ ] => inv H
      | [ H: context [ match ?a with
                         | nil => _
                         | _ :: _ => _
                       end ] |- _ ] => destruct_c a
      | [ H: context [ match ?t with
                         | Ftyp_float => _
                         | Ftyp_double => _
                         | Ftyp_int _ _ => _
                         | Ftyp_ptr _ _ => _
                         | Ftyp_fun _ _ _ => _
                         | Ftyp_ptrU _ _ => _
                       end ] |- _ ] => destruct_c t
      | [ H: context [ match ?t with
                         | Typ_float => _
                         | Typ_double => _
                         | Typ_int _ _ => _
                         | Typ_ptr _ _ => _ 
                         | Typ_name _ _ => _
                         | Typ_fun _ _ _ => _ 
                         | Typ_array _ _ => _
                         | Typ_ptrU _ _ => _
                       end ] |- _ ] => destruct_c t
      | [ H: context [ tc_op ?C ?D ?P ?G ?o ] |- _ ] =>
        consider (tc_op C D P G o); intros; try congruence
      | [ H: context [ eq_nat_dec ?n1 ?n2 ] |- _ ] =>
        destruct_c eq_nat_dec; subst
      | [ H: context [ lt_dec ?n1 ?n2 ] |- _ ] =>
        destruct_c lt_dec; subst
      | [ H: (Const31 < MAX_I_BITS)%nat |- _ ] =>
        specialize (proof_irr lt_31_MAX_I_BITS H); intros; subst
      | [ H: (Const63 < MAX_I_BITS)%nat |- _ ] =>
        specialize (proof_irr lt_63_MAX_I_BITS H); intros; subst
      | [ H1: (?sz < MAX_I_BITS)%nat, 
          H2: (?sz < MAX_I_BITS)%nat |- _ ] =>
        specialize (proof_irr H1 H2); intros; subst
    end.

Lemma tc_insn_correct : forall C D P i G1 G2,
  tc_insn C D P i G1 = Some G2 ->
  wf_insn C D P i G1 G2.
Proof.
  Opaque tc_typ.
  destruct i; simpl; intros.
  { tc_simpl_pro; econstructor; eauto. }
  { tc_simpl_pro; econstructor; eauto. }
  { tc_simpl_pro; econstructor; eauto; simpl; auto. }
  { tc_simpl_pro; econstructor; eauto; simpl; auto. }
  { tc_simpl. 
    consider (ftyps_weaken f (flatten_typ (c_lo C) (c_tenv C) t1)); intros; try congruence.
    consider (ftyps_weaken f0 (flatten_typ (c_lo C) (c_tenv C) t1)); intros; try congruence.
    destruct sz0. inv H5. 
    assert (l = l0). apply proof_irr. subst. 
    assert (Typ_int1 = Typ_int 0 l0). unfold Typ_int1. f_equal. apply proof_irr. 
    rewrite <- H5.
    apply wf_insn_select with (t1 := f) (t2 := f0); auto.
    unfold Ftyp_int1. assert (lt_0_MAX_I_BITS = l0). apply proof_irr. subst. auto.
    inv H5.
    consider (ftyps_weaken f (flatten_typ (c_lo C) (c_tenv C) t1)); intros; try congruence.
    consider (ftyps_weaken f0 (flatten_typ (c_lo C) (c_tenv C) t1)); intros; try congruence. }
  { tc_simpl. econstructor; eauto.
    repeat destruct_c n; inv H; econstructor; eauto. }
  { tc_simpl; try econstructor; eauto. 
    destruct_c zle. destruct_c zle. inv H. 
    econstructor; eauto. }
  { tc_simpl. eapply wf_insn_poolcheck_int; eauto. econstructor; eauto. }
  { tc_simpl. 
    eapply wf_insn_free_int; eauto.
    eapply wf_insn_free; eauto.
    eapply wf_insn_freeU_int; eauto.
    econstructor; eauto. }
  { destruct_c t. destruct_c t. destruct_c o0.
    remember (Nenv.find i0 (c_tenv C)) as Hd. destruct_c Hd.
    tc_simpl. inv e. destruct p. econstructor; eauto. 

    destruct_c c. 
    remember (Nenv.find i0 (c_tenv C)) as Hd. destruct_c Hd.
    tc_simpl. inv e0. 
    eapply wf_insn_gep_name with (t := t0); eauto.
    simpl in *. rewrite <- HeqHd. auto. simpl. rewrite <- HeqHd. auto.

    tc_simpl. econstructor; eauto. destruct_c zlt. inv H. econstructor; eauto.
    split; auto. unfold i2n in l1. 
    assert (Z.of_nat (nat_of_Z (Word.unsigned i0)) < Z.of_nat n0).
    omega.
    assert (forall n, nat_of_Z n = Z.to_nat n). destruct n; auto.
    rewrite H2 in H. rewrite Z2Nat.id in H; auto.
    specialize (Word.unsigned_range i0); intros. intuition.
    destruct_c zlt. }
  { tc_simpl. econstructor; eauto. eapply wf_insn_gep1_int; eauto. econstructor; eauto. }
  { destruct_c c. tc_simpl. econstructor; eauto. }
  { destruct_c c. tc_simpl. econstructor; eauto. }
  { destruct i0; tc_simpl_pro; econstructor; eauto. }
  { tc_simpl_pro; econstructor; eauto. }
  { tc_simpl. econstructor; eauto. destruct_c zle. inv H. econstructor; eauto. }
  { tc_simpl.
    assert (lt_63_MAX_I_BITS = l). apply proof_irr. rewrite <- H.
    econstructor; eauto. 
    assert (lt_63_MAX_I_BITS = l). apply proof_irr. rewrite <- H.
    econstructor; eauto. }
  { unfold Const31 in *. tc_simpl.
    assert (lt_63_MAX_I_BITS = l). apply proof_irr. rewrite <- H.
    econstructor; eauto. 
    assert (lt_63_MAX_I_BITS = l0). apply proof_irr. rewrite <- H2 in H0.
    eauto. 
    assert (Typ_int 63 l = Typ_int64). unfold Typ_int64. f_equal. apply proof_irr.
    unfold WORDSIZE_BITS in *. rewrite H. econstructor; eauto. 
    assert (Ftyp_int 63 l0 = Ftyp_int64). unfold Ftyp_int64. f_equal. apply proof_irr.
    rewrite <- H2. auto. }
  { Opaque eq_nat_dec. tc_simpl. 
    eapply wf_insn_gepU_int; eauto.
    eapply wf_insn_gepU_int2; eauto.
    eapply wf_insn_gepU3; eauto.
    eapply wf_insn_gepU2; eauto.
    eapply wf_insn_gepU3; eauto.
    destruct_c zlt. inv H. econstructor; eauto. 
    split; auto. unfold Const0. apply inj_le. omega. }
  { simpl in H. tc_simpl. eapply wf_insn_poolcheckU_int; eauto. 
    econstructor; eauto. }
  { inv H. eauto. }
Qed.

(* ---------------------------------------------------------------------- *)
Fixpoint tc_phi_args (C:config) (D:Delta) (P:Psi) (G:Gamma) (ls:list (operand*lab)) (l:lab) (t:ftyps) : bool :=
  match ls with
    | (o,l')::ls => 
      if lab_dec l l' then
        match t with
          | Ftyp_ptr t1 r1 :: nil =>
            match tc_op C D P G o with
              | Some (Ftyp_ptr t2 r2 :: nil) =>
                if ftyps_subset (flatten_typ (c_lo C) (c_tenv C) t1) (flatten_typ (c_lo C) (c_tenv C) t2) then
                  if rgn_dec r1 r2 then
                    if TSb (c_tenv C) t1 then
                      if TSb (c_tenv C) t2 then
                        if tc_ftyp (c_tenv C) D (Ftyp_ptr t1 r1) then
                          true
                          else false else false else false else false else false
              | _ => false
            end
          | Ftyp_ptrU sz1 r1 :: nil =>
            match o with
              (*
              | Op_const Const_nullU => tc_ftyp (c_tenv C) D (Ftyp_ptrU sz1 r1)
              *)
              | _ =>
                match tc_op C D P G o with
                  | Some (Ftyp_ptrU sz2 r2 :: nil) =>
                    if ge_dec sz2 sz1 then
                      if rgn_dec r1 r2 then
                        if tc_ftyp (c_tenv C) D (Ftyp_ptrU sz1 r1) then
                          true
                          else false else false else false
                  | _ => false
                end
            end
          | _ =>
            match tc_op C D P G o with
              | Some t' => ftyps_weaken t' t (* if ftyps_eq_dec t t' then true else false *)
              | _ => false
            end
        end
        else tc_phi_args C D P G ls l t
    | _ => false
  end.

Lemma tc_phi_args_correct : forall C D P G ls l t,
  tc_phi_args C D P G ls l t = true ->
  wf_phi_args C D P G ls l t.
Proof.
  induction ls; intros; tc_simpl. crush. 
  inv H. destruct a. destruct_c lab_dec; subst. destruct_c t.
  tc_simpl. econstructor; eauto.
  destruct_c f. 
  consider (tc_op C D P G o); intros.
  econstructor; eauto. eapply tc_op_correct; eauto.
  consider (tc_op C D P G o); intros.
  econstructor; eauto. eapply tc_op_correct; eauto.
  consider (tc_op C D P G o); intros. econstructor; eauto. eapply tc_op_correct; eauto.
  destruct_c t. consider (tc_op C D P G o); intros. 
  destruct_c f. simpl in H1. inv H1.
  destruct_c f. destruct_c f0.
  consider (ftyps_subset (flatten_typ (c_lo C) (c_tenv C) t0)
             (flatten_typ (c_lo C) (c_tenv C) t)); intros.
  destruct_c rgn_dec. subst. econstructor; eauto. eapply tc_op_correct; eauto.
  tc_simpl. econstructor; eauto.  
  tc_simpl. tc_simpl. 
  consider (tc_op C D P G o); intros. 
  econstructor; eauto. eapply tc_op_correct; eauto.
  consider (tc_op C D P G o); intros.

  { econstructor; eauto. eapply tc_op_correct; eauto. }
  { destruct_c t. tc_simpl. econstructor; eauto.
    tc_simpl. econstructor; eauto. }
  { eauto. }
Qed.

(* ---------------------------------------------------------------------- *)
Definition tc_phinode (C:config) (D:Delta) (P:Psi) (p:phinode) (l:lab) (G:Gamma) : option Gamma :=
  match p with
    | Insn_phi x t ls =>
      let t' := flatten_typ (c_lo C) (c_tenv C) t in
      if tc_phi_args C D P G ls l t' then Some (Nenv.add x t' G) else None
  end.

Lemma tc_phinode_correct : forall C D P p l G1 G2,
  tc_phinode C D P p l G1 = Some G2 ->
  wf_phinode C D P p l G1 G2.
Proof.
  destruct p; simpl; intros.
  remember (tc_phi_args C D P G1 l l0 (flatten_typ (c_lo C) (c_tenv C) t)) as Hd.
  symmetry in HeqHd. destruct Hd; try congruence.
  tc_simpl. eapply tc_phi_args_correct in HeqHd; eauto.
Qed.

(* ---------------------------------------------------------------------- *)
Fixpoint tc_phi_blk (C:config) (D:Delta) (P:Psi) (ps:phiblock) (l:lab) (G:Gamma) : option Gamma :=
  match ps with
    | nil => Some G
    | p::ps =>
      match tc_phinode C D P p l G with
        | Some G2 => tc_phi_blk C D P ps l G2
        | None => None
      end
  end.

Lemma tc_phi_blk_correct : forall C D P ps l G1 G2,
  tc_phi_blk C D P ps l G1 = Some G2 ->
  wf_phi_blk C D P ps l G1 G2.
Proof.
  induction ps; simpl; intros. inv H. econstructor; eauto.
  remember (tc_phinode C D P a l G1) as Hd.
  symmetry in HeqHd. destruct Hd; try congruence. 
  eapply tc_phinode_correct in HeqHd; eauto.
Qed.

(* ---------------------------------------------------------------------- *)
(* correct if no duplicates ... *)        

Fixpoint tc_extends_gamma' {A:Type} (feq : forall (x y:A), {x = y} + {x <> y}) (G1: list (Nenv.key*A)) (G2:Nenv.t A) : bool :=
  match G1 with
    | nil => true
    | (x,t)::G1' =>
      match Nenv.find x G2 with
        | Some t' => if feq t t' then tc_extends_gamma' feq G1' G2 else false
        | None => false
      end
  end.

Lemma tc_extends_gamma_correct' : forall {A} f ls G2,
  SetoidList.NoDupA (Nenv.eq_key (elt:=A)) ls ->
  tc_extends_gamma' f ls G2 = true ->
  (forall x t, SetoidList.InA (Nenv.eq_key_elt (elt:=A)) (x,t) ls -> Nenv.find x G2 = Some t).
Proof.
  induction ls; simpl; intros. rewrite SetoidList.InA_nil in H1. contradiction.
  destruct a. remember (Nenv.find k G2) as Hd.
  destruct Hd; try congruence. symmetry in HeqHd.
  destruct (f a a0); try congruence; subst.
  unfold extends_gamma; intros. inv H. inv H1.
  inv H2. simpl in H. simpl in H1. subst. auto.
  eapply IHls in H0; eauto. 
Qed.

Definition tc_extends_gamma {A:Type} (feq : forall (x y:A), {x = y} + {x <> y}) (G1 G2:Nenv.t A) : bool :=
  tc_extends_gamma' feq (Nenv.elements G1) G2.

Definition extends_gamma2 {A:Type} (G1 G2:Nenv.t A) :=
  forall x t,
    Nenv.find x G1 = Some t ->
    Nenv.find x G2 = Some t.

Lemma tc_extends_gamma_correct2 : forall {A:Type} f (G1 G2:Nenv.t A),
  tc_extends_gamma f G1 G2 = true ->
  extends_gamma2 G1 G2.
Proof.
  unfold tc_extends_gamma; intros. 
  specialize (Nenv.elements_3w G1); intros.
  specialize (tc_extends_gamma_correct' f (Nenv.elements G1) G2 H0 H); intros.
  unfold extends_gamma2; intros.
  eapply tc_extends_gamma_correct' in H0; eauto.
  rewrite <- NFacts.elements_mapsto_iff.
  rewrite NFacts.find_mapsto_iff; auto.
Qed.

Lemma tc_extends_gamma_correct : forall G1 G2,
  tc_extends_gamma ftyps_eq_dec G1 G2 = true ->
  extends_gamma G1 G2.
Proof.
  unfold tc_extends_gamma; intros.
  specialize (Nenv.elements_3w G1); intros.
  specialize (tc_extends_gamma_correct' _ (Nenv.elements G1) G2 H0 H). intros.
  unfold extends_gamma; intros.
  eapply tc_extends_gamma_correct' in H0; eauto.
  rewrite <- NFacts.elements_mapsto_iff.
  rewrite NFacts.find_mapsto_iff; auto.
Qed.

(* ---------------------------------------------------------------------- *)
Definition tc_junction (C:config) (D:Delta) (P:Psi) (G1:Gamma) (bs:blocks) (l1 l2:lab) : bool :=
  match Ienv.find l2 P, lookup_blk l2 bs with
    | Some G2, Some b =>
      match tc_phi_blk C D P (b_phis b) l1 G1 with
        | Some G3 => tc_extends_gamma ftyps_eq_dec G2 G3
        | None => false
      end
    | _, _ => false
  end.

Lemma tc_junction_correct : forall C D P G1 bs l1 l2,
  tc_junction C D P G1 bs l1 l2 = true ->
  wf_junction C D P G1 bs l1 l2.
Proof.
  unfold tc_junction; simpl; intros.
  remember (Ienv.find l2 P) as Hd. destruct Hd; try congruence.
  remember (lookup_blk l2 bs) as Hd2. destruct Hd2; try congruence.
  remember (tc_phi_blk C D P (b_phis b) l1 G1) as Hd3. destruct Hd3; try congruence.
  symmetry in HeqHd. symmetry in HeqHd2. symmetry in HeqHd3.
  eapply tc_phi_blk_correct in HeqHd3; eauto.
  eapply tc_extends_gamma_correct in H; eauto.
  econstructor; eauto 10.
Qed.

(* ---------------------------------------------------------------------- *)
Fixpoint tc_switch_arms (C:config) (D:Delta) (P:Psi) (G:Gamma) (bs:blocks) (t:typ) (l:lab) (ls:list (typ * IllvmAST.const * lab)) : bool :=
  match ls with
    | nil => match t with
               | Typ_int _ _ => true
               | _ => false
             end
    | (Typ_int sz1 pf1, Const_int sz2 pf2 i, l')::ls' =>
      match t with
        | Typ_int sz3 _ =>
          if eq_nat_dec sz1 sz2 then
            if eq_nat_dec sz1 sz3 then
              if tc_junction C D P G bs l l' then
                tc_switch_arms C D P G bs t l ls' else false else false else false
        | _ => false
      end
    | _ => false
  end.

Lemma tc_switch_arms_correct : forall C D P G bs t l ls,
  tc_switch_arms C D P G bs t l ls = true ->
  wf_switch_arms C D P G bs t l ls.
Proof.
  induction ls; simpl; intros. destruct_c t. econstructor.
  destruct a. destruct p. destruct_c t0. destruct_c c.
  destruct_c t. destruct_c eq_nat_dec. destruct_c eq_nat_dec.
  remember (tc_junction C D P G bs l l0) as Hd. destruct_c Hd.
  symmetry in HeqHd. apply tc_junction_correct in HeqHd.
  subst. assert (l2 = l1). apply proof_irr. subst.
  assert (l3 = l1). apply proof_irr. subst.
  eapply IHls in H. econstructor; eauto.
Qed.

(* ---------------------------------------------------------------------- *)
Fixpoint tc_indirect_br_arms (C:config) (D:Delta) (P:Psi) (G:Gamma) (bs:blocks) (l:lab) (ls:list lab) : bool :=
  match ls with
    | nil => true
    | l'::ls' => 
      if tc_junction C D P G bs l l' then 
        tc_indirect_br_arms C D P G bs l ls' else false
  end.

Lemma tc_indirect_br_arms_correct : forall C D P G bs l ls,
  tc_indirect_br_arms C D P G bs l ls = true ->
  wf_indirect_br_arms C D P G bs l ls.
Proof.
  induction ls; simpl; intros. constructor.
  remember (tc_junction C D P G bs l a) as Hd. destruct_c Hd.
  symmetry in HeqHd. apply tc_junction_correct in HeqHd. 
  constructor; auto.
Qed.

(* ---------------------------------------------------------------------- *)
Definition tc_term (C:config) (D:Delta) (P:Psi) (G:Gamma) (bs:blocks) (l:lab) (term:terminator) : bool :=
  match term with
    | Insn_return t o =>
      match tc_op C D P G o with
        | Some t' => 
          if ftyps_eq_dec (flatten_typ (c_lo C) (c_tenv C) t) t' then
            if tc_typ (c_tenv C) D t then
                true else false else false
        | _ => false
      end
    | Insn_return_void => true
    | Insn_br_uncond l' =>
      if tc_junction C D P G bs l l' then true else false
    | Insn_br o l1 l2 =>
      match tc_op C D P G o with
        | Some (Ftyp_int sz _ :: nil) =>
          if eq_nat_dec sz 0 then
            if tc_junction C D P G bs l l1 then
              if tc_junction C D P G bs l l2 then
                true else false else false else false
        | _ => false
      end
    | Insn_switch (Typ_int sz1 pf1) o ldef ls =>
      match tc_op C D P G o with
        | Some (Ftyp_int sz2 _ :: nil) =>
          if eq_nat_dec sz1 sz2 then
            if tc_junction C D P G bs l ldef then
              tc_switch_arms C D P G bs (Typ_int sz1 pf1) l ls 
              else false else false 
        | _ => false
      end
    | Insn_indirect_br (Typ_ptr (Typ_int sz1 pf1) r1) o ls =>
      match o with
        | Op_reg x =>
          match Nenv.find x G with
            | Some (Ftyp_ptr (Typ_int sz2 pf2) r2 :: nil) =>
              if eq_nat_dec sz1 sz2 then
                if rgn_dec r1 r2 then
                  if eq_nat_dec sz2 7 then
                    tc_indirect_br_arms C D P G bs l ls else false else false else false
            | _ => false
          end
        | Op_const (Const_baddr _ _) =>
          if eq_nat_dec sz1 7 then tc_indirect_br_arms C D P G bs l ls else false
        | _ => false
      end
    | Insn_unreachable => true
    | _ => false
  end.

Lemma tc_term_correct : forall C D P G bs l term,
  tc_term C D P G bs l term = true ->
  wf_term C D P G bs l term.
Proof.
  destruct term; crush; tc_simpl.
  { econstructor; eauto. }
  { consider (tc_junction C D P G bs l l0); intros; try congruence.
    eapply tc_junction_correct in H; eauto. }
  { consider (tc_junction C D P G bs l l0); intros; try congruence.
    consider (tc_junction C D P G bs l l1); intros; try congruence.
    eapply tc_junction_correct in H; eauto.
    eapply tc_junction_correct in H1; eauto.
    econstructor; eauto. unfold Ftyp_int1.
    assert (lt_0_MAX_I_BITS = l2). apply proof_irr. subst. auto. }
  { consider (tc_junction C D P G bs l l0); intros; try congruence.
    eapply tc_junction_correct in H; eauto.
    eapply tc_switch_arms_correct in H1; eauto. 
    econstructor; eauto. apply (Word.repr 0).
    assert (l3 = l2). apply proof_irr. subst. auto. }
  { eapply tc_indirect_br_arms_correct in H. 
    eapply wf_indirect_br  with (o := Op_reg i) in H; eauto. unfold Typ_int8 in H.
    assert (lt_7_MAX_I_BITS = l1). apply proof_irr. subst. eauto.
    unfold Typ_int8. assert (lt_7_MAX_I_BITS = l2). apply proof_irr. subst. auto. }
  { eapply tc_indirect_br_arms_correct in H.
    eapply wf_indirect_br with (o := (Op_const (Const_baddr l2 l3))) in H; eauto.
    unfold Typ_int8 in H. assert (lt_7_MAX_I_BITS = l1). apply proof_irr. subst. eauto. }
Qed.

(* ---------------------------------------------------------------------- *)
Fixpoint tc_args (C:config) (D:Delta) (P:Psi) (G:Gamma) (rmap:Nenv.t rgn) (os:list operand) (ts:list typ) : bool :=
  match os, ts with
    | nil, nil => true
    | o :: os, t :: ts =>
      match tc_op C D P G o with
        | Some t' =>
          let t := sigma rmap (flatten_typ (c_lo C) (c_tenv C) t) in
          if ftyps_weaken t' t then
            tc_args C D P G rmap os ts else false
        | _ => false
      end
    | _, _ => false
  end.

Lemma tc_args_correct : forall C D P G rmap os ts,
  tc_args C D P G rmap os ts = true ->
  wf_args C D P G rmap os ts.
Proof.
  induction os; destruct ts; intros. 
  destruct C; crush; tc_simpl. 
  destruct C; crush; tc_simpl. 
  destruct C; crush; tc_simpl.
  simpl in H.
  remember (tc_op C D P G a) as Hd. destruct_c Hd. symmetry in HeqHd.
  apply tc_op_correct in HeqHd.
  remember (sigma rmap (flatten_typ (c_lo C) (c_tenv C) t)) as Hd2. symmetry in HeqHd2.
  destruct_c Hd2. consider (ftyps_weaken f nil); intros; try congruence. 
  subst. destruct C. econstructor; eauto.
  simpl in *. rewrite HeqHd2. auto.
  consider (ftyps_weaken f (f0 :: Hd2)); intros; try congruence.
  destruct C. simpl in *. econstructor; eauto. rewrite HeqHd2. auto.
Qed.

(* ---------------------------------------------------------------------- *)
Fixpoint tc_prgn_inst (D:Delta) (lr:list rgn) : bool :=
  match lr with
    | nil => true
    | r::lr => match Nenv.find r D with
                 | Some t => tc_prgn_inst D lr
                 | None => false
               end
  end.

Lemma tc_prgn_inst_correct : forall D lr,
  tc_prgn_inst D lr = true ->
  wf_prgn_inst D lr.
Proof.
  induction lr; crush; tc_simpl; eauto.
Qed.

(* ---------------------------------------------------------------------- *)
Definition tc_nd (C:config) (D:Delta) (P:Psi) (G:Gamma) (bs:blocks) (nd:insn_nd) (l':lab) : bool :=
  match nd with
    | Insn_call (Some x) (Some t) o prgns args l =>
      match tc_op C D P G o with
        | Some (Ftyp_fun fprgns sig (Some t') :: nil) =>
          let ft := sigma (inst_prgn fprgns prgns) (flatten_typ (c_lo C) (c_tenv C) t') in
          if ftyps_weaken ft (flatten_typ (c_lo C) (c_tenv C) t) then
          (* if typ_eq_dec (sigma'' (inst_prgn fprgns prgns) t') t then *)
            if tc_ftyps (c_tenv C) D ft then
              if tc_args C D P G (inst_prgn fprgns prgns) args sig then
                if tc_prgn_inst D prgns then
                  if tc_term C D P (Nenv.add x (flatten_typ (c_lo C) (c_tenv C) t) G) bs l' (Insn_br_uncond l) then
                    if eq_nat_dec (length fprgns) (length prgns) then
                      true else false else false else false else false else false else false
        | _ => false
      end
    | Insn_call None None o prgns args l =>
      match tc_op C D P G o with
        | Some (Ftyp_fun fprgns sig None :: nil) =>
          if tc_args C D P G (inst_prgn fprgns prgns) args sig then
            if tc_prgn_inst D prgns then
              if tc_term C D P G bs l' (Insn_br_uncond l) then
                if eq_nat_dec (length fprgns) (length prgns) then
                  true else false else false else false else false 
        | _ => false
      end
    | Insn_malloc x (Some t) r o l =>
      match tc_op C D P G o with
        | Some (Ftyp_int _ _ :: nil) =>
          match Nenv.find r D with
            | Some t' =>
              if typ_eq_dec t t' then
                if tc_typ (c_tenv C) D t then
                  if tc_term C D P (Nenv.add x (Ftyp_ptr t r :: nil) G) bs l' (Insn_br_uncond l) then
                    true else false else false else false
            | None => false
          end
        | _ => false
      end
    | Insn_malloc x None r (Op_reg x2) l =>
      match tc_op C D P G (Op_reg x2) with
        | Some (Ftyp_int _ _ :: nil) =>
          (* if eq_nat_dec sz 31 then *)
            if tc_term C D P (Nenv.add x (Ftyp_ptrU 0 r :: nil) G ) bs l' (Insn_br_uncond l) then
              true else false
        | _ => false
      end
    | Insn_malloc x None r (Op_const (Const_int sz pf i)) l =>
      match tc_op C D P G (Op_const (Const_int sz pf i)) with
        | Some (Ftyp_int _ _ :: nil) =>
          (* if eq_nat_dec sz 31 then *)
            if tc_term C D P (Nenv.add x (Ftyp_ptrU (i2n i) r :: nil) G ) bs l' (Insn_br_uncond l) then
              true else false
        | _ => false
      end
    | Insn_unsafe_call xt _ _ l =>
      match xt with
        | Some (x, t) => tc_term C D P (Nenv.add x (flatten_typ (c_lo C) (c_tenv C) t) G) bs l' (Insn_br_uncond l)
        | None => true
      end
    | _ => false
  end.

Lemma tc_nd_correct : forall C D P G bs nd l',
  tc_nd C D P G bs nd l' = true ->
  wf_nd C D P G bs nd l'.
Proof.
  destruct nd; simpl; intros. 
  tc_simpl; repeat match goal with
                     | [ H: context [ match ?o with
                                        | Some _ => _
                                        | None => _
                                      end ] |- _ ] => destruct o; try congruence
                   end; tc_simpl.
  { consider (ftyps_weaken
    (sigma (inst_prgn l2 l) (flatten_typ (c_lo C) (c_tenv C) t0))
    (flatten_typ (c_lo C) (c_tenv C) t)); intros; try congruence.
    consider (tc_ftyps (c_tenv C) D
      (sigma (inst_prgn l2 l) (flatten_typ (c_lo C) (c_tenv C) t0))); intros; try congruence.
    consider (tc_args C D P G (inst_prgn l2 l) l0 l3); intros; try congruence.
    consider (tc_prgn_inst D l); intros; try congruence.
    consider (tc_junction C D P
      (Nenv.add i (flatten_typ (c_lo C) (c_tenv C) t) G) bs l' l1); intros; try congruence.
    eapply tc_ftyps_correct in H1; eauto.
    eapply tc_args_correct in H2; eauto.
    eapply tc_prgn_inst_correct in H3; eauto.
    eapply tc_junction_correct in H4; eauto.
    destruct C. simpl in *. econstructor; eauto. }
  { consider (tc_args C D P G (inst_prgn l2 l) l0 l3); intros; try congruence.
    consider (tc_prgn_inst D l); intros; try congruence.
    consider (tc_junction C D P G bs l' l1); intros; try congruence.
    eapply tc_args_correct in H; eauto.
    eapply tc_prgn_inst_correct in H1; eauto.
    eapply tc_junction_correct in H2; eauto.
    destruct C. simpl in *. econstructor; eauto. }
  { consider (ftyps_weaken
    (sigma (inst_prgn l2 l) (flatten_typ (c_lo C) (c_tenv C) t0))
    (flatten_typ (c_lo C) (c_tenv C) t)); intros; try congruence.
    consider (tc_ftyps (c_tenv C) D
      (sigma (inst_prgn l2 l) (flatten_typ (c_lo C) (c_tenv C) t0))); intros; try congruence.
    consider (tc_args C D P G (inst_prgn l2 l) l0 l3); intros; try congruence.
    consider (tc_prgn_inst D l); intros; try congruence.
    consider (tc_junction C D P
      (Nenv.add i (flatten_typ (c_lo C) (c_tenv C) t) G) bs l' l1); intros; try congruence. }
  { consider (tc_args C D P G (inst_prgn l2 l) l0 l3); intros; try congruence.
    consider (tc_prgn_inst D l); intros; try congruence.
    consider (tc_junction C D P G bs l' l1); intros; try congruence. }
  destruct o; tc_simpl.
  remember (tc_junction C D P (Nenv.add i (Ftyp_ptr t0 r :: nil) G) bs l' l) as Hd.
  tc_simpl. destruct Hd; try congruence. symmetry in HeqHd.
  destruct C. econstructor; eauto.

  econstructor; eauto. eapply tc_junction_correct; eauto. 
  remember (tc_junction C D P (Nenv.add i (Ftyp_ptrU 0 r :: nil) G) bs l' l) as Hd.
  destruct_c Hd. symmetry in HeqHd. destruct C. econstructor; eauto. econstructor; eauto.
  eapply tc_junction_correct; eauto.

  remember (tc_junction C D P (Nenv.add i (Ftyp_ptrU (i2n i0) r :: nil) G)
               bs l' l) as Hd.
  destruct_c Hd. symmetry in HeqHd. destruct C. econstructor; eauto. econstructor; eauto.
  eapply tc_junction_correct; eauto.

  destruct C. destruct o. destruct p. simpl in H.
  consider (tc_junction (mk_config c_fs c_lo c_tenv) D P (Nenv.add i (flatten_typ c_lo c_tenv t) G) bs l' l0); intros.
  eapply tc_junction_correct in H; eauto. econstructor; eauto.
Qed.

(* ---------------------------------------------------------------------- *)
Fixpoint tc_insns_ndterm (C:config) (D:Delta) (P:Psi) (bs:blocks) (l:lab) (insns:list insn) (ndterm:insn_nd_term) (G:Gamma) : bool :=
  match insns with
    | nil => match ndterm with
               | Insn_nd nd => tc_nd C D P G bs nd l
               | Insn_term term => tc_term C D P G bs l term
             end
    | i::insns =>
      match tc_insn C D P i G with
        | Some G2 => tc_insns_ndterm C D P bs l insns ndterm G2
        | None => false
      end
  end.

Lemma tc_insns_ndterm_correct : forall C D P bs l insns ndterm G,
  tc_insns_ndterm C D P bs l insns ndterm G = true ->
  wf_insns_ndterm C D P bs l insns ndterm G.
Proof.
  induction insns; simpl; intros.
  destruct ndterm.
  eapply tc_nd_correct in H; eauto.
  eapply tc_term_correct in H; eauto.
  remember (tc_insn C D P a G) as Hd. destruct Hd; try congruence.
  symmetry in HeqHd. eapply tc_insn_correct in HeqHd; eauto.
Qed.

(* ---------------------------------------------------------------------- *)
Fixpoint tc_fbody1' (P:list (PTRTYP*Gamma)) (f:function) : bool :=
  match P with
    | nil => true
    | (l,G)::P' => match lookup_blk l (f_body f) with
                      | Some b => tc_fbody1' P' f
                      | None => false
                    end
  end.

Lemma tc_fbody1_correct' : forall ls f,
  SetoidList.NoDupA (Ienv.eq_key (elt:=Gamma)) ls ->
  tc_fbody1' ls f = true ->
  (forall l G, SetoidList.InA (Ienv.eq_key_elt (elt:=Gamma)) (l,G) ls -> 
    exists b, lookup_blk l (f_body f) = Some b).
Proof.
  induction ls; simpl; intros. rewrite SetoidList.InA_nil in H1. contradiction.
  destruct a. remember (lookup_blk k (f_body f)) as Hd.
  destruct Hd; try congruence. symmetry in HeqHd.
  inv H. inv H1. inv H2. simpl in H. simpl in H1. subst. 
  specialize (Word.eq_spec _ l k); intros. rewrite H in H1. subst. eauto.
  eapply IHls in H0; eauto.
Qed.
  
Definition tc_fbody1 (P:Psi) (f:function) : bool :=
  tc_fbody1' (Ienv.elements P) f.

Lemma tc_fbody1_correct : forall P f,
  tc_fbody1 P f = true ->
  (forall l G, Ienv.find l P = Some G -> 
    exists b, lookup_blk l (f_body f) = Some b).
Proof.
  unfold tc_fbody1; intros.
  specialize (Ienv.elements_3w P); intros.
  specialize (tc_fbody1_correct' (Ienv.elements P) f H1 H); intros.
  eapply H2 with G.
  rewrite <- IFacts.elements_mapsto_iff.
  rewrite IFacts.find_mapsto_iff; auto.
Qed.

(* ---------------------------------------------------------------------- *)
Fixpoint tc_fbody2 (P:Psi) (bs:blocks) : bool :=
  match bs with
    | nil => true
    | b::bs' => match Ienv.find (b_lab b) P with
                  | Some G => tc_fbody2 P bs'
                  | None => false
                end
  end.

Lemma tc_fbody2_correct : forall P bs,
  tc_fbody2 P bs = true ->
  (forall l b, lookup_blk l bs = Some b -> 
    exists G, Ienv.find l P = Some G).
Proof.
  induction bs; crush.
  destruct lab_dec; crush.
  remember (Ienv.find (b_lab b) P) as Hd. destruct Hd; crush. eauto.
  remember (Ienv.find (b_lab a) P) as Hd. destruct Hd; crush. eauto.
Qed.

(* ---------------------------------------------------------------------- *)

Definition tc_fbody_body (C:config) (D1 D2:Delta) (P:Psi) (f:function) (l:lab) (G:Gamma) :=
  match lookup_blk l (f_body f) with
    | Some b =>
      if tc_insns_ndterm C D2 P (f_body f) (b_lab b) (b_insns b) (b_nd_term b) G then
        match b_nd_term b with
          | Insn_term (Insn_return t x) =>
            match f_ret f with
              | Some t' =>
                if typ_eq_dec t t' then
                  if tc_ftyps (c_tenv C) D1 (flatten_typ (c_lo C) (c_tenv C) t) then
                    true else false else false
              | _ => false
            end
          | Insn_term Insn_return_void =>
            match f_ret f with
              | None => true
              | _ => false
            end
          | _ => true
        end
        else false
    | _ => false
  end.

Lemma tc_fbody_body_correct : forall C D1 D2 P f l G,
  tc_fbody_body C D1 D2 P f l G = true ->
  (exists b, 
    lookup_blk l (f_body f) = Some b /\
    wf_insns_ndterm C D2 P (f_body f) (b_lab b) (b_insns b) (b_nd_term b) G /\
    (match b_nd_term b with
       | Insn_term (Insn_return t x) => (f_ret f) = Some t /\ wf_ftyps (c_tenv C) D1 (flatten_typ (c_lo C) (c_tenv C) t)
       | Insn_term Insn_return_void => f_ret f = None
       | _ => True
     end)).
Proof.
  unfold tc_fbody_body; simpl; intros.
  remember (lookup_blk l (f_body f)) as Hd. destruct Hd; try congruence.
  remember (tc_insns_ndterm C D2 P (f_body f) (b_lab b) (b_insns b) (b_nd_term b) G) as Hd2.
  destruct Hd2; try congruence.
  symmetry in HeqHd. symmetry in HeqHd2.
  remember (b_nd_term b) as Hd3. destruct Hd3; try congruence.
  eapply tc_insns_ndterm_correct in HeqHd2; eauto. exists b. split; eauto.
  rewrite HeqHd3 in HeqHd2. split; eauto.
  destruct (b_nd_term b); crush. 
  exists b. split; eauto. rewrite HeqHd3 in HeqHd2.
  eapply tc_insns_ndterm_correct in HeqHd2; eauto.
  split; eauto. destruct (b_nd_term b); crush.
  destruct t0; crush.
  remember (f_ret f) as Hd3. destruct Hd3; try congruence.
  destruct typ_eq_dec; crush.
  remember (f_ret f) as Hd3. destruct Hd3; try congruence.
  destruct typ_eq_dec; crush.
  remember (tc_ftyps (c_tenv C) D1 (flatten_typ (c_lo C) (c_tenv C) t0)) as Hd4.
  destruct Hd4; try congruence. symmetry in HeqHd4.
  eapply tc_ftyps_correct; eauto.
  destruct (f_ret f); crush.
Qed.

Lemma find_empty_iff : forall T (m : Ienv.t T),
  Ienv.Empty m <-> forall k, Ienv.find k m = None.
Proof.
  unfold Ienv.Empty. intros. split.
  { intros; case_eq (Ienv.find k m); auto; intros.
    exfalso. eapply IFacts.find_mapsto_iff in H0. eapply H; eauto. }
  { intro. unfold Ienv.Raw.Proofs.Empty. intros.
    specialize (H a). unfold not. intros. 
    assert (Ienv.MapsTo a e m). crush.
    rewrite IFacts.find_mapsto_iff in H1. congruence. }
Qed.

Definition tc_fbody3'' (C:config) (D1 D2:Delta) (P:Psi) (f:function) : bool :=
  Ienv.fold (fun l G b => if tc_fbody_body C D1 D2 P f l G then b else false) P true.

Definition b2p (b1 b2 : bool) : Prop :=
  match b1, b2 with
    | true, true => True
    | false, false => True
    | _, _ => False
  end.

Lemma tc_fbody3_correct : forall P C D1 D2 f acc P',
  Ienv.fold (fun l G b => if tc_fbody_body C D1 D2 P' f l G then b else false) P acc = true ->
  (forall l G, Ienv.find l P = Some G ->
    (exists b, 
      lookup_blk l (f_body f) = Some b /\
      wf_insns_ndterm C D2 P' (f_body f) (b_lab b) (b_insns b) (b_nd_term b) G /\
      (match b_nd_term b with
         | Insn_term (Insn_return t x) => (f_ret f) = Some t /\ wf_ftyps (c_tenv C) D1 (flatten_typ (c_lo C) (c_tenv C) t)
         | Insn_term Insn_return_void => f_ret f = None
         | _ => True
       end))).
Proof.
  intros. generalize dependent H0. generalize dependent G. 
  generalize dependent l. generalize dependent H.
  eapply (IProp.map_induction) with (m := P); eauto; intros.
  erewrite find_empty_iff in H; try congruence.
  t_dup H1.
  eapply IProp.fold_Add with (elt := Gamma) (A := bool) (eqA := b2p) 
    (f := (fun (l : Ienv.key) (G : Gamma) (b : bool) =>
         if tc_fbody_body C D1 D2 P' f l G then b else false)) (i := acc) in H1; eauto.
  unfold b2p in H1. rewrite H2 in H1. simpl in H1.
  remember (tc_fbody_body C D1 D2 P' f x e) as Hd.
  destruct Hd; try contradiction. 
  symmetry in HeqHd. eapply tc_fbody_body_correct in HeqHd; eauto.
  unfold IProp.Add in H'. specialize (H' l). rewrite H' in H3.
  destruct (Word.eq_dec x l); subst. 
  rewrite IFacts.add_eq_o in H3; auto. inv H3. eauto.
  apply Word.int_eq_refl.
  rewrite IFacts.add_neq_o in H3; auto. 
  remember (Ienv.fold
            (fun (l : Ienv.key) (G : Gamma) (b : bool) =>
             if tc_fbody_body C D1 D2 P' f l G then b else false) m acc) as Hd2.
  destruct Hd2; try contradiction. eauto.

  apply Word.int_eq_false_iff2 in n. crush.

  constructor. unfold RelationClasses.Reflexive. intros. destruct x0; crush.
  unfold RelationClasses.Symmetric. intros. destruct x0; destruct y; crush.
  unfold RelationClasses.Transitive. intros. destruct x0; destruct y; destruct z; crush.

  unfold Morphisms.Proper. unfold Morphisms.respectful. intros. subst.
  apply Word.int_eq_true_iff2 in H4. subst.
  destruct (tc_fbody_body C D1 D2 P' f y y0); crush.

  unfold IProp.transpose_neqkey; intros.
  unfold b2p. 
  destruct (tc_fbody_body C D1 D2 P' f k e0); crush. 
  destruct (tc_fbody_body C D1 D2 P' f k' e'); crush.
  destruct a; crush.
  destruct (tc_fbody_body C D1 D2 P' f k' e'); crush.
Qed.

(* ---------------------------------------------------------------------- *)
Definition tc_fbody (C:config) (D1 D2:Delta) (P:Psi) (f:function) : bool :=
  if tc_fbody1 P f then
    if tc_fbody2 P (f_body f) then
      if tc_fbody3'' C D1 D2 P f then
        true else false else false else false.

Lemma tc_fbody_correct : forall C D1 D2 P f,
  tc_fbody C D1 D2 P f = true ->
  wf_fbody C D1 D2 P f.
Proof.
  unfold tc_fbody; intros.
  remember (tc_fbody1 P f) as Hd. destruct Hd; try congruence.
  remember (tc_fbody2 P (f_body f)) as Hd2. destruct Hd2; try congruence.
  remember (tc_fbody3'' C D1 D2 P f) as Hd3. destruct Hd3; try congruence.
  symmetry in HeqHd. symmetry in HeqHd2. symmetry in HeqHd3.
  unfold wf_fbody. repeat split; intros.
  eapply tc_fbody1_correct in HeqHd; eauto.
  eapply tc_fbody2_correct in HeqHd2; eauto.
  unfold tc_fbody3'' in HeqHd3.
  eapply tc_fbody3_correct in HeqHd3; eauto.
Qed.

(* ---------------------------------------------------------------------- *)
Fixpoint tc_fparams (C:config) (D:Delta) (xs:list id) (ts:list typ) : option Gamma :=
  match xs, ts with
    | nil, nil => Some (Nenv.empty ftyps) 
    | x::xs, t::ts =>
      match tc_fparams C D xs ts with
        | Some G =>
          let t' := flatten_typ (c_lo C) (c_tenv C) t in
            if tc_ftyps (c_tenv C) D t' then
              Some (Nenv.add x t' G)
              else None
        | None => None
      end
    | _, _ => None
  end.

Lemma tc_fparams_correct : forall C D xs ts G,
  tc_fparams C D xs ts = Some G ->
  wf_fparams C D xs ts G.
Proof.
  induction xs; destruct ts; crush.
  remember (tc_fparams C D xs ts) as Hd. destruct Hd; try congruence.
  remember (tc_ftyps (c_tenv C) D (flatten_typ (c_lo C) (c_tenv C) t)) as Hd2. destruct Hd2; try congruence.
  symmetry in HeqHd. symmetry in HeqHd2. inv H.
  eapply tc_ftyps_correct in HeqHd2; eauto. 
  econstructor; eauto. crush.
Qed.

(* ---------------------------------------------------------------------- *)
Fixpoint tc_prgns (lr:list (rgn*typ)) : option Delta :=
  match lr with
    | nil => Some (Nenv.empty typ)
    | (r,t)::lr' => match tc_prgns lr' with
                      | Some D => Some (Nenv.add r t D)
                      | None => None
                    end
  end.

Lemma tc_prgns_correct : forall lr D,
  tc_prgns lr = Some D ->
  wf_prgns lr D.
Proof.
  induction lr; crush.
  remember (tc_prgns lr) as Hd. destruct Hd; try congruence.
  inv H. econstructor; eauto. crush.
Qed.

(* ---------------------------------------------------------------------- *)
Fixpoint tc_lrgns (C:config) (lrgn:list (rgn*typ)) (D:Delta) : option Delta :=
  match lrgn with
    | nil => Some D
    | (r,t)::lrgn' =>
      match tc_lrgns C lrgn' D with
        | Some D2 => match Nenv.find r D2 with
                       | None => Some (Nenv.add r t D2)
                       | _ => None
                     end
        | _ => None
      end
  end.

Lemma tc_lrgns_correct : forall C lrgn D1 D2,
  tc_lrgns C lrgn D1 = Some D2 ->
  wf_lrgns C lrgn D1 D2.
Proof.
  induction lrgn; crush.
  remember (tc_lrgns C lrgn D1) as Hd. destruct Hd; try congruence.
  tc_simpl. eauto.
Qed.

(* ---------------------------------------------------------------------- *)
Lemma extends_gamma_iff_equiv2 : forall {A:Type} (G1 G2:Nenv.t A),
  extends_gamma2 G1 G2 ->
  extends_gamma2 G2 G1 ->
  Nenv.Equal G1 G2.
Proof.
  unfold extends_gamma2; crush.
  unfold Nenv.Equal; crush.
  case_eq (Nenv.find y G1); intros.
  apply H in H1; auto.
  case_eq (Nenv.find y G2); intros.
  apply H0 in H2; crush.
  reflexivity.
Qed.

Lemma tc_wf_ftyps_ls2 : forall tenv D lr b lo,
  fold_left (fun a b => a && tc_ftyps tenv D (flatten_typ lo tenv b)) lr b = true ->
  b = true.
Proof.
  induction lr; intros; eauto. simpl in H.
  eapply IHlr in H. rewrite andb_true_iff in H. crush.
Qed.
  
Lemma tc_wf_ftyps_ls : forall tenv D lr lo,
  fold_left (fun a b => a && tc_ftyps tenv D (flatten_typ lo tenv b)) lr true = true ->
  Forall (fun t => wf_ftyps tenv D (flatten_typ lo tenv t)) lr.
Proof.
  induction lr; intros; econstructor; eauto. simpl in H. 
  assert (tc_ftyps tenv D (flatten_typ lo tenv a) = true). eapply tc_wf_ftyps_ls2; eauto.
  eapply tc_ftyps_correct; eauto.
  simpl in H.
  assert (tc_ftyps tenv D (flatten_typ lo tenv a) = true). eapply tc_wf_ftyps_ls2; eauto.
  rewrite H0 in H. eauto.
Qed.

Definition tc_function (C:config) (D1 D2:Delta) (P:Psi) (f:function) : bool :=
  match Ienv.find (f_lab f) P with
    | Some G =>
      match tc_fparams C D1 (f_params f) (f_sig f) with
        | Some G' =>
          if andb (tc_extends_gamma ftyps_eq_dec G G') (tc_extends_gamma ftyps_eq_dec G' G) then
            if list_disjoint_dec rgn_dec (domain (f_lrgn f)) (domain (f_prgn f)) then
              if list_norepet_dec rgn_dec (domain (f_prgn f)) then
                if list_norepet_dec rgn_dec (domain (f_lrgn f)) then
                  match tc_prgns (f_prgn f) with
                    | Some D1' =>
                      if andb (tc_extends_gamma typ_eq_dec D1 D1') (tc_extends_gamma typ_eq_dec D1' D1) then
                      match tc_lrgns C (f_lrgn f) D1' with
                        | Some D2' =>
                          if andb (tc_extends_gamma typ_eq_dec D2 D2') (tc_extends_gamma typ_eq_dec D2' D2) then
                          if tc_fbody C D1 D2 P f then
                            if fold_left (fun a b => a && tc_ftyps (c_tenv C) D2 (flatten_typ (c_lo C) (c_tenv C) b)) (range (f_lrgn f)) true then
                            true else false else false else false
                        | _ => false
                      end else false
                    | _ => false
                  end
                  else false else false else false else false
        | _ => false
      end
    | _ => false
  end.

Ltac tc_fun_simpl :=
  repeat
  match goal with
    | [ H1: extends_gamma2 ?G1 ?G2,
        H2: extends_gamma2 ?G2 ?G1 |- _ ] => 
      specialize (extends_gamma_iff_equiv2 G1 G2 H1 H2); intros; clear H1; clear H2
    | [ H: tc_extends_gamma ?f ?G1 ?G2 = true |- _ ] =>
      apply tc_extends_gamma_correct2 in H
    | [ H: andb (tc_extends_gamma ?f ?G ?G') (tc_extends_gamma ?f ?G' ?G) = true |- _ ] =>
      rewrite H in *; simpl in *; rewrite andb_true_iff in H; destruct H
    | [ H: andb (tc_extends_gamma ?f ?G ?G') (tc_extends_gamma ?f ?G' ?G) = false |- _ ] =>
      rewrite H in *; try congruence
    | [ H: context [ andb (tc_extends_gamma ?f ?G ?G') (tc_extends_gamma ?f ?G' ?G) ] |- _ ] =>
      case_eq (andb (tc_extends_gamma f G G') (tc_extends_gamma f G' G)); intros
    | [ H: context [ list_disjoint_dec ] |- _ ] =>
      destruct list_disjoint_dec; try congruence; subst
    | [ H: context [ list_norepet_dec ] |- _ ] =>
      destruct list_norepet_dec; try congruence; subst
  end.

Lemma tc_function_correct : forall C D1 D2 P f,
  tc_function C D1 D2 P f = true ->
  wf_function C D1 D2 P f.
Proof.
  unfold tc_function; intros.
  remember (Ienv.find (elt:=Nenv.t ftyps) (f_lab f) P) as Hd.
  destruct Hd; try congruence.
  remember (tc_fparams C D1 (f_params f) (f_sig f)) as Hd2.
  destruct Hd2; try congruence.
  tc_fun_simpl.
  remember (tc_prgns (f_prgn f)) as Hd3. destruct Hd3; try congruence.
  tc_fun_simpl.
  remember (tc_lrgns C (f_lrgn f) d) as Hd4. destruct Hd4; try congruence.
  tc_fun_simpl.
  remember (tc_fbody C D1 D2 P f) as Hd5. destruct Hd5; try congruence.
  remember (fold_left
    (fun (a : bool) (b : typ) =>
      a && tc_ftyps (c_tenv C) D2 (flatten_typ (c_lo C) (c_tenv C) b))
    (range (f_lrgn f)) true) as Hd6. destruct Hd6; try congruence.
  symmetry in HeqHd. symmetry in HeqHd2. symmetry in HeqHd3. symmetry in HeqHd4.
  symmetry in HeqHd5. symmetry in HeqHd6.
  econstructor; eauto. split; eauto. 
  exists g. exists d. exists d0.
  eapply tc_fbody_correct in HeqHd5.
  repeat (split; eauto).
  eapply tc_fparams_correct in HeqHd2; eauto.
  eapply tc_prgns_correct; eauto.
  eapply tc_lrgns_correct; eauto.
  eapply tc_wf_ftyps_ls in HeqHd6; eauto.
Qed.

(* ---------------------------------------------------------------------- *)
Definition wf_functions_weak (fs:functions) (C:config) (FT:Ienv.t Psi) (FD:Ienv.t (Delta*Delta)): Prop :=
  (forall l f, lookup_fun l fs = Some f ->
    exists D1, exists D2, Ienv.find (f_lab f) FD = Some (D1,D2) /\
      exists P, Ienv.find (f_lab f) FT = Some P /\
        wf_function C D1 D2 P f).

Fixpoint tc_functions' (fs:functions) (C:config) (FT:Ienv.t Psi) (FD:Ienv.t (Delta*Delta)) : bool :=
  match fs with
    | nil => true
    | f::fs' =>
      if tc_functions' fs' C FT FD then
        match Ienv.find (f_lab f) FD, Ienv.find (f_lab f) FT with
          | Some (D1, D2), Some P =>
            tc_function C D1 D2 P f
          | _, _ => false
        end
        else false
  end.

Lemma tc_functions_correct' : forall fs C FT FD,
  list_norepet (map (fun f => f_lab f) fs) ->
  tc_functions' fs C FT FD = true ->
  wf_functions_weak fs C FT FD.
Proof.
  induction fs; crush. econstructor; eauto. unfold lookup_fun in H1. inv H1.
  remember (tc_functions' fs C FT FD) as Hd. destruct Hd; try congruence.
  remember (Ienv.find (elt:=Delta * Delta) (f_lab a) FD) as Hd3. destruct Hd3; try congruence.
  destruct p.
  remember (Ienv.find (elt:=Psi) (f_lab a) FT) as Hd4. destruct Hd4; try congruence.
  symmetry in HeqHd. (* symmetry in HeqHd2. *) symmetry in HeqHd3. symmetry in HeqHd4.
  eapply tc_function_correct in H0; eauto.
  unfold wf_functions_weak; intros.
  inv H. simpl in H1. destruct lab_dec; subst. inv H1. eauto 10.
  eapply IHfs; eauto.

  Grab Existential Variables.
  apply (Nenv.empty typ).
Qed.

Definition tc_functions (C:config) (FT:Ienv.t Psi) (FD:Ienv.t (Delta*Delta)) : bool :=
  if list_norepet_dec lab_dec (map (fun f => f_lab f) (c_fs C)) then
    tc_functions' (c_fs C) C FT FD else false.

Lemma tc_functions_correct : forall C FT FD,
  tc_functions C FT FD = true ->
  wf_functions C FT FD.
Proof.
  unfold tc_functions; intros.
  destruct list_norepet_dec; crush.
  eapply tc_functions_correct' in H; eauto.
  unfold wf_functions_weak in H; eauto.
  unfold wf_functions; eauto.
Qed.

(* ---------------------------------------------------------------------- *)
Module NProp := FMapFacts.WProperties_fun(Nat_as_OT)(Nenv).

Lemma find_empty_iff2 : forall T (m : Nenv.t T),
  Nenv.Empty m <-> forall k, Nenv.find k m = None.
Proof.
  unfold Nenv.Empty. intros. split.
  { intros; case_eq (Nenv.find k m); auto; intros.
    exfalso. eapply NFacts.find_mapsto_iff in H0. eapply H; eauto. }
  { intro. unfold Nenv.Raw.Proofs.Empty. intros.
    specialize (H a). unfold not. intros. 
    assert (Nenv.MapsTo a e m). crush.
    rewrite NFacts.find_mapsto_iff in H1. congruence. }
Qed.

(* ---------------------------------------------------------------------- *)
Definition tc_tenv (tenv:tenv_t) : bool := 
  Nenv.fold (fun x p b => 
    match p with
      | (t, lr, _) => 
        if tc_tenv_ftyps lr t then
          if ftyps_eq_dec t nil then false 
            else b else false
    end) tenv true.

Lemma tc_tenv_correct' : forall tenv acc,
  Nenv.fold (fun x p b => 
    match p with
      | (t, lr, _) => if tc_tenv_ftyps lr t then
          if ftyps_eq_dec t nil then false 
            else b else false
    end) tenv acc = true ->
  wf_tenv tenv.
Proof.
  intro.
  eapply NProp.map_induction with (m := tenv); eauto; intros.
  unfold wf_tenv; intros. rewrite find_empty_iff2 in H.
  congruence.
  t_dup H1.
  eapply NProp.fold_Add with (elt := (ftyps * list rgn * bool)%type) (A := bool) (eqA := b2p) 
    (f := (fun (_ : Nenv.key) (p : ftyps * list rgn * bool) (b : bool) =>
         let (y, _) := p in
         let (t, lr) := y in if tc_tenv_ftyps lr t then
          if ftyps_eq_dec t nil then false 
            else b else false)) (i := acc) in H1; eauto.
  destruct e. rewrite H2 in H1. destruct p.
  remember (tc_tenv_ftyps l f) as Hd. destruct Hd; try contradiction.
  symmetry in HeqHd. eapply tc_tenv_ftyps_correct in HeqHd; eauto.
  destruct_c ftyps_eq_dec.
  simpl in H1. contradiction.
  remember (Nenv.fold
            (fun (_ : Nenv.key) (p : ftyps * list rgn * bool) (b : bool) =>
             let (y, _) := p in
             let (t, lr) := y in if tc_tenv_ftyps lr t then
          if ftyps_eq_dec t nil then false
            else b else false) m
            acc) as Hd2. destruct Hd2; try contradiction.
  symmetry in HeqHd2. 
  unfold wf_tenv; intros. unfold NProp.Add in H'. rewrite H' in H3.
  destruct (eq_nat_dec x0 x); subst. 
  rewrite NFacts.add_eq_o in H3; eauto. inv H3. split; auto.
  rewrite NFacts.add_neq_o in H3; eauto. 
  specialize (H acc). rewrite HeqHd2 in H. 
  assert (true = true). reflexivity. apply H in H4. unfold wf_tenv in H4.
  eapply H4 in H3; eauto. 

  constructor. unfold RelationClasses.Reflexive. intros. destruct x0; crush.
  unfold RelationClasses.Symmetric. intros. destruct x0; destruct y; crush.
  unfold RelationClasses.Transitive. intros. destruct x0; destruct y; destruct z; crush.
   
  unfold Morphisms.Proper. unfold Morphisms.respectful. intros. subst.
  destruct y0. destruct p.
  destruct (tc_tenv_ftyps l f); crush.
  destruct_c ftyps_eq_dec.
  unfold b2p. auto.

  unfold NProp.transpose_neqkey; intros.
  unfold b2p. destruct e0. destruct e'. destruct p. destruct p0.
  destruct_c (tc_tenv_ftyps l f); auto. 
  destruct_c ftyps_eq_dec; auto.
  destruct_c tc_tenv_ftyps; auto.
  destruct_c ftyps_eq_dec; auto.
  destruct_c tc_tenv_ftyps; auto.
  destruct_c ftyps_eq_dec; auto.
  destruct_c a; auto.
  destruct_c tc_tenv_ftyps; auto.
  destruct_c ftyps_eq_dec; auto.
Qed.

Lemma tc_tenv_correct : forall tenv,
  tc_tenv tenv = true ->
  wf_tenv tenv.
Proof.
  intros. unfold tc_tenv in H. eapply tc_tenv_correct' in H; eauto.
Qed.
