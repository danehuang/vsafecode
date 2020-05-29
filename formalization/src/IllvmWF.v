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
Import SVAmem.

(* ---------------------------------------------------------------------- *)
(** * Machine Invariants *)

(* Well-formed environment context
 * C; live; HT; rmap |- env : G *)
Definition wf_env (C:config) (live:list rgn) (HT:heap_t) (rmap:Nenv.t rgn) (env:Nenv.t rt_val) (G:Gamma) : Prop :=
  forall x t,
    Nenv.find x G = Some t ->
    exists v, Nenv.find x env = Some v /\ 
      wf_value (c_fs C) (c_lo C) (c_tenv C) live HT v (sigma rmap t).

(* Well-formed region-map 
 * All regions in D are mapped in rmap and are currently live
 * D; live |- rmap *)
Definition wf_rmap (D:Delta) (live:list rgn) (rmap:Nenv.t rgn) : Prop :=
  forall r t,
    Nenv.find r D = Some t ->
    exists r', Nenv.find r rmap = Some r' /\ In r' live.

(* rmap1 subset of rmap2 *)
Definition rmap_subset (rmap1 rmap2:Nenv.t rgn) : Prop :=
  forall r r',
    Nenv.find r rmap1 = Some r' ->
    Nenv.find r rmap2 = Some r'.

(* rmap1 subset of rmap2 under substitution rmap3 *)
Definition rmap_subset2 (rmap1 rmap2:Nenv.t rgn) (rmap3:Nenv.t rgn) : Prop :=
  forall r r',
    Nenv.find r rmap1 = Some r' ->
    Nenv.find (alpha rmap3 r) rmap2 = Some r'.

(* Well-formed execution context 
 * C; D; G |- ec *)
Definition wf_ec (C:config) (D:Delta) (ec:exec_ctxt) (G:Gamma) : Prop :=
  exists f, exists b,
    f = (ec_fun ec) /\
    b = (ec_blk ec) /\
    lookup_fun (f_lab f) (c_fs C) = Some f /\
    lookup_blk (b_lab b) (f_body f) = Some b /\
    match ec_term ec with
      | Insn_term (Insn_br_uncond l) => True
      | _ => ec_term ec = b_nd_term b 
    end /\ 
    wf_env C (ec_live ec) (ec_HT ec) (ec_rmap_b ec) (ec_env ec) G /\
    wf_HT_live (ec_live ec) (ec_HT ec) /\
    wf_HT (c_lo C) (ec_HT ec) /\
    wf_HT_bounds (ec_HT ec) /\
    wf_rmap D (ec_live ec) (ec_rmap_b ec) /\
    rmap_subset (ec_rmap_e ec) (ec_rmap_b ec) /\
    list_norepet (ec_rgns ec) /\
    exists ls, b_insns b = ls ++ (ec_insns ec).

(* Well-formed call stack
 * Under a config, code, region (local and polymorphic for bottom), precondition 
 * and typ context, 2 adjacent contexts are well-formed
 * C; D_p; D_l; P; G |- <ECtop, ECbot> *)
Inductive wf_call : config -> Delta -> Delta -> Psi -> Gamma -> exec_ctxt -> 
  exec_ctxt -> Prop :=
| wf_call_return : forall fs lo tenv Dbot Dtop ecbot ectop x t t' t'' o prgns args l P G,
  ec_insns ecbot = nil ->
  f_ret (ec_fun ectop) = Some t ->
  t' = sigma (inst_prgn (domain (f_prgn (ec_fun ectop))) prgns) (flatten_typ lo tenv t) ->
  wf_term (mk_config fs lo tenv) Dbot P (Nenv.add x (flatten_typ lo tenv t'') G) (f_body (ec_fun ecbot)) (b_lab (ec_blk ecbot)) (Insn_br_uncond l) ->
  (* wf_term (mk_config fs lo tenv) Dbot P (Nenv.add x t' G) (f_body (ec_fun ecbot)) (b_lab (ec_blk ecbot)) (Insn_br_uncond l) -> *)
  ftyps_weaken t' (flatten_typ lo tenv t'') = true ->
  ec_term ecbot = Insn_nd (Insn_call (Some x) (Some t'') o prgns args l) ->
  (* ec_term ecbot = Insn_nd (Insn_call (Some x) (Some (sigma'' (inst_prgn (domain (f_prgn (ec_fun ectop))) prgns) t)) o prgns args l) -> *)
  rmap_subset2 (ec_rmap_e ectop) (ec_rmap_b ecbot) (inst_prgn (domain (f_prgn (ec_fun ectop))) prgns) ->
  match ec_term ectop with
    | Insn_term (Insn_return _ _) => True
    | Insn_term Insn_return_void => False
    | _ => True
  end ->
  wf_call (mk_config fs lo tenv) Dtop Dbot P G ectop ecbot
| wf_call_return_void : forall fs lo tenv Dbot Dtop ecbot ectop o prgns args l P G,
  ec_insns ecbot = nil ->
  f_ret (ec_fun ectop) = None ->
  wf_term (mk_config fs lo tenv) Dbot P G (f_body (ec_fun ecbot)) (b_lab (ec_blk ecbot)) (Insn_br_uncond l) ->
  ec_term ecbot = Insn_nd (Insn_call None None o prgns args l) ->
  match ec_term ectop with
    | Insn_term (Insn_return_void) => True
    | Insn_term (Insn_return _ _) => False
    | _ => True
  end ->
  wf_call (mk_config fs lo tenv) Dtop Dbot P G ectop ecbot.
Hint Constructors wf_call.

(* Well-formed execution stack
 * Under a config, code context mapping, stack of region contexts, and stack of 
 * typ contexts, a stack of execution contexts is well-formed
 * C; FD; FT; (G::stkG); (D:stkD) |- (ec::stkEC) *)
Inductive wf_ec_stk : config -> Ienv.t (Delta*Delta) -> Ienv.t Psi -> exec_ctxt -> (Delta*Delta) -> Gamma -> list exec_ctxt -> list (Delta*Delta) -> list Gamma -> Prop :=
| wf_ec_stk_nil : forall C FD FT ectop G D1 D2,
  wf_ec C D2 ectop G ->
  wf_ec_stk C FD FT ectop (D1,D2) G nil nil nil
(* Check that adjacent stack frames are well-formed *)
| wf_ec_stk_cons : forall C FD FT P ectop ecbot ecs Gtop Gbot lsG Dbot1 Dbot2 Dtop1 Dtop2 lsD,
  wf_ec C Dtop2 ectop Gtop ->
  list_disjoint (ec_rgns ectop) (ec_live ecbot) ->
  (ec_live ectop) = (ec_rgns ectop) ++ (ec_live ecbot) ->
  wf_rmap Dtop1 (ec_live ecbot) (ec_rmap_e ectop) ->
  heapt_ext (ec_HT ecbot) (ec_HT ectop) ->
  heapt_ext2 (ec_live ecbot) (ec_HT ecbot) (ec_HT ectop) ->
  max_HT (ec_HT ecbot) <= max_HT (ec_HT ectop) ->
  Ienv.find (f_lab (ec_fun ecbot)) FT = Some P ->
  Ienv.find (f_lab (ec_fun ecbot)) FD = Some (Dbot1, Dbot2) ->
  wf_call C Dbot1 Dbot2 P Gbot ectop ecbot ->
  wf_ec_stk C FD FT ecbot (Dbot1, Dbot2) Gbot ecs lsD lsG ->
  wf_ec_stk C FD FT ectop (Dtop1, Dtop2) Gtop (ecbot::ecs) ((Dbot1, Dbot2)::lsD) (Gbot::lsG).
Hint Constructors wf_ec_stk.

(* Well-formed machine state
 * The top-level invariant
 * |- <C, (m, ec, stkEC)> *)
Inductive wf_ms : config -> mstate -> Prop :=
| wf_ms_intro : forall fs lo tenv P FT G lsG f b insns term env m stk D1 D2 HT rmap_e rmap_b rgns live lsD FD,
  Ienv.find (f_lab f) FT = Some P ->
  Ienv.find (f_lab f) FD = Some (D1, D2) ->
  wf_insns_ndterm (mk_config fs lo tenv) D2 P (f_body f) (b_lab b) insns term G ->
  wf_functions (mk_config fs lo tenv) FT FD ->
  wf_ec_stk (mk_config fs lo tenv) FD FT (mk_ec f b insns term env HT rmap_e rmap_b rgns live) (D1,D2) G stk lsD lsG ->
  wf_mem fs lo tenv live HT m ->
  wf_mem_metadata HT m ->
  wf_tenv tenv ->
  wf_ms (mk_config fs lo tenv) (mk_mstate m (mk_ec f b insns term env HT rmap_e rmap_b rgns live) stk).
Hint Constructors wf_ms.

(* Well-formed computation *)
Inductive wf_comp : config -> comp -> Prop :=
| wf_comp_ret : forall C,
  wf_comp C Ret
| wf_comp_delay : forall C ms,
  wf_ms C ms ->
  wf_comp C (Delay ms).
Hint Constructors wf_comp.

(* ---------------------------------------------------------------------- *)
(** * Canonical Form Lemmas *)

Lemma canonical_form_float : forall fs lo tenv live HT rmap v,
  wf_value fs lo tenv live HT v (sigma rmap (Ftyp_float :: nil)) ->
  exists f, v = RT_float f :: nil.
Proof.
  unfold sigma; simpl; intros. inv H. inv H5. inv H6. eauto.
Qed.

Lemma canonical_form_double : forall fs lo tenv live HT rmap v,
  wf_value fs lo tenv live HT v (sigma rmap (Ftyp_double :: nil)) ->
  exists f, v = RT_double f :: nil.
Proof.
  unfold sigma; simpl; intros. inv H. inv H5. inv H6. eauto.
Qed.

Lemma canonical_form_int : forall fs lo tenv live HT rmap v sz pf,
  wf_value fs lo tenv live HT v (sigma rmap (Ftyp_int sz pf :: nil)) ->
  exists i, v = RT_int sz pf i :: nil.
Proof.
  unfold sigma; simpl; intros. inv H. inv H5. inv H6. 
  exists i0. f_equal. f_equal. apply proof_irr.
Qed.

Lemma canonical_form_ptr : forall fs lo tenv live HT rmap v t r,
  wf_value fs lo tenv live HT v (sigma rmap (Ftyp_ptr t r :: nil)) ->
  exists addr, 
    v = RT_ptr addr :: nil /\
    check_HT lo HT (Word.unsigned addr) (alpha rmap r) (flatten_typ lo tenv (sigma'' rmap t)) = true.
Proof.
  unfold sigma; simpl; intros. inv H. inv H5. inv H6. eauto.
Qed.

Lemma canonical_form_ptrU : forall fs lo tenv live HT rmap v sz r,
  wf_value fs lo tenv live HT v (sigma rmap (Ftyp_ptrU sz r :: nil)) ->
  exists addr, 
    v = RT_ptr addr :: nil /\
    check_HT lo HT (Word.unsigned addr) (alpha rmap r) (list_repeat sz Ftyp_int8) = true.
Proof.
  unfold sigma; simpl; intros. inv H. inv H5. inv H6. eauto.
Qed.

Lemma canonical_form_fun : forall fs lo tenv live HT rmap v prgns sig ret,
  wf_value fs lo tenv live HT v (sigma rmap (Ftyp_fun prgns sig ret :: nil)) ->
  v = RT_fun Word.zero :: nil \/
  (exists l, exists f,
    v = RT_fun l :: nil /\
    lookup_fun l fs = Some f /\
    domain (f_prgn f) = prgns /\
    f_sig f = sig /\
    f_ret f = ret).
Proof.
  unfold sigma; simpl; intros. inv H. inv H5. inv H6. unfold check_fun in H3. 
  repeat match goal with
           | [ H: context [ if ?x then _ else _ ] |- _ ] =>
             (consider x); intros; subst; eauto 20
           | [ H: context [ match ?x with | Some _ => _ | None => _ end ] |- _ ] =>
             (consider x); intros; subst; eauto 20
         end; try congruence.
Qed.

Lemma nat_of_Z_same : forall i,
  nat_of_Z i = Z.to_nat i.
Proof.
  induction i; simpl; intros; auto.
Qed.

Lemma Z_of_nat_eq : forall n,
  nat_of_Z (Z.of_nat n) = n.
Proof.
  intros. rewrite nat_of_Z_same. rewrite Nat2Z.id. reflexivity.
Qed.

Lemma wf_typ_ptr_live : forall D live rmap tenv t r,
  wf_rmap D live rmap ->
  wf_typ tenv D (Typ_ptr t r) ->
  In (alpha rmap r) live.
Proof.
  intros. unfold wf_rmap in H. inv H0. apply H in H3. 
  t_simp. unfold alpha. rewrite H0. auto.
Qed.

Lemma wf_typ_ptrU_live : forall D live rmap tenv t r,
  wf_rmap D live rmap ->
  wf_typ tenv D (Typ_ptrU t r) ->
  In (alpha rmap r) live.
Proof.
  intros. unfold wf_rmap in H. inv H0. apply H in H4. 
  t_simp. unfold alpha. rewrite H0. auto.
Qed.

Lemma wf_typ_TS : forall tenv D t,
  wf_typ tenv D t ->
  TS tenv t.
Proof.
  induction 1; intros; auto.
Qed.

(* ---------------------------------------------------------------------- *)
(** * Helper Lemmas *)

Lemma wf_env_subsume : forall G1 G2 env C live HT rmap,
  extends_gamma G1 G2 ->
  wf_env C live HT rmap env G2 ->
  wf_env C live HT rmap env G1.
Proof.
  unfold wf_env; auto. 
Qed.
  
Lemma wf_opreg_val : forall fs lo tenv D P G env x t live rmap HT,
  wf_operand (mk_config fs lo tenv) D P G (Op_reg x) t ->
  wf_env (mk_config fs lo tenv) live HT rmap env G ->
  exists v, Nenv.find x env = Some v /\ 
    wf_value fs lo tenv live HT v (sigma rmap t).
Proof.
  intros. inv H. unfold wf_env in *. apply H0 in H6; crush.
Qed.

Lemma wf_opconst_val2 : forall fs lo tenv D P G c t live HT rmap,
  wf_operand (mk_config fs lo tenv) D P G (Op_const c) t ->
  exists v, 
    const2rtv c = v /\ wf_value fs lo tenv live HT v (sigma rmap t).
Proof.
  destruct c; simpl; intros.
  { inv H. inv H5. exists (RT_ptr (Word.repr 0) :: nil). split; auto. repeat econstructor; eauto. }
  { inv H. inv H5. exists (RT_ptr (Word.repr 0) :: nil). split; auto.  repeat econstructor; eauto. }
  { inv H. inv H5. exists (RT_float f :: nil). split; auto. repeat constructor. }
  { inv H. inv H5. exists (RT_double d :: nil). split; auto. repeat constructor. }
  { inv H. inv H5. exists (RT_int sz l i :: nil). split; auto. repeat constructor.
    assert (l = pf0). apply proof_irr. subst. repeat constructor. }
  { inv H. inv H5. exists (RT_fun (f_lab f) :: nil); crush. repeat econstructor.
    unfold check_fun. destruct lab_dec; try congruence. rewrite H3.
    destruct_c list_eq_dec. destruct_c list_eq_dec.
    destruct_c (f_ret f). destruct_c typ_eq_dec. }
  { inv H. inv H5. induction H3. exists nil. split; auto. econstructor.
    simpl. inv H; t_simp; subst; 
    match goal with
      | [ |- exists v, ?v' = v /\ wf_value _ _ _ _ _ _ _ ] => exists v'
    end; split; auto; repeat econstructor; eauto.
    (*
    exists (RT_float (Word.repr (UNDEF_STREAM tt)) :: nil).
    split; auto. repeat constructor.
    exists (RT_int sz pf (Word.repr (UNDEF_STREAM tt)) :: nil).
    split; auto. repeat constructor. 
    *)}
  { inv H. inv H5. }
Qed.

Lemma wf_opfun_val : forall fs lo tenv D P G o prgns sig ret HT env live rmap,
  wf_operand (mk_config fs lo tenv) D P G o (Ftyp_fun prgns sig ret :: nil) ->
  wf_env (mk_config fs lo tenv) live HT rmap env G ->
  exists l, 
    op2fun o env = Some l /\
    (l = Word.zero \/
    exists f,
      lookup_fun l fs = Some f /\
      domain (f_prgn f) = prgns /\
      f_sig f = sig /\
      f_ret f = ret).
Proof.
  intros. unfold op2fun. unfold op2rtv. destruct o. 
  { unfold wf_env in *. inv H. apply H0 in H6. t_simp. simpl in *.
    assert (sigma rmap (Ftyp_fun prgns sig ret :: nil) = 
      (Ftyp_fun prgns sig ret :: nil)). crush. rewrite <- H2 in H1.
    eapply canonical_form_fun in H1. rewrite H. destruct H1; crush. eauto. eauto 10. }
  { inv H. inv H6. unfold const2rtv. eauto 10. inv H. inv H3. }
Qed.

Lemma wf_op_val : forall fs lo tenv D P G env o t live rmap HT,
  wf_operand (mk_config fs lo tenv) D P G o t ->
  wf_env (mk_config fs lo tenv) live HT rmap env G ->
  exists v, op2rtv o env = Some v /\ 
    wf_value fs lo tenv live HT v (sigma rmap t).
Proof.
  destruct o; simpl; intros.
  { eapply wf_opreg_val; eauto. }
  { exists (const2rtv c). split; auto. eapply wf_opconst_val2 in H; eauto. t_simp; subst; eauto. }
Qed.

Lemma wf_val_int_any : forall fs lo tenv live HT sz pf i,
  wf_value fs lo tenv live HT (RT_int sz pf i :: nil) (Ftyp_int sz pf :: nil).
Proof.
  intros. destruct i.
  assert (Word.repr intval = Word.mkint _ intval intrange). 
  apply Word.mkint_eq. rewrite Zmod_small; auto. rewrite <- H.
  repeat constructor.
Qed.

(* ---------------------------------------------------------------------- *)
(** * Extension lemmas *)

Lemma wf_env_val_ext : forall env x rt t G lo fs tenv HT live rmap,
  wf_env (mk_config fs lo tenv) live HT rmap env G ->
  wf_value fs lo tenv live HT rt (sigma rmap t) ->
  wf_env (mk_config fs lo tenv) live HT rmap (Nenv.add x rt env) (Nenv.add x t G).
Proof.
  unfold wf_env; intros; simpl in *. 
  destruct (rgn_dec x0 x).
  { rewrite NFacts.add_eq_o in *; crush; eauto. }
  { rewrite NFacts.add_neq_o in *; crush; eauto. }
Qed.

(* ---------------------------------------------------------------------- *)
(** * Deterministic Instruction Helper Lemmas *)

(* Ltac to simplify some instruction cases *)
Ltac t_insn_simpl_pro :=
  repeat (match goal with
            | [ H1: wf_env (mk_config ?fs ?lo ?tenv) ?live ?HT ?rmap ?env ?G,
                H2: wf_operand (mk_config ?fs ?lo ?tenv) ?D ?P ?G ?o ?t |- _ ] => 
                apply wf_op_val with fs lo tenv D P G env o t live rmap HT in H2; [ | assumption ]
            | [ H : wf_value _ _ _ _ _ _ (sigma ?rmap (Ftyp_int _ _ :: nil)) |- _ ] => 
                apply canonical_form_int in H
            | [ H : wf_value _ _ _ _ _ _ (sigma ?rmap (flatten_typ _ _ (Typ_int _ _))) |- _ ] => 
                apply canonical_form_int in H 
            | [ H: wf_value _ _ _ _ _ _ (sigma ?rmap (Ftyp_ptr _ _ :: nil)) |- _ ] =>
                apply canonical_form_ptr in H
            | [ H: wf_value _ _ _ _ _ _ (sigma ?rmap (Ftyp_ptrU _ _ :: nil)) |- _ ] =>
                apply canonical_form_ptrU in H
            | [ H : wf_value _ _ _ _ _ _ (sigma ?rmap (Ftyp_float :: nil)) |- _ ] => 
                apply canonical_form_float in H 
            | [ H : wf_value _ _ _ _ _ _ (sigma ?rmap (flatten_typ _ _ Typ_float)) |- _ ] => 
                apply canonical_form_float in H 
            | [ H : wf_value _ _ _ _ _ _ (sigma ?rmap (Ftyp_double :: nil)) |- _ ] => 
                apply canonical_form_double in H 
            | [ H : wf_value _ _ _ _ _ _ (sigma ?rmap (flatten_typ _ _ Typ_double)) |- _ ] => 
                apply canonical_form_double in H 
            | [ H: exists i, _ |- _ ] => destruct H
            | [ H: _ /\ _ |- _ ] => destruct H
            | [ H: _ \/ _ |- _ ] => destruct H
            | [ |- context [ eq_nat_dec ?a ?b ] ] =>
              destruct (eq_nat_dec a b); try congruence
            | [ H: op2rtv ?o ?env = Some ?v |- context [ op2rtv ?o ?env ] ] => rewrite H
          end; try subst; simpl).

Ltac t_solve_int_goal :=
  match goal with
    | [ |- exists v, Some (RT_int ?sz ?pf ?i :: nil) = Some v /\ _ ] =>
      exists (RT_int sz pf i :: nil); split; auto; eapply wf_val_int_any
    | [ |- exists v, Load_Val (RT_int ?sz ?pf ?i :: nil) = Load_Val v /\ _ ] =>
      exists (RT_int sz pf i :: nil); split; auto; eapply wf_val_int_any
  end.

Ltac t_solve_float_goal :=
  match goal with
    | [ |- exists v, Some (RT_float ?f :: nil) = Some v /\ _ ] => 
      exists (RT_float f :: nil); repeat econstructor
    | [ |- exists v, Some (RT_double ?d :: nil) = Some v /\ _ ] => 
      exists (RT_double d :: nil); repeat econstructor
  end.

(* ---------------------------------------------------------------------- *)
(* Insertvalue helper lemmas *)

Lemma wf_val_app : forall fs lo tenv live HT v1 v2 t,
  wf_value fs lo tenv live HT (v1 ++ v2) t ->
  exists t1, exists t2,
    t = t1 ++ t2 /\
    wf_value fs lo tenv live HT v1 t1 /\
    wf_value fs lo tenv live HT v2 t2.
Proof.
  induction v1; simpl; intros.
  { exists nil. exists t. simpl. split; auto. split; auto. constructor. }
  { inv H. eapply IHv1 in H6; eauto. t_simp. subst.
    exists (t0 :: x). exists x0. split; auto. split; auto.
    constructor; auto. }
Qed.

Lemma wf_val_app2 : forall fs lo tenv live HT v1 v2 t1 t2,
  wf_value fs lo tenv live HT v1 t1 ->
  wf_value fs lo tenv live HT v2 t2 ->
  wf_value fs lo tenv live HT (v1 ++ v2) (t1 ++ t2).
Proof.
  induction v1; simpl; intros.
  { inv H. simpl. auto. }
  { inv H. simpl. eapply IHv1 in H0; eauto. econstructor; eauto. }
Qed.

Lemma wf_val_app3 : forall fs lo tenv live HT v1 v2 t,
  wf_value fs lo tenv live HT (v1 ++ v2) t ->
  wf_value fs lo tenv live HT v1 (firstn (length v1) t) /\
  wf_value fs lo tenv live HT v2 (skipn (length v1) t).
Proof.
  induction v1; simpl; intros.
  { split; try constructor; auto. }
  { inv H. split; try constructor; auto. 
    apply IHv1 in H6. destruct H6. auto.
    apply IHv1 in H6. destruct H6. auto. }
Qed.

Lemma wf_val_app4 : forall fs lo tenv live HT v1 v2 t,
  wf_value fs lo tenv live HT v1 (firstn (length v1) t) ->
  wf_value fs lo tenv live HT v2 (skipn (length v1) t) ->
  wf_value fs lo tenv live HT (v1 ++ v2) t.
Proof.
  induction v1; simpl; intros; auto.
  inv H. destruct t; crush. econstructor; eauto.
Qed.

Lemma wf_val_length : forall fs lo tenv live HT v t,
  wf_value fs lo tenv live HT v t ->
  length v = length t.
Proof.
  induction 1; crush.
Qed.

Lemma wf_val_app5 : forall fs lo tenv live HT v1 v2 t1 t2,
  wf_value fs lo tenv live HT (v1 ++ (v2 :: nil)) (t1 ++ (t2 :: nil)) ->
  wf_value fs lo tenv live HT v1 t1 /\
  wf_value fs lo tenv live HT (v2 :: nil) (t2 :: nil).
Proof.
  induction v1; simpl; intros.
  { inv H. inv H6. destruct t1. simpl in *. inv H4. split; auto. constructor.
    constructor. auto. constructor. simpl in *. inv H4. 
    specialize (app_cons_not_nil t1 nil t2); intros. crush. }
  { inv H. inv H6. 
    specialize (app_cons_not_nil v1 nil v2); intros. crush. 
    destruct t1. simpl in H4. crush. simpl in H4. inv H4.
    assert (wf_value fs lo tenv live HT (v::vs) (t0::ts0)). constructor; auto.
    rewrite H6 in H1. rewrite H in H1. apply IHv1 in H1. destruct H1.
    split; auto. constructor; auto. }
Qed.
    

Lemma skipn_cons : forall {A:Type} n t (t':A) ts,
  skipn n t = t' :: ts ->
  skipn n t = t' :: skipn (n + 1) t.
Proof.
  induction n; simpl; intros; auto.
  destruct t. crush. f_equal. inv H. auto.
  destruct t. crush.
  eapply IHn; eauto.
Qed.

Lemma firstn_cons : forall {A:Type} n (v: list A),
  (n + 1 <= length v)%nat ->
  exists v', firstn (n + 1) v = firstn n v ++ (v' :: nil).
Proof.
  induction n; simpl; intros. 
  { destruct v; eauto. simpl in H. omegaContradiction. }
  { destruct v; eauto. simpl in H. omegaContradiction.
    simpl. simpl in H. 
    assert (n + 1 <= length v)%nat by omega. apply IHn in H0. t_simp.
    rewrite H0. eauto. }
Qed.

Lemma skipn_firstn_splice : forall {A:Type} n t (t':A) ts,
  skipn n t = t' :: ts ->
  firstn (n + 1) t = firstn n t ++ (t' :: nil).
Proof.
  induction n; simpl; intros.
  { destruct t. crush. inv H. auto. }
  { destruct t. crush. simpl. f_equal. eauto. }
Qed. 

Lemma wf_val_splice : forall fs lo tenv live HT v1 v2 n t1 t2,
  wf_value fs lo tenv live HT v1 t1 ->
  wf_value fs lo tenv live HT v2 t2 ->
  ftyps_subset t1 (skipn n t2) = true ->
  (n + length t1 <= length t2)%nat ->
  wf_value fs lo tenv live HT (firstn n v2 ++ v1 ++ skipn (n + length v1) v2) t2.
Proof.
  induction v1; simpl; intros.
  { inv H. replace (n + 0)%nat with n by omega. rewrite firstn_skipn. auto. }
  { inv H. replace (n + S (length v1))%nat with ((n+1) + (length v1))%nat by omega.
    assert (firstn n v2 ++ a :: v1 ++ skipn (n + 1 + length v1) v2 = 
            (firstn n v2 ++ (a :: nil)) ++ v1 ++ skipn (n + 1 + length v1) v2).
    rewrite <- app_assoc. f_equal.
    rewrite H.

    t_dup H0. apply wf_val_length in H'. simpl in H2. 
    replace (n + S (length ts))%nat with (n + 1 + length ts)%nat in H2 by omega.
    eapply IHv1 with (n := (n + 1)%nat) in H0; eauto.
    apply wf_val_app3 in H0. destruct H0.
    apply wf_val_app4; auto. 

    { clear - H0 H' H2 H1 H7. rewrite firstn_length in H0.
      rewrite <- H' in H2.
      assert ((n + 1) <= length v2)%nat by omega.
      apply Min.min_l in H. rewrite H in H0.
      rewrite app_length. simpl. rewrite firstn_length.
      assert (n <= length v2)%nat by omega.
      apply Min.min_l in H3. rewrite H3.
      simpl in H1. consider (skipn n t2); intros; try congruence.
      destruct_c ftyp_eq_dec. rewrite e in *. clear e.
      clear H. clear H3.
      t_dup H1. apply skipn_cons in H1. rewrite H1 in H'0. inv H'0.

      apply skipn_firstn_splice in H1. rewrite H1 in H0. rewrite H1.
      assert (n + 1 <= length v2)%nat by omega.
      specialize (firstn_cons n v2 H); intros. t_simp. 
      rewrite H3 in H0.
      apply wf_val_app5 in H0. t_simp.
      apply wf_val_app2; auto. constructor; auto. constructor. }
    { rewrite firstn_length in H3. rewrite app_length. simpl. rewrite firstn_length.
      rewrite <- H' in H2. 
      assert ((n + 1) <= length v2)%nat by omega.
      apply Min.min_l in H4. rewrite H4 in H3.
      assert (n <= length v2)%nat by omega.
      apply Min.min_l in H5. rewrite H5. auto. }
    { clear -H1 H' H2. rewrite <- H' in H2. simpl in H1.
      consider (skipn n t2); intros; try congruence.
      destruct_c ftyp_eq_dec; subst.
      t_dup H. apply skipn_cons in H.
      rewrite H in H'0. inv H'0. auto. }
  }
Qed.

Lemma wf_val_splice2 : forall fs lo tenv live HT v1 v2 n t1 t2,
  wf_value fs lo tenv live HT v1 t1 ->
  wf_value fs lo tenv live HT v2 t2 ->
  ftyps_subset2 t1 (skipn n t2) = true ->
  (n + length t1 <= length t2)%nat ->
  wf_value fs lo tenv live HT (firstn n v2 ++ v1 ++ skipn (n + length v1) v2) t2.
Proof.
  induction v1; simpl; intros.
  { inv H. replace (n + 0)%nat with n by omega. rewrite firstn_skipn. auto. }
  { inv H. replace (n + S (length v1))%nat with ((n+1) + (length v1))%nat by omega.
    assert (firstn n v2 ++ a :: v1 ++ skipn (n + 1 + length v1) v2 = 
            (firstn n v2 ++ (a :: nil)) ++ v1 ++ skipn (n + 1 + length v1) v2).
    rewrite <- app_assoc. f_equal.
    rewrite H.

    t_dup H0. apply wf_val_length in H'. simpl in H2. 
    replace (n + S (length ts))%nat with (n + 1 + length ts)%nat in H2 by omega.
    eapply IHv1 with (n := (n + 1)%nat) in H0; eauto.
    apply wf_val_app3 in H0. destruct H0.
    apply wf_val_app4; auto. 

    { clear - H0 H' H2 H1 H7. rewrite firstn_length in H0.
      rewrite <- H' in H2.
      assert ((n + 1) <= length v2)%nat by omega.
      apply Min.min_l in H. rewrite H in H0.
      rewrite app_length. simpl. rewrite firstn_length.
      assert (n <= length v2)%nat by omega.
      apply Min.min_l in H3. rewrite H3.
      simpl in H1. consider (skipn n t2); intros; try congruence.
      consider (ftyp_sub t f); intros; try congruence.
      (* rewrite e in *. clear e. *)
      clear H. clear H3.
      t_dup H1. apply skipn_cons in H1. rewrite H1 in H'0. inv H'0.

      apply skipn_firstn_splice in H1. rewrite H1 in H0. rewrite H1.
      assert (n + 1 <= length v2)%nat by omega.
      specialize (firstn_cons n v2 H); intros. t_simp. 
      rewrite H3 in H0.
      apply wf_val_app5 in H0. t_simp.
      apply wf_val_app2; auto. constructor; auto. 
      eapply wf_val_ftyp_sub; eauto. constructor. }
    { rewrite firstn_length in H3. rewrite app_length. simpl. rewrite firstn_length.
      rewrite <- H' in H2. 
      assert ((n + 1) <= length v2)%nat by omega.
      apply Min.min_l in H4. rewrite H4 in H3.
      assert (n <= length v2)%nat by omega.
      apply Min.min_l in H5. rewrite H5. auto. }
    { clear -H1 H' H2. rewrite <- H' in H2. simpl in H1.
      consider (skipn n t2); intros; try congruence.
      consider (ftyp_sub t f); intros; try congruence.
      t_dup H. apply skipn_cons in H.
      rewrite H in H'0. inv H'0. auto. }
  }
Qed.

Lemma skipn_sigma_comm : forall n rmap t,
  sigma rmap (skipn n t) = skipn n (sigma rmap t).
Proof.
  induction n; simpl; intros; auto.
  destruct t; simpl; auto.
Qed.

Lemma length_sigma_inv : forall t rmap,
  length (sigma rmap t) = length t.
Proof.
  induction t; simpl; intros; auto.
Qed.

Lemma evalinsertvalue_prop : forall fs lo tenv D P G1 G2 live HT rmap env x t1 o1 t2 o2 c,
  wf_insn (mk_config fs lo tenv) D P (Insn_insertvalue x t1 o1 t2 o2 c) G1 G2 ->
  wf_env (mk_config fs lo tenv) live HT rmap env G1 ->
  exists v,
    eval_insertvalue env o1 o2 c = Load_Val v /\
    wf_value fs lo tenv live HT v (sigma rmap (flatten_typ lo tenv t1)).
Proof.
  intros; unfold eval_insertvalue; inv H; t_insn_simpl_pro; simpl in *.
  exists ((firstn (Z.to_nat (Word.unsigned i)) x0 ++
        x1 ++ skipn (Z.to_nat (Word.unsigned i) + length x1) x0)).
  split; auto. 
  eapply ftyps_subset2_sigma in H18. erewrite skipn_sigma_comm in H18; eauto.
  eapply wf_val_splice2; eauto. rewrite length_sigma_inv.
  rewrite length_sigma_inv. auto.
  (*
  eapply ftyps_subset_sigma in H18. erewrite skipn_sigma_comm in H18; eauto.
  eapply wf_val_splice2; eauto. rewrite length_sigma_inv.
  rewrite length_sigma_inv. auto.
  *)
Qed.

Lemma wf_val_ftyps_subset : forall fs lo tenv live HT t2 t1 v,
  ftyps_subset t2 t1 = true ->
  (length t2 <= length v)%nat ->
  wf_value fs lo tenv live HT v t1 ->
  wf_value fs lo tenv live HT (firstn (length t2) v) t2.
Proof.
  induction t2; simpl; intros.
  { constructor. }
  { destruct t1. inv H1. simpl in H0. omegaContradiction.
    destruct_c ftyp_eq_dec; subst. inv H1. simpl in *.
    eapply IHt2 in H8; eauto. econstructor; eauto.
    omega. }
Qed.

Lemma wf_val_splice3 : forall fs lo tenv live HT n v t1 t2,
  wf_value fs lo tenv live HT v t1 ->
  ftyps_subset t2 (skipn n t1) = true ->
  (n + length t2 <= length t1)%nat ->
  wf_value fs lo tenv live HT (firstn (length t2) (skipn n v)) t2.
Proof.
  induction n; simpl; intros; auto.
  { t_dup H. apply wf_val_length in H. rewrite <- H in H1. eapply wf_val_ftyps_subset; eauto. }
  { destruct t1. simpl in H1. omegaContradiction. simpl in H1. inv H.
    eapply IHn in H8; eauto. omega. }
Qed.

    
Lemma evalextractvalue_prop : forall fs lo tenv D P G1 G2 live HT rmap env x t1 o t2 c,
  wf_insn (mk_config fs lo tenv) D P (Insn_extractvalue x t1 o t2 c) G1 G2 ->
  wf_env (mk_config fs lo tenv) live HT rmap env G1 ->
  exists v,
    eval_extractvalue env lo tenv o t2 c = Load_Val v /\
    wf_value fs lo tenv live HT v (sigma rmap (flatten_typ lo tenv t2)).
Proof.
  intros; unfold eval_extractvalue; inv H; t_insn_simpl_pro; simpl in *.
  exists (firstn (length (flatten_typ lo tenv t2))
          (skipn (Z.to_nat (Word.unsigned i)) x0)).
  split; auto.
  eapply ftyps_subset_sigma in H16. erewrite skipn_sigma_comm in H16; eauto.
  erewrite <- length_sigma_inv.
  eapply wf_val_splice3; eauto.
  rewrite length_sigma_inv. rewrite length_sigma_inv. auto.
Qed.

(* ---------------------------------------------------------------------- *)
(* Binop helper lemmas *)

Lemma evalbinop_prop : forall env D P HT G1 bop o1 o2 lo fs live rmap tenv n pf1 pf2,
  wf_operand (mk_config fs lo tenv) D P G1 o1 (Ftyp_int n pf1 :: nil) ->
  wf_operand (mk_config fs lo tenv) D P G1 o2 (Ftyp_int n pf2 :: nil) ->
  wf_env (mk_config fs lo tenv) live HT rmap env G1 -> 
  exists i, 
    eval_binop env bop o1 o2 = Some (RT_int n pf1 i :: nil) /\
    wf_value fs lo tenv live HT (RT_int n pf1 i :: nil) (Ftyp_int n pf1 :: nil).
Proof.
  intros; unfold eval_binop; destruct bop; t_insn_simpl_pro;
    match goal with
      | [ |- exists i', Some (RT_int ?n ?pf ?i :: nil) = Some (RT_int ?n ?pf i' :: nil) /\ _ ] =>
        exists i; repeat econstructor
    end.
Qed.

(* ---------------------------------------------------------------------- *)
(* Fbinop helper lemmas *)

Lemma evalfbinop_prop : forall env D P G1 c o1 o2 t1 t2 lo fs tenv live HT rmap,
  (* wf_insn (mk_config fs lo tenv) D P (Insn_fbinop x c o1 o2) G1 G2 -> *)
  wf_operand (mk_config fs lo tenv) D P G1 o1 (t1 :: nil) ->
  wf_operand (mk_config fs lo tenv) D P G1 o2 (t2 :: nil) ->
  t1 = Ftyp_float \/ t1 = Ftyp_int 31 lt_31_MAX_I_BITS ->
  t2 = Ftyp_float \/ t2 = Ftyp_int 31 lt_31_MAX_I_BITS ->
  wf_env (mk_config fs lo tenv) live HT rmap env G1 ->
  exists v, 
    eval_fbinop env c o1 o2 = Some v /\
    wf_value fs lo tenv live HT v (Ftyp_float :: nil).
Proof.
  intros; unfold eval_fbinop; t_insn_simpl_pro; try t_solve_float_goal.
Qed.

Lemma evalfbinop_prop2 : forall env D P G1 c o1 o2 t1 t2 lo fs tenv live HT rmap,
  (* wf_insn (mk_config fs lo tenv) D P (Insn_fbinop x c o1 o2) G1 G2 -> *)
  wf_operand (mk_config fs lo tenv) D P G1 o1 (t1 :: nil) ->
  wf_operand (mk_config fs lo tenv) D P G1 o2 (t2 :: nil) ->
  t1 = Ftyp_double \/ t1 = Ftyp_int 63 lt_63_MAX_I_BITS ->
  t2 = Ftyp_double \/ t2 = Ftyp_int 63 lt_63_MAX_I_BITS ->
  wf_env (mk_config fs lo tenv) live HT rmap env G1 ->
  exists v, 
    eval_fbinop env c o1 o2 = Some v /\
    wf_value fs lo tenv live HT v (Ftyp_double :: nil).
Proof.
  intros; unfold eval_fbinop; t_insn_simpl_pro; try t_solve_float_goal.
Qed.

(* ---------------------------------------------------------------------- *)
(* Icmp helper lemmas *)

Lemma evalicmp_prop : forall env D P G1 G2 i c o1 o2 lo fs tenv live HT rmap,
  wf_insn (mk_config fs lo tenv) D P (Insn_icmp i c o1 o2) G1 G2 ->
  wf_env (mk_config fs lo tenv) live HT rmap env G1 ->
  exists v, 
    eval_icmp env c o1 o2 = Some v /\
    wf_value fs lo tenv live HT v (Ftyp_int 0 lt_0_MAX_I_BITS :: nil).
Proof.
  intros; inv H; unfold eval_icmp; destruct c; 
    repeat match goal with
             | [ H: context [ match ?t with
                                | Ftyp_float => _
                                | Ftyp_double => _
                                | Ftyp_int _ _ => _
                                | Ftyp_ptr _ _ => _
                                | Ftyp_fun _ _ _ => _
                                | Ftyp_ptrU _ _ => _
                     end
             ] |- _ ] => destruct_c t; try contradiction
           end; t_insn_simpl_pro; t_solve_int_goal.
Qed.
  
(* ---------------------------------------------------------------------- *)
(* Fcmp helper lemmas *)
(*
Lemma ordered_fcmp_prop : forall fs lo tenv live HT c f1 f2,
  exists v, 
    ordered_fcmp c f1 f2 = Some v /\
    wf_value fs lo tenv live HT v (Ftyp_int 0 lt_0_MAX_I_BITS :: nil).
Proof.
  intros; destruct f1; destruct f2; unfold ordered_fcmp; destruct c; t_solve_int_goal.
Qed.

Lemma unordered_fcmp_prop : forall fs lo tenv live HT c f1 f2,
  exists v,
    unordered_fcmp c f1 f2 = Some v /\
    wf_value fs lo tenv live HT v (Ftyp_int 0 lt_0_MAX_I_BITS :: nil).
Proof.
  intros; destruct f1; destruct f2; unfold unordered_fcmp; destruct c; t_solve_int_goal.
Qed.

match goal with
| [ |- exists v, Some (RT_int ?sz ?pf ?i :: nil) = Some v /\ _ ] =>
exists (RT_int sz pf i :: nil); split; auto; eapply wf_val_int_any
| [ |- context [ ordered_fcmp ] ] => eapply ordered_fcmp_prop; eauto
| [ |- context [ unordered_fcmp ] ] => eapply unordered_fcmp_prop; eauto
end.
*)

Lemma evalfcmp_prop : forall env D P G1 G2 i c o1 o2 lo fs tenv live HT rmap,
  wf_insn (mk_config fs lo tenv) D P (Insn_fcmp i c o1 o2) G1 G2 ->
  wf_env (mk_config fs lo tenv) live HT rmap env G1 ->
  exists v, 
    eval_fcmp env c o1 o2 = Some v /\
    wf_value fs lo tenv live HT v (Ftyp_int 0 lt_0_MAX_I_BITS :: nil).
Proof.
  intros; inv H; unfold eval_fcmp; destruct t1; destruct t2; try contradiction;
    t_insn_simpl_pro;
    try
    match goal with
      | [ |- exists v, Some (RT_int ?sz ?pf ?i :: nil) = Some v /\ _ ] =>
        exists (RT_int sz pf i :: nil); split; auto; eapply wf_val_int_any
    end.
Qed.

(* ---------------------------------------------------------------------- *)
(* Select helper lemmas *)

Lemma evalselect_prop : forall env D P HT G1 G2 x c o1 o2 t lo fs live rmap tenv,
  wf_insn (mk_config fs lo tenv) D P (Insn_select x Typ_int1 c t o1 t o2) G1 G2 ->
  wf_env (mk_config fs lo tenv) live HT rmap env G1 -> 
  exists rt, eval_select env lo tenv t c o1 o2 = Some rt /\
    wf_value fs lo tenv live HT rt (sigma rmap (flatten_typ lo tenv t)).
Proof.
  intros; inv H; unfold eval_select; unfold Ftyp_int1 in *; t_insn_simpl_pro;
    simpl in *; destruct_c Word.eq; eauto.
  exists (weaken_val x1 (flatten_typ lo tenv t)). split; auto. 
  apply wf_val_ftyps_weaken with (t1 := t1); auto.
  exists (weaken_val x0 (flatten_typ lo tenv t)). split; auto. 
  apply wf_val_ftyps_weaken with (t1 := t2); auto.
Qed.

(* ---------------------------------------------------------------------- *)
(* Load helper lemmas *)

Lemma load_ht_prop' : forall t r tenv HT n m live fs lo,
  Zenv.find n HT = Some (t,r) ->
  wf_mem fs lo tenv live HT m ->
  exists v, load m lo n t = Some v /\ 
    wf_value' fs lo tenv live HT v t.
Proof.
  intros. unfold wf_mem in H0. apply H0 in H. t_simp. eauto. 
Qed.

Ltac t_simpl_check_HT :=
  repeat match goal with
           | [ H: context [ match ?p with | (_, _) => _ end ] |- _ ] => destruct p
           | [ H: context [ match ?x with | Some _ => _ | None => _ end ] |- _ ] => 
             (consider x); intros; try congruence
           | [ H: context [ if ?x then _ else _ ] |- _ ] =>
             (consider x); intros; try congruence
         end; simpl in *; subst.

Lemma load_ht_prop : forall t fs lo tenv live HT n m r,
  n <> 0 ->
  check_HT lo HT n r t = true ->
  wf_mem fs lo tenv live HT m ->
  wf_HT lo HT ->
  exists v, 
    load_helper m lo n t = Some v /\
    wf_value fs lo tenv live HT v t.
Proof.
  induction t; simpl; intros; auto. 
  { exists nil. repeat split; econstructor; eauto. }
  { unfold check_HT in H0. destruct_c zeq. simpl in *. t_simpl_check_HT.
    unfold wf_mem in H1. t_dup H0. eapply load_ht_prop' in H0; eauto. t_simp. 
    assert (check_HT lo HT (n + size_ftyp lo f) r0 t = true).
    unfold check_HT. destruct zeq; auto. 
    eapply IHt in H5; eauto. t_simp. rewrite H5. rewrite H0.
    exists (x :: x0). repeat split; econstructor; eauto.
    unfold wf_HT in H2. apply H2 in H'. t_simp. size_ftyp_prop; crush. 
  }
Qed.

Lemma rt_ptr_conv : forall (addr:Word.int WORDSIZE_BITS),
  Word.unsigned addr mod Word.modulus 63 = Word.unsigned addr.
Proof.
  intros. rewrite Zmod_small; auto. apply Word.unsigned_range.
Qed.

Lemma evalload_prop : forall fs lo tenv D P env G1 G2 m o t r x live rmap HT,
  wf_insn (mk_config fs lo tenv) D P (Insn_load x (Typ_ptr t r) o) G1 G2 ->
  wf_env (mk_config fs lo tenv) live HT rmap env G1 ->
  wf_mem fs lo tenv live HT m ->
  wf_HT lo HT ->
  wf_tenv tenv ->
  (exists rt, eval_load env m lo tenv rmap (Typ_ptr t r) o = Load_Val rt /\
    wf_value fs lo tenv live HT rt (sigma rmap (flatten_typ lo tenv t))) \/
  (eval_load env m lo tenv rmap (Typ_ptr t r) o = Load_SvaErr).
Proof.
  intros. inv H. simpl. unfold op2ptr. t_insn_simpl_pro. destruct zeq; auto.
  rewrite <- flatten_sigma_comm in H5; auto. eapply check_HT_subset in H5; eauto.
  eapply load_ht_prop in H5; eauto. t_simp. simpl in H4. inv H14. 
  rewrite flatten_sigma_comm in H4; auto. 
  rewrite rt_ptr_conv. rewrite H4. eauto. 
  rewrite rt_ptr_conv in n. eauto.
Qed.

Opaque load_helper. 
Lemma evalload_propU : forall fs lo tenv D P env G1 G2 m o r x live rmap HT,
  wf_insn (mk_config fs lo tenv) D P (Insn_load x (Typ_ptrU 4 r) o) G1 G2 ->
  wf_env (mk_config fs lo tenv) live HT rmap env G1 ->
  wf_mem fs lo tenv live HT m ->
  wf_HT lo HT ->
  wf_tenv tenv ->
  (exists rt, eval_load env m lo tenv rmap (Typ_ptrU 4 r) o = Load_Val rt /\
    wf_value fs lo tenv live HT rt (sigma rmap (Ftyp_int32 :: nil))) \/
  (eval_load env m lo tenv rmap (Typ_ptrU 4 r) o = Load_SvaErr).
Proof.
  intros. inv H. simpl. unfold op2ptr. t_insn_simpl_pro.
  destruct zeq; eauto. rewrite bytes_sigma_inv with (rmap := rmap) in H5.
  eapply check_HT_subset_bytes with (sz2 := 4%nat) in H5; eauto. 
  eapply load_ht_prop in H5; eauto. t_simp. simpl in H4. 
  rewrite rt_ptr_conv. rewrite H4. left. 
  exists (bytestoint lo x0). split; auto. repeat econstructor.
  rewrite rt_ptr_conv in n. auto.
  unfold size_ftyp_nat in *. unfold size_ftyp in *. simpl in *. 
  assert (Z.of_nat sz >= Z.of_nat (Pos.to_nat 4)). omega. simpl in H4. omega.
Qed.

Lemma evalload_propU2 : forall fs lo tenv D P env G1 G2 m o r x live rmap HT,
  wf_insn (mk_config fs lo tenv) D P (Insn_load x (Typ_ptrU 8 r) o) G1 G2 ->
  wf_env (mk_config fs lo tenv) live HT rmap env G1 ->
  wf_mem fs lo tenv live HT m ->
  wf_HT lo HT ->
  wf_tenv tenv ->
  (exists rt, eval_load env m lo tenv rmap (Typ_ptrU 8 r) o = Load_Val rt /\
    wf_value fs lo tenv live HT rt (sigma rmap (Ftyp_int64 :: nil))) \/
  (eval_load env m lo tenv rmap (Typ_ptrU 8 r) o = Load_SvaErr).
Proof.
  intros. inv H. simpl. unfold op2ptr. t_insn_simpl_pro.
  destruct zeq; eauto. rewrite bytes_sigma_inv with (rmap := rmap) in H5.
  eapply check_HT_subset_bytes with (sz2 := 8%nat) in H5; eauto. 
  eapply load_ht_prop in H5; eauto. t_simp. simpl in H4. 
  rewrite rt_ptr_conv. rewrite H4. left. 
  exists (bytestoint64 lo x0). split; auto. repeat econstructor.
  rewrite rt_ptr_conv in n. auto.
  unfold size_ftyp_nat in *. unfold size_ftyp in *. simpl in *. 
  assert (Z.of_nat sz >= Z.of_nat (Pos.to_nat 8)). omega. simpl in H4. omega.
Qed.

Lemma evalload_propU3 : forall fs lo tenv D P env G1 G2 m o r x live rmap HT,
  wf_insn (mk_config fs lo tenv) D P (Insn_load x (Typ_ptrU 1 r) o) G1 G2 ->
  wf_env (mk_config fs lo tenv) live HT rmap env G1 ->
  wf_mem fs lo tenv live HT m ->
  wf_HT lo HT ->
  wf_tenv tenv ->
  (exists rt, eval_load env m lo tenv rmap (Typ_ptrU 1 r) o = Load_Val rt /\
    wf_value fs lo tenv live HT rt (sigma rmap (Ftyp_int8 :: nil))) \/
  (eval_load env m lo tenv rmap (Typ_ptrU 1 r) o = Load_SvaErr).
Proof.
  intros. inv H. simpl. unfold op2ptr. t_insn_simpl_pro.
  destruct zeq; eauto. rewrite bytes_sigma_inv with (rmap := rmap) in H5.
  eapply check_HT_subset_bytes with (sz2 := 1%nat) in H5; eauto. 
  eapply load_ht_prop in H5; eauto. t_simp. simpl in H4. 
  rewrite rt_ptr_conv. rewrite H4. left. 
  exists (x0). split; auto. repeat econstructor.
  rewrite rt_ptr_conv in n. auto.
  unfold size_ftyp_nat in *. unfold size_ftyp in *. simpl in *. 
  assert (Z.of_nat sz >= Z.of_nat (Pos.to_nat 1)). omega. simpl in H4. omega.
Qed.

Lemma evalload_propU4 : forall fs lo tenv D P env G1 G2 m o r x live rmap HT,
  wf_insn (mk_config fs lo tenv) D P (Insn_load x (Typ_ptrU 2 r) o) G1 G2 ->
  wf_env (mk_config fs lo tenv) live HT rmap env G1 ->
  wf_mem fs lo tenv live HT m ->
  wf_HT lo HT ->
  wf_tenv tenv ->
  (exists rt, eval_load env m lo tenv rmap (Typ_ptrU 2 r) o = Load_Val rt /\
    wf_value fs lo tenv live HT rt (sigma rmap (Ftyp_int16 :: nil))) \/
  (eval_load env m lo tenv rmap (Typ_ptrU 2 r) o = Load_SvaErr).
Proof.
  intros. inv H. simpl. unfold op2ptr. t_insn_simpl_pro.
  destruct zeq; eauto. rewrite bytes_sigma_inv with (rmap := rmap) in H5.
  eapply check_HT_subset_bytes with (sz2 := 2%nat) in H5; eauto. 
  eapply load_ht_prop in H5; eauto. t_simp. simpl in H4. 
  rewrite rt_ptr_conv. rewrite H4. left. 
  exists (bytestoint16 lo x0). split; auto. repeat econstructor.
  rewrite rt_ptr_conv in n. auto.
  unfold size_ftyp_nat in *. unfold size_ftyp in *. simpl in *. 
  assert (Z.of_nat sz >= Z.of_nat (Pos.to_nat 2)). omega. simpl in H4. omega.
Qed.

(* ---------------------------------------------------------------------- *)
(* Store helper lemmas *)

Lemma store_ht_prop' : forall t r m n v fs lo tenv HT live,
  Zenv.find n HT = Some (t,r) ->
  wf_HT lo HT ->
  wf_mem fs lo tenv live HT m ->
  wf_value' fs lo tenv live HT v t ->
    exists m', store m lo n t v = Some m' /\
      wf_mem fs lo tenv live HT m'.
Proof.
  unfold wf_mem; intros. unfold wf_HT in H0. t_dup H. apply H1 in H. t_simp.
  eapply load_store_valid in H; eauto. t_simp. exists x0. split; eauto. intros. t_dup H'.
  destruct (zeq n n0); subst. 
  { rewrite H4 in H'. inv H'. eapply load_store_same in H; eauto. 
    (* destruct t; eauto.
    t_simp. exists (RT_float x1). split; auto. econstructor.*) }
  { apply H0 with (n := n0) (t := t0) (r := r0) in H'; auto.
    apply H1 in H4. erewrite load_store_other; eauto. omega. }
Qed.

Lemma store_ht_prop : forall t m n v tenv HT live fs lo r,
  n <> 0 ->
  check_HT lo HT n r t = true ->
  wf_HT lo HT ->
  wf_mem fs lo tenv live HT m ->
  wf_value fs lo tenv live HT v t ->
  exists m', store_helper m lo n t v = Some m' /\
    wf_mem fs lo tenv live HT m'.
Proof.
  induction t; destruct v; simpl; intros; eauto. 
  { inv H3. } 
  { inv H3. }
  { inv H3. unfold check_HT in H0. destruct_c (zeq n 0). simpl in *. t_simpl_check_HT.
    assert (check_HT lo HT (n + size_ftyp lo f) r1 t = true).
    unfold check_HT. destruct_c zeq. 
    eapply IHt in H4; eauto. t_simp. rewrite H4. eapply store_ht_prop'; eauto.
    unfold wf_mem in H2. t_dup H0. apply H2 in H0. t_simp. 
    unfold wf_HT in H1. apply H1 in H'. t_simp. size_ftyp_prop; crush. }
Qed.

Lemma store_ht_prop2' : forall t1 t2 r m n v fs lo tenv HT live rmap,
  Zenv.find n HT = Some ((sigma' rmap t2), r) ->
  wf_HT lo HT ->
  wf_mem fs lo tenv live HT m ->
  ftyp_sub t1 t2 = true ->
  wf_value' fs lo tenv live HT v (sigma' rmap t1) ->
   exists m',
     store m lo n (sigma' rmap t2) v = Some m' /\ wf_mem fs lo tenv live HT m'.
Proof.
  unfold wf_mem; intros. unfold wf_HT in H0. t_dup H. apply H1 in H. t_simp.
  eapply load_store_valid_sub in H; eauto. t_simp. exists x0. split; eauto. intros. t_dup H'.
  destruct (zeq n n0); subst. 
  { rewrite H5 in H'. inv H'. eapply load_store_same_sub in H; eauto. 
    exists v. split; auto. eapply wf_val_ftyp_sub2; eauto. }
  { apply H0 with (n := n0) (t := t) (r := r0) in H'; auto.
    apply H1 in H5. erewrite load_store_other; eauto. 
    rewrite size_ftyp_sigma_inv. rewrite size_ftyp_sigma_inv in H'.
    rewrite size_ftyp_sub_same with (t1 := t1) (t2 := t2); auto. omega. }
Qed.

Lemma store_ht_prop2 : forall t1 t2 m n v tenv HT live fs lo r rmap,
  n <> 0 ->
  check_HT lo HT n r (sigma rmap t2) = true ->
  wf_HT lo HT ->
  wf_mem fs lo tenv live HT m ->
  wf_value fs lo tenv live HT v (sigma rmap t1) ->
  ftyps_subset2 t1 t2 = true ->
  exists m', store_helper m lo n (weaken_typ (sigma rmap t1) (sigma rmap t2)) v = Some m' /\
    wf_mem fs lo tenv live HT m'.
Proof.
  induction t1; destruct v; simpl; intros; eauto. 
  { inv H3. } 
  { inv H3. }
  { inv H3. unfold check_HT in H0. destruct_c (zeq n 0). destruct_c t2. 
    simpl in *. t_simpl_check_HT.
    assert (check_HT lo HT (n + size_ftyp lo (sigma' rmap f)) r1 (sigma rmap t2) = true).
    unfold check_HT. destruct_c zeq.
    eapply IHt1 in H6; eauto. t_simp.
    rewrite H6. eapply store_ht_prop2'; eauto.
    unfold wf_mem in H2. t_dup H0. apply H2 in H0. t_simp. 
    unfold wf_HT in H1. apply H1 in H'. t_simp. size_ftyp_prop; crush. }
Qed.

Lemma evalstore_prop : forall env D P G m o1 o2 t t' r lo fs tenv live rmap HT,
  wf_insn (mk_config fs lo tenv) D P (Insn_store t o1 (Typ_ptr t' r) o2) G G ->
  wf_env (mk_config fs lo tenv) live HT rmap env G ->
  wf_mem fs lo tenv live HT m ->
  wf_HT lo HT ->
  wf_tenv tenv ->
  (exists m', 
    eval_store env m lo tenv rmap t (Typ_ptr t' r) o1 o2 = Store_Val m' /\
    wf_mem fs lo tenv live HT m') \/
  (eval_store env m lo tenv rmap t (Typ_ptr t' r) o1 o2 = Store_SvaErr).
Proof.
  intros. inv H. 
  unfold eval_store. unfold op2ptr. t_insn_simpl_pro. destruct zeq; eauto. 
  simpl in *. 
  rewrite <- flatten_sigma_comm in H7; auto. (* eapply check_HT_subset2 in H7; eauto. *)
  eapply store_ht_prop2 in H7; eauto. t_simp. 
  rewrite <-flatten_sigma_comm; auto. rewrite <- flatten_sigma_comm; auto.
  rewrite rt_ptr_conv. rewrite H6. eauto. 
  rewrite rt_ptr_conv in n. auto.
Qed.
(*  
  rewrite <- flatten_sigma_comm in H8; auto. eapply check_HT_subset in H8; eauto.
  eapply store_ht_prop in H8; eauto. t_simp. inv H16. rewrite flatten_sigma_comm in H7; auto. 
  rewrite H7. eauto.
Qed.
*)

Lemma evalstore_propU : forall env D P G m o1 o2 t r lo fs tenv live rmap HT sz,
  wf_insn (mk_config fs lo tenv) D P (Insn_store t o1 (Typ_ptrU sz r) o2) G G ->
  wf_env (mk_config fs lo tenv) live HT rmap env G ->
  wf_mem fs lo tenv live HT m ->
  wf_HT lo HT ->
  wf_tenv tenv ->
  (exists m', 
    eval_store env m lo tenv rmap t (Typ_ptrU sz r) o1 o2 = Store_Val m' /\
    wf_mem fs lo tenv live HT m') \/
  (eval_store env m lo tenv rmap t (Typ_ptrU sz r) o1 o2 = Store_SvaErr).
Proof.
  intros. inv H. unfold eval_store. unfold op2ptr. t_insn_simpl_pro.
  destruct zeq; eauto. simpl in *. 
  specialize (wf_val_anytobytes x fs lo tenv live HT (length (anytobytes lo x)) eq_refl); intros.
  specialize (wf_val_any_size fs lo tenv live HT (sigma rmap t') x H7); intros.
  rewrite size_ftyps_sigma_inv in H10. rewrite <- H10 in H5.
  assert (length (anytobytes lo x) <= sz)%nat. omega.
  rewrite bytes_sigma_inv with (rmap := rmap) in H8.
  rewrite bytes_sigma_inv with (rmap := rmap) in H9.
  eapply check_HT_subset_bytes with (sz1 := sz') (sz2 := length (anytobytes lo x)) in H9; eauto.
  rewrite rt_ptr_conv in n.
  eapply store_ht_prop in H8; eauto. t_simp.
  rewrite <- bytes_sigma_inv with (rmap := rmap) in H8.
  rewrite rt_ptr_conv. rewrite H8. eauto. omega.
Qed.

Lemma store_helper_wf_meta : forall t HT m m' lo n v,
  wf_mem_metadata HT m ->
  store_helper m lo n t v = Some m' ->
  wf_mem_metadata HT m'.
Proof.
  induction t; destruct v; crush.
  consider (store_helper m lo (n + size_ftyp lo a) t v); intros; try congruence.
  eapply IHt in H0; eauto. eapply store_high_addr_same in H1. 
  unfold wf_mem_metadata in *; crush.
Qed.

Lemma evalstore_wf_meta : forall env m lo tenv t1 t2 o1 o2 m' HT rmap,
  wf_mem_metadata HT m ->
  eval_store env m lo tenv rmap t1 t2 o1 o2 = Store_Val m' ->
  wf_mem_metadata HT m'.
Proof.
  unfold eval_store; intros. destruct_c t2; destruct_c op2rtv; destruct_c op2ptr; destruct_c zeq.
  { case_eq (store_helper m lo (Word.unsigned p)
           (weaken_typ (flatten_typ lo tenv (sigma'' rmap t1))
              (flatten_typ lo tenv (sigma'' rmap t2))) r0); intros.
    rewrite H1 in H0. inv H0. eapply store_helper_wf_meta; eauto.
    rewrite H1 in H0. inv H0. }
  { case_eq (store_helper m lo (Word.unsigned p)
    (list_repeat (length (anytobytes lo r0)) Ftyp_int8)
    (anytobytes lo r0)); intros.
    rewrite H1 in H0. inv H0. eapply store_helper_wf_meta; eauto.
    rewrite H1 in H0. inv H0. }
Qed.

(* ---------------------------------------------------------------------- *)
(* Poolcheck helper lemmas *)

Lemma modulus_monotone2 : forall sz1 sz2,
  (sz1 <= sz2)%nat ->
  Word.modulus sz1 <= Word.modulus sz2.
Proof.
  intros. unfold Word.modulus. rewrite two_power_nat_two_p.
  rewrite two_power_nat_two_p. apply two_p_monotone. split; try omega.
  unfold Word.wordsize. apply inj_le. omega.
Qed.

Lemma evalpoolcheck_notstuck : forall fs lo tenv D P env G1 G2 m t r x x2 live rmap HT,
  wf_insn (mk_config fs lo tenv) D P (Insn_poolcheck x2 r t (Op_reg x)) G1 G2 ->
  wf_env (mk_config fs lo tenv) live HT rmap env G1 ->
  wf_mem fs lo tenv live HT m ->
  wf_HT lo HT ->
  wf_rmap D live rmap ->
  (exists v, eval_poolcheck env lo tenv rmap HT r t (Op_reg x) = Some v /\
      wf_value fs lo tenv live HT v (sigma rmap (flatten_typ lo tenv (Typ_ptr t r)))) \/
  (eval_poolcheck env lo tenv rmap HT r t (Op_reg x) = None).
Proof.
  intros. inv H. unfold eval_poolcheck. unfold op2ptr. t_insn_simpl_pro. simpl in *. rewrite H. 
  unfold RT_ptr.
  repeat match goal with
           | [ |- context [ if ?a then _ else _ ] ] => case_eq a; intros; eauto
         end. 
  left. simpl. rewrite Word.repr_unsigned. exists (RT_ptr x1 :: nil). split; auto. 
  repeat econstructor; eauto. 
  destruct zeq; auto. eapply wf_typ_ptr_live; eauto.
  unfold eval_poolcheck. Opaque op2rtv. t_insn_simpl_pro. simpl in *.
  repeat match goal with
           | [ |- context [ if ?a then _ else _ ] ] => case_eq a; intros; eauto
         end. 
  left. exists (RT_ptr (Word.repr (Word.unsigned x1)) :: nil). split; auto.
  repeat econstructor. destruct zeq; auto. eapply wf_typ_ptr_live; eauto.
  simpl. apply modulus_monotone2 in H15.
  rewrite Zmod_small. auto. 
  specialize (Word.unsigned_range x1); intros. unfold WORDSIZE_BITS in *. split; try omega.
  Transparent op2rtv.
Qed.

Lemma evalpoolcheck_notstuckU : forall fs lo tenv D P env G1 G2 m sz r x x2 live rmap HT,
  wf_insn (mk_config fs lo tenv) D P (Insn_poolcheckU x2 r sz (Op_reg x)) G1 G2 ->
  wf_env (mk_config fs lo tenv) live HT rmap env G1 ->
  wf_mem fs lo tenv live HT m ->
  wf_HT lo HT ->
  wf_rmap D live rmap ->
  (exists v, eval_poolcheckU env lo rmap HT r sz (Op_reg x) = Some v /\ 
      wf_value fs lo tenv live HT v (sigma rmap (flatten_typ lo tenv (Typ_ptrU sz r)))) \/
  (eval_poolcheckU env lo rmap HT r sz (Op_reg x) = None).
Proof.
  intros. inv H. unfold eval_poolcheckU. unfold op2ptr. t_insn_simpl_pro. simpl in *. rewrite H.
  unfold RT_ptr.
  repeat match goal with
           | [ |- context [ if ?a then _ else _ ] ] => case_eq a; intros; eauto
         end. 
  left. rewrite Word.repr_unsigned. exists (RT_ptr x1 :: nil). split; auto. repeat econstructor. 
  destruct zeq; auto. eapply wf_typ_ptrU_live; eauto. erewrite bytes_sigma_inv; eauto.

  unfold eval_poolcheckU. unfold op2ptr. t_insn_simpl_pro. simpl in *. rewrite H.
  repeat match goal with
           | [ |- context [ if ?a then _ else _ ] ] => case_eq a; intros; eauto
         end. 
  left. exists (RT_ptr (Word.repr (Word.unsigned x1)) :: nil). split; auto. 
  repeat econstructor. 
  destruct zeq; auto. eapply wf_typ_ptrU_live; eauto. simpl.
  apply modulus_monotone2 in H15.
  rewrite Zmod_small. erewrite bytes_sigma_inv. eauto.
  specialize (Word.unsigned_range x1); intros. unfold WORDSIZE_BITS in *. split; try omega.
Qed.

(* ---------------------------------------------------------------------- *)
(* Free helper lemmas *)
Lemma evalfree_notstuck : forall fs lo tenv D P t o G m env live HT rmap,
  wf_insn (mk_config fs lo tenv) D P (Insn_free t o) G G ->
  wf_env (mk_config fs lo tenv) live HT rmap env G ->
  wf_mem fs lo tenv live HT m ->
  exists m', eval_free env m lo o = Some m' /\
    wf_mem fs lo tenv live HT m'.
Proof.
  intros. unfold eval_free. unfold op2ptr. unfold SVAmem.free.
  Opaque op2rtv.
  inv H; destruct o; t_insn_simpl_pro; eauto.
  Transparent op2rtv.
Qed.

Lemma evalfree_wf_meta : forall m env lo o m' HT,
  wf_mem_metadata HT m ->
  eval_free env m lo o = Some m' ->
  wf_mem_metadata HT m'.
Proof.
  unfold eval_free; intros. destruct_c o. destruct_c (op2rtv (Op_reg i) env).
  destruct_c r. destruct_c r. destruct_c r0.
  eapply free_high_addr_same in H0. unfold wf_mem_metadata in *; crush.
  (* destruct_c r0. eapply free_high_addr_same in H0. unfold wf_mem_metadata in *; crush. *)
  destruct_c (op2rtv (Op_const c) env). destruct_c r. destruct_c r.
  destruct_c r0. eapply free_high_addr_same in H0. unfold wf_mem_metadata in *; crush.
  (* destruct_c r0. eapply free_high_addr_same in H0. unfold wf_mem_metadata in *; crush. *)
Qed.

(* ---------------------------------------------------------------------- *)
(* Getelementptr helper lemmas *)

Lemma wf_val_ptr_mid : forall fs lo tenv t x2 ft lr ls r rmap x0 i HT live,
  wf_tenv tenv ->
  length ls = length lr ->
  Word.unsigned x0 > 0 ->
  flatten_typ lo tenv t <> nil -> 
  TS tenv t ->
  Nenv.find (elt:=ftyps * list rgn * bool) x2 tenv = Some (ft, lr, true) ->
  (nat_of_Z i + walk_offset2 lo ft <
    length (sigma (inst_prgn lr ls) ft))%nat ->
  ftyps_subset (flatten_typ lo tenv t)
  (skipn (nat_of_Z i + walk_offset2 lo ft)
    (sigma (inst_prgn lr ls) ft)) = true ->
  check_HT lo HT (Word.unsigned x0) (alpha rmap r)
  (sigma (inst_prgn lr (map (alpha rmap) ls)) ft) = true ->
  wf_HT_bounds HT ->
  wf_value fs lo tenv live HT (RT_ptr x0 :: nil)
  (Ftyp_ptr (Typ_name x2 (map (alpha rmap) ls)) (alpha rmap r) :: nil) ->
  wf_value fs lo tenv live HT
  (RT_ptr
    (Word.repr
      (Word.unsigned x0 +
        walk_offset lo
        (nat_of_Z i + walk_offset2 lo ft)
        (sigma (inst_prgn lr ls) ft))) :: nil)
  (Ftyp_ptr (sigma'' rmap t) (alpha rmap r) :: nil).
Proof.
  intros. inv H9. inv H15. assert (n = x0). crush. subst. repeat econstructor.   
  destruct zeq; try omega. destruct zeq; auto. destruct zeq; try omega.
  simpl in *. rewrite H4 in *. rewrite <- ftyps_sigma_comm in H18; auto.
  assert (Word.unsigned x0 >= 0). unfold Word.unsigned. unfold Word.intval. 
  destruct x0; auto. omega.
  assert (Word.unsigned x0 > 0). omega.
  specialize (check_HT_mid ((sigma (inst_prgn lr ls) ft)) (nat_of_Z i + walk_offset2 lo ft) (flatten_typ lo tenv t) lo HT (Word.unsigned x0) r rmap H11 H5 H6 H18); intros.
  rewrite flatten_sigma_comm in H12; auto.
  assert (walk_offset lo (nat_of_Z i + walk_offset2 lo ft)
    ((sigma (inst_prgn lr ls) ft)) >= 0).
  apply walk_offset_nonneg. 
  assert (Word.unsigned x0 +
    walk_offset lo (nat_of_Z i + walk_offset2 lo ft)
    ((sigma (inst_prgn lr ls) ft)) <= Word.max_unsigned WORDSIZE_BITS).
  eapply check_HT_bounds in H12; eauto. erewrite walk_offset_sigma_inv in H12; eauto. omega.
  rewrite <- flatten_sigma_comm; auto. eapply sigma_not_nil; eauto.
  rewrite Zmod_small; try omega. auto. split.
  omega. unfold Word.max_unsigned in *. unfold WORDSIZE_BITS in *. omega.
  unfold wf_tenv in H. eapply H in H4; eauto.

  destruct H4; auto.
  Grab Existential Variables.
  apply rmap.
Qed.

Lemma wf_val_ptr_mid2 : forall fs lo tenv t x2 ft lr ls r rmap x0 i HT live,
  wf_tenv tenv ->
  length ls = length lr ->
  Word.unsigned x0 > 0 ->
  flatten_typ lo tenv t <> nil -> 
  TS tenv t ->
  Nenv.find (elt:=ftyps * list rgn * bool) x2 tenv = Some (ft, lr, false) ->
  (nat_of_Z i + walk_offset2 lo ft <
    length (pad_ftyps lo (sigma (inst_prgn lr ls) ft)))%nat ->
  ftyps_subset (flatten_typ lo tenv t)
  (skipn (nat_of_Z i + walk_offset2 lo ft)
    (pad_ftyps lo (sigma (inst_prgn lr ls) ft))) = true ->
  check_HT lo HT (Word.unsigned x0) (alpha rmap r)
  (pad_ftyps lo (sigma (inst_prgn lr (map (alpha rmap) ls)) ft)) = true ->
  wf_HT_bounds HT ->
  wf_value fs lo tenv live HT (RT_ptr x0 :: nil)
  (Ftyp_ptr (Typ_name x2 (map (alpha rmap) ls)) (alpha rmap r) :: nil) ->
  wf_value fs lo tenv live HT
  (RT_ptr
    (Word.repr
      (Word.unsigned x0 +
        walk_offset lo
        (nat_of_Z i + walk_offset2 lo ft)
        (pad_ftyps lo (sigma (inst_prgn lr ls) ft)))) :: nil)
  (Ftyp_ptr (sigma'' rmap t) (alpha rmap r) :: nil).
Proof.
  intros. inv H9. inv H15. assert (n = x0). crush. subst. repeat econstructor. 
  destruct zeq; try omega. destruct zeq; auto. destruct zeq; try omega.
  simpl in *. rewrite H4 in *. rewrite <- ftyps_sigma_comm in H18; auto.
  assert (Word.unsigned x0 >= 0). unfold Word.unsigned. unfold Word.intval. 
  destruct x0; auto. omega.
  assert (Word.unsigned x0 > 0). omega.
  rewrite pad_ftyps_sigma_comm in H18.
  specialize (check_HT_mid (pad_ftyps lo (sigma (inst_prgn lr ls) ft)) (nat_of_Z i + walk_offset2 lo ft) (flatten_typ lo tenv t) lo HT (Word.unsigned x0) r rmap H11 H5 H6 H18); intros.
  rewrite flatten_sigma_comm in H12; auto.
  assert (walk_offset lo (nat_of_Z i + walk_offset2 lo ft)
    (pad_ftyps lo (sigma (inst_prgn lr ls) ft)) >= 0).
  apply walk_offset_nonneg. 
  assert (Word.unsigned x0 +
    walk_offset lo (nat_of_Z i + walk_offset2 lo ft)
    (pad_ftyps lo (sigma (inst_prgn lr ls) ft)) <= Word.max_unsigned WORDSIZE_BITS).
  eapply check_HT_bounds in H12; eauto. 
  rewrite pad_ftyps_sigma_comm in H12. 
  erewrite walk_offset_sigma_inv in H12; eauto. omega.
  rewrite <- flatten_sigma_comm; auto. eapply sigma_not_nil; eauto.
  rewrite Zmod_small; try omega. auto. split.
  rewrite pad_ftyps_sigma_comm in *. omega.
  unfold Word.max_unsigned in *. unfold WORDSIZE_BITS in *. omega.
  unfold wf_tenv in H. eapply H in H4; eauto.
  
  destruct H4; auto.
  Grab Existential Variables.
  apply rmap.
Qed.

Lemma evalgep_prop : forall fs lo tenv D P o G1 live HT rmap env r x2 ls t ft lr p sz pf i,
  wf_env (mk_config fs lo tenv) live HT rmap env G1 ->
  wf_const (mk_config fs lo tenv) D P (Const_int sz pf i) (Ftyp_int sz pf :: nil) ->
  wf_operand (mk_config fs lo tenv) D P G1 o (Ftyp_ptr (Typ_name x2 ls) r :: nil) ->
  ((nat_of_Z (Word.unsigned i) + walk_offset2 lo ft) < length (flatten_typ lo tenv (Typ_name x2 ls)))%nat ->
  ftyps_subset (flatten_typ lo tenv t) (skipn (nat_of_Z (Word.unsigned i) + walk_offset2 lo ft) (flatten_typ lo tenv (Typ_name x2 ls))) = true ->
  TS tenv t ->
  TS tenv (Typ_name x2 ls) ->
  Nenv.find x2 tenv = Some (ft, lr, p) ->
  wf_tenv tenv ->
  wf_HT_bounds HT ->
  flatten_typ lo tenv t <> nil ->
  eval_gep env lo tenv o (Op_const (Const_int sz pf i)) (Typ_ptr (Typ_name x2 ls) r) t = Load_SvaErr \/
  exists rt, eval_gep env lo tenv o (Op_const (Const_int sz pf i)) (Typ_ptr (Typ_name x2 ls) r) t = Load_Val rt /\
    wf_value fs lo tenv live HT rt (sigma rmap (Ftyp_ptr t r :: nil)).
Proof.
  intros. unfold eval_gep. unfold op2ptr. eapply wf_op_val in H1; eauto. t_simp.
  t_dup H10. eapply canonical_form_ptr in H10. t_simp. subst. rewrite H1. unfold RT_ptr. destruct zle; eauto.
  right. simpl in *. rewrite H6 in *. destruct p.
  { exists ((RT_ptr
          (Word.repr
             (Word.unsigned x0 +
              walk_offset lo
                (nat_of_Z (Word.unsigned i) + walk_offset2 lo ft)
                (sigma (inst_prgn lr ls) ft))) :: nil)).
    rewrite rt_ptr_conv.
    split; auto. eapply wf_val_ptr_mid; eauto. 
    rewrite rt_ptr_conv in g. auto. }
  { exists (RT_ptr
          (Word.repr
             (Word.unsigned x0 +
              walk_offset lo
                (nat_of_Z (Word.unsigned i) + walk_offset2 lo ft)
                (pad_ftyps lo (sigma (inst_prgn lr ls) ft)))) :: nil).
    rewrite rt_ptr_conv.
    split; auto. eapply wf_val_ptr_mid2; eauto.
    rewrite rt_ptr_conv in g. auto. }
Qed.

Lemma evalgep_prop2 : forall fs lo tenv D P o G1 live HT rmap env r x2 ls t ft lr x3 p sz pf,
  wf_env (mk_config fs lo tenv) live HT rmap env G1 ->
  wf_operand (mk_config fs lo tenv) D P G1 (Op_reg x3) (Ftyp_int sz pf :: nil) ->
  wf_operand (mk_config fs lo tenv) D P G1 o (Ftyp_ptr (Typ_name x2 ls) r :: nil) ->
  TS tenv t ->
  TS tenv (Typ_name x2 ls) ->
  Nenv.find x2 tenv = Some (ft, lr, p) ->
  wf_tenv tenv ->
  wf_HT_bounds HT ->
  flatten_typ lo tenv t <> nil ->
  eval_gep env lo tenv o (Op_reg x3) (Typ_ptr (Typ_name x2 ls) r) t = Load_SvaErr \/
  (exists rt, eval_gep env lo tenv o (Op_reg x3) (Typ_ptr (Typ_name x2 ls) r) t = Load_Val rt /\
    wf_value fs lo tenv live HT rt (sigma rmap (Ftyp_ptr t r :: nil))).
Proof.
  intros. unfold eval_gep. unfold op2ptr. eapply wf_op_val in H1; eauto. t_simp.
  t_dup H8. eapply canonical_form_ptr in H8. t_simp. subst. rewrite H1. 
  eapply wf_op_val in H0; eauto. t_simp. eapply canonical_form_int in H8.
  t_simp. subst. rewrite H0. unfold RT_ptr. destruct zle; eauto. destruct lt_dec; eauto.
  remember (ftyps_subset (flatten_typ lo tenv t)
         (skipn
            (walk_offset3 lo tenv (nat_of_Z (Word.unsigned x1))
               (Typ_name x2 ls)) (flatten_typ lo tenv (Typ_name x2 ls)))) as Hd.
  destruct Hd; eauto. right.
  exists (RT_ptr
          (Word.repr
             (Word.unsigned x0 +
              walk_offset lo
                (walk_offset3 lo tenv (nat_of_Z (Word.unsigned x1))
                   (Typ_name x2 ls)) (flatten_typ lo tenv (Typ_name x2 ls))))
        :: nil).
  rewrite Word.repr_unsigned. 
  split; auto. simpl in *.  rewrite H4 in *. destruct p. 
  eapply wf_val_ptr_mid; eauto. rewrite rt_ptr_conv in g. auto.
  eapply wf_val_ptr_mid2; eauto. rewrite rt_ptr_conv in g. auto.
Qed.

Lemma check_HT_array' : forall n sz,
  Z.of_nat n < Z.of_nat sz ->
  forall lo HT addr r tenv rmap t D,
  check_HT' lo HT addr r (sigma rmap (flatten_typ lo tenv (Typ_array t sz))) = true ->
  addr > 0 ->
  wf_typ tenv D t ->
  wf_tenv tenv ->
  check_HT' lo HT (addr + array_offset lo (flatten_typ lo tenv t) n)
    r (flatten_typ lo tenv (sigma'' rmap t)) = true.
Proof.
  induction n; intros; auto. 
  rewrite <- flatten_sigma_comm; auto. simpl.
  assert (addr + 0 = addr). omega. rewrite H4. auto.
  apply check_HT_array'' with (sz := sz); auto. omega. 
  eapply wf_typ_TS; eauto.
  simpl.
  assert (addr +
      (size_ftyps lo (flatten_typ lo tenv t) +
       array_offset lo (flatten_typ lo tenv t) n) = addr +
      size_ftyps lo (flatten_typ lo tenv t) +
       array_offset lo (flatten_typ lo tenv t) n). omega.
  rewrite H4. eapply IHn with (sz := (sz - 1)%nat); eauto.
  specialize (NPeano.Nat.lt_add_lt_sub_r n sz 1); intros.
  rewrite <- Nat2Z.inj_lt in H. 
  assert (S n = n + 1)%nat. omega. rewrite H6 in H.
  destruct H5.
  apply H5 in H. apply inj_lt; auto.
  eapply check_HT_array_subset'; eauto.
  specialize (size_ftyps_nonneg lo (flatten_typ lo tenv t)); intros. omega.
Qed.

Lemma check_HT_array_more : forall n sz,
  Z.of_nat n < Z.of_nat sz ->
  forall lo HT addr r tenv rmap t D,
  check_HT lo HT addr r (sigma rmap (flatten_typ lo tenv (Typ_array t sz))) = true ->
  addr > 0 ->
  wf_typ tenv D t ->
  wf_tenv tenv ->
  check_HT lo HT (addr + array_offset lo (flatten_typ lo tenv t) n)
    r (flatten_typ lo tenv (sigma'' rmap t)) = true.
Proof.
  unfold check_HT; intros. destruct_c zeq. omegaContradiction.
  destruct_c zeq. eapply check_HT_array'; eauto.
Qed.

Lemma evalgep_prop3 : forall fs lo tenv D P o G1 live HT rmap env r t sz sz' pf' i,
  wf_env (mk_config fs lo tenv) live HT rmap env G1 ->
  wf_operand (mk_config fs lo tenv) D P G1 o (Ftyp_ptr (Typ_array t sz) r :: nil) ->
  wf_const (mk_config fs lo tenv) D P (Const_int sz' pf' i) (Ftyp_int sz' pf' :: nil) ->
  wf_typ tenv D (Typ_ptr (Typ_array t sz) r) ->
  Word.unsigned i < Z.of_nat sz ->
  wf_tenv tenv ->
  wf_HT_bounds HT ->
  wf_rmap D live rmap ->
  (sz' <= WORDSIZE_BITS)%nat ->
  wf_HT lo HT ->
  eval_gep env lo tenv o (Op_const (Const_int sz' pf' i)) (Typ_ptr (Typ_array t sz) r) t = Load_SvaErr \/
  (exists rt, eval_gep env lo tenv o (Op_const (Const_int sz' pf' i)) (Typ_ptr (Typ_array t sz) r) t = Load_Val rt /\
    wf_value fs lo tenv live HT rt (sigma rmap (Ftyp_ptr t r :: nil))).
Proof.
  Opaque flatten_typ.
  intros. unfold eval_gep. unfold op2ptr. t_insn_simpl_pro. destruct zeq; eauto. right.
  exists (RT_ptr
          (Word.repr
             ((Word.unsigned x0 +
               array_offset lo (flatten_typ lo tenv t)
                 (nat_of_Z (Word.unsigned i))) mod 
              Word.modulus WORDSIZE_BITS)) :: nil).
  split; auto. repeat econstructor. destruct zeq; auto. eapply wf_typ_ptr_live; eauto.
  inv H2. rewrite <- flatten_sigma_comm in *; auto.
  simpl in *. unfold WORDSIZE_BITS. rewrite Zmod_mod.
  t_dup H10. apply check_HT_range_general in H'. rewrite Zmod_small; auto. 
  eapply check_HT_array_more with (n := (nat_of_Z (Word.unsigned i))) in H10; auto.
  rewrite <- flatten_sigma_comm in H10; auto. rewrite nat_of_Z_eq; auto.
  specialize (Word.unsigned_range i); intros. intuition.
  specialize (Word.unsigned_range x0); intros. intuition.
  inv H14. eauto.
  split. 
  assert (array_offset lo (flatten_typ lo tenv t) (nat_of_Z (Word.unsigned i)) >= 0). apply array_offset_nonneg.
  assert (Word.unsigned x0 >= 0).
  specialize (Word.unsigned_range x0); intros. intuition.
  unfold WORDSIZE_BITS in *. omega.
  rewrite size_ftyps_sigma_inv in H'.
  assert(array_offset lo (flatten_typ lo tenv t) (nat_of_Z (Word.unsigned i)) <= size_ftyps lo (flatten_typ lo tenv (Typ_array t sz))).
  apply array_offset_less. 
  rewrite nat_of_Z_same.
  assert (Z.of_nat (Z.to_nat (Word.unsigned i)) < Z.of_nat sz). 
  rewrite Z2Nat.id; auto.
  specialize (Word.unsigned_range i); intros. omega. omega.
  unfold WORDSIZE_BITS in H'. omega.
  specialize (Word.unsigned_range x0); intros. omega.
  specialize (Word.unsigned_range i); intros.
  assert (forall x y,
    (x < y)%nat ->
    two_power_nat x < two_power_nat y).
  intros. rewrite two_power_nat_two_p. rewrite two_power_nat_two_p.
  apply two_p_monotone_strict. split; omega.
  specialize (Word.unsigned_range x0); intros. omega. (* unfold WORDSIZE_BITS. omega. *)
  auto.
  Transparent flatten_typ.
Qed.

Lemma evalgep_prop4 : forall fs lo tenv D P o G1 live HT rmap env r t sz x2 G2 x,
  wf_insn (mk_config fs lo tenv) D P (Insn_gep x (Typ_ptr (Typ_array t sz) r) o t (Op_reg x2)) G1 G2 ->
  wf_env (mk_config fs lo tenv) live HT rmap env G1 ->
  wf_tenv tenv ->
  wf_HT_bounds HT ->
  wf_rmap D live rmap ->
  wf_HT lo HT ->
  eval_gep env lo tenv o (Op_reg x2) (Typ_ptr (Typ_array t sz) r) t = Load_SvaErr \/
  (exists rt, eval_gep env lo tenv o (Op_reg x2) (Typ_ptr (Typ_array t sz) r) t = Load_Val rt /\
    wf_value fs lo tenv live HT rt (sigma rmap (Ftyp_int WORDSIZE_BITS lt_63_MAX_I_BITS :: nil))).
Proof.
  intros. inv H. unfold eval_gep. Opaque op2rtv. t_insn_simpl_pro.
  destruct zeq; eauto. right. t_solve_int_goal. Transparent op2rtv.
Qed.

(* ---------------------------------------------------------------------- *)
(* gep1 helper lemmas *)

Lemma evalgep1_prop : forall fs lo tenv D P o1 o2 t1 r G1 G2 live HT rmap env x,
  wf_insn (mk_config fs lo tenv) D P (Insn_gep1 x (Typ_ptr t1 r) o1 o2) G1 G2 ->
  wf_env (mk_config fs lo tenv) live HT rmap env G1 ->
  wf_HT lo HT ->
  wf_tenv tenv ->
  eval_gep1 env lo tenv o1 o2 (Typ_ptr t1 r) = Load_SvaErr \/
  (exists rt, eval_gep1 env lo tenv o1 o2 (Typ_ptr t1 r) = Load_Val rt /\
    wf_value fs lo tenv live HT rt (sigma rmap (Ftyp_int WORDSIZE_BITS lt_63_MAX_I_BITS :: nil))).
Proof.
  intros. unfold eval_gep1. inv H; t_insn_simpl_pro.
  { right. t_solve_int_goal. }
  { right. t_solve_int_goal. }
Qed.

Lemma evalgep1_prop2 : forall fs lo tenv D P o1 o2 sz pf G1 G2 live HT rmap env x,
  wf_insn (mk_config fs lo tenv) D P (Insn_gep1 x (Typ_int sz pf) o1 o2) G1 G2 ->
  wf_env (mk_config fs lo tenv) live HT rmap env G1 ->
  wf_HT lo HT ->
  wf_tenv tenv ->
  eval_gep1 env lo tenv o1 o2 (Typ_int sz pf) = Load_SvaErr \/
  (exists rt, eval_gep1 env lo tenv o1 o2 (Typ_int sz pf) = Load_Val rt /\
    wf_value fs lo tenv live HT rt (sigma rmap (Ftyp_int WORDSIZE_BITS lt_63_MAX_I_BITS :: nil))).
Proof.
  intros. unfold eval_gep1. inv H; t_insn_simpl_pro. right. t_solve_int_goal. 
Qed.

(* ---------------------------------------------------------------------- *)
(* gepU helper lemmas *)

Lemma evalgepU_prop : forall fs lo tenv D P o G1 live HT rmap env r sz sz' pf' i sz'',
  wf_operand (mk_config fs lo tenv) D P G1 o (Ftyp_ptrU sz'' r :: nil) ->
  wf_operand (mk_config fs lo tenv) D P G1 (Op_const (Const_int sz' pf' i)) (Ftyp_int sz' pf' :: nil) ->
  wf_typ tenv D (Typ_ptrU sz r) ->
  Z.of_nat sz <= Z.of_nat sz'' < Word.modulus WORDSIZE_BITS ->
  (* wf_insn (mk_config fs lo tenv) D P (Insn_gepU x (Typ_ptrU sz r) o (Op_const (Const_int sz' pf' i))) G1 G2 -> *)
  wf_env (mk_config fs lo tenv) live HT rmap env G1 ->
  wf_HT lo HT ->
  wf_rmap D live rmap ->
  eval_gepU env o (Op_const (Const_int sz' pf' i)) (Typ_ptrU sz r) = Load_SvaErr \/
  (exists rt, eval_gepU env o (Op_const (Const_int sz' pf' i)) (Typ_ptrU sz r) = Load_Val rt /\
    wf_value fs lo tenv live HT rt (sigma rmap (Ftyp_ptrU (sz - nat_of_Z (Word.unsigned i)) r :: nil))).
Proof.
  intros. (* assert (i = i1). crush. subst. *) unfold eval_gepU. unfold op2ptr. t_insn_simpl_pro.

  destruct zle; eauto. right.
  exists (RT_ptr
          (Word.repr
             ((Word.unsigned x + Word.unsigned i)
              mod Word.modulus WORDSIZE_BITS)) :: nil).
  split; auto. repeat econstructor. destruct zeq; eauto.
  eapply wf_typ_ptrU_live; eauto. simpl.

  unfold WORDSIZE_BITS in *. rewrite Zmod_mod.
  destruct (zlt (Word.unsigned i) (Z.of_nat sz)).

  assert (Word.unsigned x + Word.unsigned i < Word.modulus WORDSIZE_BITS).
  eapply check_HT_range; eauto. specialize (Word.unsigned_range x); intros.
  unfold WORDSIZE_BITS in *. omega.
  split; auto. omega. unfold WORDSIZE_BITS in *.
  unfold Word.modulus in *. unfold Word.wordsize in *. unfold two_power_nat in *.
  unfold shift_nat in *. unfold nat_iter in *. omega.
  unfold WORDSIZE_BITS in *. rewrite Zmod_small; auto.

  assert (Z.of_nat (nat_of_Z (Word.unsigned i)) = Word.unsigned i).
  specialize (Word.unsigned_range i); intros. rewrite nat_of_Z_eq; auto. omega.
  specialize (check_HT_mid_bytes sz (Word.unsigned x) (nat_of_Z (Word.unsigned i)) lo HT (alpha rmap r) g); intros. rewrite nat_of_Z_eq in H10; auto. apply H10. omega.
  rewrite bytes_sigma_inv with (rmap := rmap) in *. eapply check_HT_subset_bytes; eauto.
  omega.
  specialize (Word.unsigned_range i); intros; omega.
  destruct (zeq (Word.unsigned i) (Z.of_nat sz)). 
  
  assert (sz - (nat_of_Z (Word.unsigned i)) = 0)%nat. rewrite e.
  rewrite Z_of_nat_eq. omega. rewrite H7. simpl. 
  unfold check_HT. destruct zeq; auto.

  assert (Word.unsigned i > Z.of_nat sz). omega.
  assert (sz - nat_of_Z (Word.unsigned i) = 0)%nat.
  apply not_le_minus_0. unfold not. intros. 
  assert (Z.of_nat (nat_of_Z (Word.unsigned i)) <= Z.of_nat sz). omega.
  rewrite nat_of_Z_eq in H10; auto. omega. rewrite H9. simpl.
  unfold check_HT. destruct zeq; auto.
Qed.

Lemma evalgepU_prop2 : forall fs lo tenv D P o G1 G2 live HT rmap env r x sz x2,
  wf_insn (mk_config fs lo tenv) D P (Insn_gepU x (Typ_ptrU sz r) o (Op_reg x2)) G1 G2 ->
  wf_env (mk_config fs lo tenv) live HT rmap env G1 ->
  wf_rmap D live rmap ->
  eval_gepU env o (Op_reg x2) (Typ_ptrU sz r) = Load_SvaErr \/
  (exists rt, eval_gepU env o (Op_reg x2) (Typ_ptrU sz r) = Load_Val rt /\
    wf_value fs lo tenv live HT rt (sigma rmap (Ftyp_ptrU 0 r :: nil))).
Proof.
  intros. inv H. unfold eval_gepU. unfold op2ptr. t_insn_simpl_pro. simpl in *. rewrite H. 
  destruct zle; eauto. right.
  exists ((RT_ptr
          (Word.repr
             ((Word.unsigned x0 + Word.unsigned x3)
              mod Word.modulus WORDSIZE_BITS)) :: nil)).
  split; auto. repeat econstructor. destruct zeq; auto. eapply wf_typ_ptrU_live; eauto.
  simpl. unfold check_HT. destruct zeq; auto. 
  unfold eval_gepU. unfold op2ptr. t_insn_simpl_pro. simpl in *. rewrite H. 
  destruct zle; eauto. right.
  exists ((RT_ptr
          (Word.repr
             ((Word.unsigned x0 + Word.unsigned x3)
              mod Word.modulus WORDSIZE_BITS)) :: nil)).
  split; auto. repeat econstructor. destruct zeq; auto. eapply wf_typ_ptrU_live; eauto.
  simpl. unfold check_HT. destruct zeq; auto. 
Qed.

Lemma evalgepU_prop3 : forall fs lo tenv D P o1 o2 G1 G2 live HT rmap env x sz pf,
  wf_insn (mk_config fs lo tenv) D P (Insn_gepU x (Typ_int sz pf) o1 o2) G1 G2 ->
  wf_env (mk_config fs lo tenv) live HT rmap env G1 ->
  wf_rmap D live rmap ->
  eval_gepU env o1 o2 (Typ_int sz pf) = Load_SvaErr \/
  (exists rt, eval_gepU env o1 o2 (Typ_int sz pf) = Load_Val rt /\
    wf_value fs lo tenv live HT rt (sigma rmap (Ftyp_int WORDSIZE_BITS lt_63_MAX_I_BITS :: nil))).
Proof.
  intros. inv H. unfold eval_gepU. unfold op2ptr. t_insn_simpl_pro. destruct zle; eauto.
  right.
  exists (RT_ptr
          (Word.repr
             ((Word.unsigned x0 + Word.unsigned x2)
              mod Word.modulus WORDSIZE_BITS)) :: nil).
  split; auto. repeat econstructor.
  unfold eval_gepU. t_insn_simpl_pro. destruct zle; eauto.
  right.
  exists (RT_ptr
          (Word.repr
             ((Word.unsigned x0 + Word.unsigned x2)
              mod Word.modulus WORDSIZE_BITS)) :: nil).
  split; auto. repeat econstructor.
Qed.

Lemma evalgepU_prop4 : forall fs lo tenv D P G1 live HT rmap env o1 o2 sz1 pf1 sz2 pf2 sz3 r,
  wf_operand (mk_config fs lo tenv) D P G1 o1 (Ftyp_int sz1 pf1 :: nil) ->
  wf_operand (mk_config fs lo tenv) D P G1 o2 (Ftyp_int sz2 pf2 :: nil) ->
  wf_typ tenv D (Typ_ptrU sz3 r) ->
  wf_env (mk_config fs lo tenv) live HT rmap env G1 ->
  wf_rmap D live rmap ->
  eval_gepU env o1 o2 (Typ_ptrU sz3 r) = Load_SvaErr \/
  (exists rt, eval_gepU env o1 o2 (Typ_ptrU sz3 r) = Load_Val rt /\
    wf_value fs lo tenv live HT rt (sigma rmap (Ftyp_ptrU 0 r :: nil))).
Proof.
  intros. unfold eval_gepU. unfold op2ptr. t_insn_simpl_pro. destruct zle; eauto.
  right.
  exists (RT_ptr
          (Word.repr
             ((Word.unsigned x + Word.unsigned x1)
              mod Word.modulus WORDSIZE_BITS)) :: nil).
  split; auto. repeat econstructor.
  unfold eval_gepU. t_insn_simpl_pro. destruct zeq; eauto. eapply wf_typ_ptrU_live; eauto.
  simpl. unfold check_HT. destruct zeq; auto. 
Qed.

(* ---------------------------------------------------------------------- *)
(* To integer conversion helper lemmas *)

Lemma evaliconv_prop : forall env D P HT G1 G2 x c o lo fs live rmap tenv t sz pf,
  wf_insn (mk_config fs lo tenv) D P (Insn_iconv x c t o (Typ_int sz pf)) G1 G2 ->
  wf_env (mk_config fs lo tenv) live HT rmap env G1 ->
  exists v, 
    eval_iconv env c o (Typ_int sz pf) = Some v /\
    wf_value fs lo tenv live HT v (Ftyp_int sz pf :: nil).
Proof.
  intros; inv H; unfold eval_iconv; destruct c; destruct t; try contradiction; t_insn_simpl_pro;
    repeat match goal with
             | [ H: (63 < MAX_I_BITS)%nat |- _ ] =>
               assert (pf = lt_63_MAX_I_BITS) by apply proof_irr; subst
             | [ H: (31 < MAX_I_BITS)%nat |- _ ] =>
               assert (pf = lt_31_MAX_I_BITS) by apply proof_irr; subst
             | [ |- exists v, Some (RT_int ?sz ?pf ?i :: nil) = Some v /\ _ ] =>
               exists (RT_int sz pf i :: nil); split; auto; eapply wf_val_int_any
           end.
Qed.

(* ---------------------------------------------------------------------- *)
(* To float conversion helper lemmas *)

Lemma evalfconv_prop : forall env D P HT G1 G2 x c o lo fs live rmap tenv t,
  wf_insn (mk_config fs lo tenv) D P (Insn_fconv x c t o Typ_float) G1 G2 ->
  wf_env (mk_config fs lo tenv) live HT rmap env G1 ->
  exists v, 
    eval_fconv env c o Typ_float = Some v /\
    wf_value fs lo tenv live HT v (Ftyp_float :: nil).
Proof.
  intros; inv H; unfold eval_fconv; destruct c; destruct t; try contradiction; t_insn_simpl_pro; try t_solve_float_goal.
Qed.

Lemma evalfconv_prop2 : forall env D P HT G1 G2 x c o lo fs live rmap tenv t,
  wf_insn (mk_config fs lo tenv) D P (Insn_fconv x c t o Typ_double) G1 G2 ->
  wf_env (mk_config fs lo tenv) live HT rmap env G1 ->
  exists v, 
    eval_fconv env c o Typ_double = Some v /\
    wf_value fs lo tenv live HT v (Ftyp_double :: nil).
Proof.
  intros; inv H; unfold eval_fconv; destruct c; destruct t; try contradiction; t_insn_simpl_pro; try t_solve_float_goal.
Qed.

(* ---------------------------------------------------------------------- *)
(* Bitcast helper lemmas *)

Lemma evalbitcast_prop : forall lo fs tenv D P x t1 t2 r o env live HT rmap G1 G2,
  wf_insn (mk_config fs lo tenv) D P (Insn_bitcast x (Typ_ptr t1 r) o (Typ_ptr t2 r)) G1 G2 ->
  wf_env (mk_config fs lo tenv) live HT rmap env G1 ->
  wf_rmap D live rmap ->
  wf_tenv tenv ->
  exists v, 
    eval_bitcast env (Typ_ptr t1 r) (Typ_ptr t2 r) o = Some v /\
    wf_value fs lo tenv live HT v (sigma rmap (Ftyp_ptr t2 r :: nil)).
Proof.
  intros; inv H; unfold eval_bitcast; t_insn_simpl_pro; simpl in *; 
    match goal with
      | [ |- exists v, Some (RT_ptr ?addr :: nil) = Some v /\ _ ] =>
        exists (RT_ptr addr :: nil); split; auto
    end.
  repeat econstructor.
  { destruct zeq; auto. eapply wf_typ_ptr_live; eauto. }
  { inv H15. inv H16. rewrite <- flatten_sigma_comm in *; auto. rewrite Word.repr_unsigned. 
    eapply check_HT_subset; eauto. }
Qed.

Lemma evalbitcast_propU : forall lo fs tenv D P x sz1 sz2 r o env live HT rmap G1 G2,
  wf_insn (mk_config fs lo tenv) D P (Insn_bitcast x (Typ_ptrU sz1 r) o (Typ_ptrU sz2 r)) G1 G2 ->
  wf_env (mk_config fs lo tenv) live HT rmap env G1 ->
  wf_rmap D live rmap ->
  wf_tenv tenv ->
  exists v, 
    eval_bitcast env (Typ_ptrU sz1 r) (Typ_ptrU sz2 r) o = Some v /\
    wf_value fs lo tenv live HT v (sigma rmap (Ftyp_ptrU sz2 r :: nil)).
Proof.
  intros; inv H; unfold eval_bitcast; t_insn_simpl_pro; simpl in *; 
    match goal with
      | [ |- exists v, Some (RT_ptr ?addr :: nil) = Some v /\ _ ] =>
        exists (RT_ptr addr :: nil); split; auto
    end.
  repeat econstructor.
  { destruct zeq; auto. eapply wf_typ_ptrU_live; eauto. }
  { rewrite bytes_sigma_inv with (rmap := rmap) in *. rewrite Word.repr_unsigned. 
    eapply check_HT_subset_bytes; eauto. }
Qed.

(* ---------------------------------------------------------------------- *)
(* Ptrtoint helper lemmas *)

Lemma evalptrtoint_prop : forall lo fs tenv D P x t2 r o G1 G2 env HT live rmap,
  wf_insn (mk_config fs lo tenv) D P (Insn_ptrtoint x (Typ_ptr t2 r) o Typ_int64) G1 G2 ->
  wf_env (mk_config fs lo tenv) live HT rmap env G1 ->
  exists v, 
    eval_ptrtoint env x o (Typ_ptr t2 r) Typ_int64 = Some v /\
    wf_value fs lo tenv live HT v (Ftyp_int64 :: nil).
Proof.
  intros; inv H; unfold eval_ptrtoint; t_insn_simpl_pro; t_solve_int_goal.
Qed.

Lemma evalptrtoint_propU : forall lo fs tenv D P x sz r o G1 G2 env HT live rmap,
  wf_insn (mk_config fs lo tenv) D P (Insn_ptrtoint x (Typ_ptrU sz r) o Typ_int64) G1 G2 ->
  wf_env (mk_config fs lo tenv) live HT rmap env G1 ->
  exists v, 
    eval_ptrtoint env x o (Typ_ptrU sz r) Typ_int64 = Some v /\
    wf_value fs lo tenv live HT v (Ftyp_int64 :: nil).
Proof.
  intros; inv H; unfold eval_ptrtoint; t_insn_simpl_pro; t_solve_int_goal.
Qed.

(* ---------------------------------------------------------------------- *)
(* Inttoptr helper lemmas *)

Lemma evalinttoptr_prop : forall lo fs tenv D P x t2 r o G1 G2 env live HT rmap,
  wf_insn (mk_config fs lo tenv) D P (Insn_inttoptr x Typ_int64 o (Typ_ptr t2 r)) G1 G2 ->
  wf_env (mk_config fs lo tenv) live HT rmap env G1 ->
  (exists v, 
    eval_inttoptr env lo tenv live rmap HT o (Typ_ptr t2 r) = Load_Val v /\
    wf_value fs lo tenv live HT v (sigma rmap (Ftyp_ptr t2 r :: nil))
  ) \/
  (eval_inttoptr env lo tenv live rmap HT o (Typ_ptr t2 r) = Load_SvaErr).
Proof.
  intros; inv H; unfold eval_inttoptr; simpl in *; unfold Ftyp_int64 in *; t_insn_simpl_pro.
  destruct in_dec; auto.
  remember (check_HT lo HT (Word.unsigned x1) (alpha rmap r)
            (flatten_typ lo tenv (sigma'' rmap t2))) as Hd.
  destruct Hd; auto.
  left. exists (RT_ptr x1 :: nil). 
  split; auto. repeat econstructor; auto. destruct zeq; auto.
Qed.

Lemma evalinttoptr_propU : forall lo fs tenv D P x sz r o G1 G2 env live HT rmap,
  wf_insn (mk_config fs lo tenv) D P (Insn_inttoptr x Typ_int64 o (Typ_ptrU sz r)) G1 G2 ->
  wf_env (mk_config fs lo tenv) live HT rmap env G1 ->
  (exists v, 
    eval_inttoptr env lo tenv live rmap HT o (Typ_ptrU sz r) = Load_Val v /\
    wf_value fs lo tenv live HT v (sigma rmap (Ftyp_ptrU sz r :: nil))
  ) \/
  (eval_inttoptr env lo tenv live rmap HT o (Typ_ptrU sz r) = Load_SvaErr).
Proof.
  intros; inv H; unfold eval_inttoptr; simpl in *; unfold Ftyp_int64 in *; t_insn_simpl_pro.
  destruct in_dec; auto.
  remember (check_HT lo HT (Word.unsigned x1) (alpha rmap r)
            (sigma rmap (list_repeat sz Ftyp_int8))) as Hd.
  destruct Hd; auto.
  left. exists (RT_ptr x1 :: nil). rewrite <- bytes_sigma_inv in HeqHd. 
  split; auto. repeat econstructor; auto. destruct zeq; auto.
Qed.

(* ---------------------------------------------------------------------- *)
(** * Execution Context/Stack Projection Lemmas *)

Lemma wf_ec_proj_fun : forall fs lo tenv D G f b insns t env HT rmap_e rmap_b rgns live,
  wf_ec (mk_config fs lo tenv) D (mk_ec f b insns t env HT rmap_e rmap_b rgns live) G ->
  lookup_fun (f_lab f) fs = Some f.
Proof.
  unfold wf_ec; crush.
Qed.

Lemma wf_ec_stk_proj_top : forall C FD FT ec D1 D2 G stk lsD lsG,
  wf_ec_stk C FD FT ec (D1,D2) G stk lsD lsG ->
  wf_ec C D2 ec G.
Proof.
  intros. inv H; eauto.
Qed.

Lemma wf_ec_stk_proj_env : forall fs lo tenv FD FT f b insns t env HT rmap_e rmap_b rgns live D1 D2 G stk lsD lsG,
  wf_ec_stk (mk_config fs lo tenv) FD FT (mk_ec f b insns t env HT rmap_e rmap_b rgns live) (D1,D2) G stk lsD lsG ->
  wf_env (mk_config fs lo tenv) live HT rmap_b env G.
Proof.
  intros. inv H. inv H10. t_simp; crush. inv H2. t_simp; crush.
Qed.

Lemma wf_ec_stk_proj_HT : forall fs lo tenv FD FT f b insns t env HT rmap_e rmap_b rgns live D1 D2 G stk lsD lsG,
  wf_ec_stk (mk_config fs lo tenv) FD FT (mk_ec f b insns t env HT rmap_e rmap_b rgns live) (D1,D2) G stk lsD lsG ->
  wf_HT lo HT.
Proof.
  intros. inv H. inv H10. t_simp; crush. inv H2. t_simp; crush.
Qed.

Lemma wf_ec_stk_proj_HT_bounds : forall fs lo tenv FD FT f b insns t env HT rmap_e rmap_b rgns live D1 D2 G stk lsD lsG,
  wf_ec_stk (mk_config fs lo tenv) FD FT (mk_ec f b insns t env HT rmap_e rmap_b rgns live) (D1,D2) G stk lsD lsG ->
  wf_HT_bounds HT.
Proof.
  intros. inv H. inv H10. t_simp; crush. inv H2. t_simp; crush.
Qed.

Lemma wf_ec_stk_proj_rmapb : forall fs lo tenv FD FT f b insns t env HT rmap_e rmap_b rgns live D1 D2 G stk lsD lsG,
  wf_ec_stk (mk_config fs lo tenv) FD FT (mk_ec f b insns t env HT rmap_e rmap_b rgns live) (D1,D2) G stk lsD lsG ->
  wf_rmap D2 live rmap_b.
Proof.
  intros. inv H. inv H10. t_simp; crush. inv H2. t_simp; crush.
Qed.

(* ---------------------------------------------------------------------- *)
(** * Execution Context/Stack Lemmas *)

Lemma lst_comp : forall insns' x i (insns: list insn),
  insns = x ++ i :: insns' ->
  exists ls, insns = ls ++ insns'.
Proof.
  intros. assert (i::insns = (i::nil) ++ insns) by crush.
  exists (x ++ i :: nil). crush.
Qed.
Hint Resolve lst_comp : ec_ext_db.

Lemma wf_call_ortho : forall C D1 D2 P G f b insns insns' t env env' ec HT rmap_e rmap_b rgns live,
  wf_call C D1 D2 P G (mk_ec f b insns t env HT rmap_e rmap_b rgns live) ec ->
  wf_call C D1 D2 P G (mk_ec f b insns' t env' HT rmap_e rmap_b rgns live) ec.
Proof.
  intros. inv H. econstructor; eauto. eapply wf_call_return_void; eauto.
Qed.
Hint Resolve wf_call_ortho : ec_ext_db.

Lemma wf_ec_insns_dec : forall C D f b i insns t env HT rmap_e rmap_b rgns live G,
  wf_ec C D (mk_ec f b (i::insns) t env HT rmap_e rmap_b rgns live) G ->
  wf_ec C D (mk_ec f b insns t env HT rmap_e rmap_b rgns live) G.
Proof.
  unfold wf_ec; simpl; intros. t_simp. subst.
  exists f. exists b. repeat (split; eauto with ec_ext_db).
Qed.
Hint Resolve wf_ec_insns_dec : ec_ext_db.

Lemma wf_ec_stk_insns_dec : forall FD FT D G lsD lsG fs lo tenv f b i insns t stk HT env rmap_e rmap_b rgns live,
  wf_ec_stk (mk_config fs lo tenv) FD FT (mk_ec f b (i :: insns) t HT env rmap_e rmap_b rgns live) D G stk lsD lsG ->
  wf_ec_stk (mk_config fs lo tenv) FD FT (mk_ec f b insns t HT env rmap_e rmap_b rgns live) D G stk lsD lsG.
Proof.
  intros. inv H; econstructor; eauto with ec_ext_db.
Qed.
Hint Resolve wf_ec_stk_insns_dec : ec_ext_db.

Hint Resolve wf_env_val_ext : ec_ext_db.
Lemma wf_ec_env_val_ext : forall fs lo tenv D f b insns t env HT rmap_e rmap_b rgns live G ft rt x,
  wf_ec (mk_config fs lo tenv) D (mk_ec f b insns t env HT rmap_e rmap_b rgns live) G ->
  wf_value fs lo tenv live HT rt (sigma rmap_b ft) ->
  wf_ec (mk_config fs lo tenv) D (mk_ec f b insns t (Nenv.add x rt env) HT rmap_e rmap_b rgns live) (Nenv.add x ft G).
Proof.
  unfold wf_ec; simpl; intros. t_simp. subst.
  exists f. exists b. repeat (split; eauto with ec_ext_db).
Qed.
Hint Resolve wf_ec_env_val_ext : ec_ext_db.

Lemma wf_ec_stk_env_ext : forall FD FT D1 D2 G lsD lsG fs lo tenv f b insns t stk env HT rmap_e rmap_b rgns live x rt ft,
  wf_ec_stk (mk_config fs lo tenv) FD FT (mk_ec f b insns t env HT rmap_e rmap_b rgns live) (D1,D2) G stk lsD lsG ->
  wf_value fs lo tenv live HT rt (sigma rmap_b ft) ->
  wf_ec_stk (mk_config fs lo tenv) FD FT (mk_ec f b insns t (Nenv.add x rt env) HT rmap_e rmap_b rgns live) (D1,D2) (Nenv.add x ft G) stk lsD lsG.
Proof.
  intros. inv H; econstructor; eauto with ec_ext_db.
Qed.
Hint Resolve wf_ec_stk_env_ext : ec_ext_db.

Lemma wf_ec_G_ext : forall fs lo tenv D f b insns t env HT rmap_e rmap_b rgns live G rt ft x,
  wf_ec (mk_config fs lo tenv) D (mk_ec f b insns t env HT rmap_e rmap_b rgns live) G ->
  Nenv.find x env = Some rt ->
  wf_value fs lo tenv live HT rt (sigma rmap_b ft) ->
  wf_ec (mk_config fs lo tenv) D (mk_ec f b insns t env HT rmap_e rmap_b rgns live) (Nenv.add x ft G).
Proof.
  unfold wf_ec; simpl; intros. t_simp. subst.
  exists f. exists b. repeat (split; eauto with ec_ext_db).
  unfold wf_env in *; intros. 
  destruct (eq_nat_dec x0 x); subst.
  { rewrite NFacts.add_eq_o in *; eauto. inv H. eauto. }
  { rewrite NFacts.add_neq_o in *; eauto. }
Qed.
Hint Resolve wf_ec_G_ext : ec_ext_db.

Lemma wf_ec_stk_G_ext : forall FD FT D1 D2 G lsD lsG fs lo tenv f b insns t stk env HT rmap_e rmap_b rgns live x rt ft,
  wf_ec_stk (mk_config fs lo tenv) FD FT (mk_ec f b insns t env HT rmap_e rmap_b rgns live) (D1,D2) G stk lsD lsG ->
  Nenv.find x env = Some rt ->
  wf_value fs lo tenv live HT rt (sigma rmap_b ft) ->
  wf_ec_stk (mk_config fs lo tenv) FD FT (mk_ec f b insns t env HT rmap_e rmap_b rgns live) (D1,D2) (Nenv.add x ft G) stk lsD lsG.
Proof.
  intros. inv H; econstructor; eauto with ec_ext_db.
Qed.

(* ---------------------------------------------------------------------- *)
(** * Preservation *)

Ltac t_pres_eval_init :=
  match goal with
    | [ H: wf_insn _ _ _ _ _ _ |- _ ] => inversion H; subst
  end;
  match goal with
    | [ H: wf_ec_stk _ _ _ _ _ _ _ _ _ |- _ ] =>
      t_dup H
  end;
  match goal with
    | [ H: wf_ec_stk _ _ _ _ _ _ _ _ _ |- _ ] =>
      apply wf_ec_stk_proj_env in H
  end;
  match goal with
    | [ H: wf_ec_stk _ _ _ _ _ _ _ _ _ |- _ ] =>
      t_dup H
  end;
  match goal with
    | [ H: wf_ec_stk _ _ _ _ _ _ _ _ _ |- _ ] =>
      apply wf_ec_stk_proj_HT in H
  end;
  match goal with
    | [ H: wf_ec_stk _ _ _ _ _ _ _ _ _ |- _ ] =>
      t_dup H
  end;
  match goal with
    | [ H: wf_ec_stk _ _ _ _ _ _ _ _ _ |- _ ] =>
      apply wf_ec_stk_proj_rmapb in H
  end;
  match goal with
    | [ H: wf_ec_stk _ _ _ _ _ _ _ _ _ |- _ ] =>
      t_dup H
  end;
  match goal with
    | [ H: wf_ec_stk _ _ _ _ _ _ _ _ _ |- _ ] =>
      apply wf_ec_stk_proj_HT_bounds in H
  end.

Hint Resolve wf_ec_stk_env_ext : pres_eval_db.
Hint Resolve wf_ec_stk_insns_dec : pres_eval_db.
Hint Resolve wf_ec_stk_G_ext : pres_eval_db.

(* By induction on the instruction sequence *)
Theorem preservation_eval : forall lo fs tenv m stk f b env HT rmap_e rmap_b rgns live insns t,
  wf_ms (mk_config fs lo tenv) (mk_mstate m (mk_ec f b insns t env HT rmap_e rmap_b rgns live) stk) ->
  wf_comp (mk_config fs lo tenv) (eval_blk lo tenv insns (mk_mstate m (mk_ec f b insns t env HT rmap_e rmap_b rgns live) stk)).
Proof.
  intros. inv H.
  generalize dependent m. generalize dependent env.
  remember (mk_config fs lo tenv) as C. remember (b_lab b) as l. 
  remember (f_body f) as bs. induction H17; subst.

  (* Base case: non-deterministic *)
  { intros. econstructor; simpl in *. econstructor; eauto. }

  (* Base case: terminator *)
  { intros. econstructor; simpl in *. econstructor; eauto. }

  (* Inductive case: sequence of instructions *)
  { simpl. destruct i; intros; t_pres_eval_init. 

    (* BINOP Case *)
    eapply evalbinop_prop with (bop := b0) (o1 := o) (o2 := o0) in H10; eauto. 
    t_simp. rewrite H0. apply IHwf_insns_ndterm; eauto with pres_eval_db.

    (* FBINOP Case *)
    eapply evalfbinop_prop with (c := f0) (o1 := o) (o2 := o0) in H7; eauto. 
    t_simp. rewrite H0. apply IHwf_insns_ndterm; eauto with pres_eval_db.

    eapply evalfbinop_prop2 with (c := f0) (o1 := o) (o2 := o0) in H7; eauto. 
    t_simp. rewrite H0. apply IHwf_insns_ndterm; eauto with pres_eval_db.
 
    (* ICMP Case *)
    eapply evalicmp_prop in H; eauto. t_simp. rewrite H.
    apply IHwf_insns_ndterm; eauto with pres_eval_db.

    (* FCMP Case *)
    eapply evalfcmp_prop in H; eauto. t_simp. rewrite H.
    apply IHwf_insns_ndterm; eauto with pres_eval_db.

    (* Select Case *)
    eapply evalselect_prop in H; eauto. t_simp. rewrite H.
    apply IHwf_insns_ndterm; eauto with pres_eval_db.

    (* LOAD case *)
    (* success *)
    t_dup H. eapply evalload_prop in H; eauto. 
    destruct H. t_simp. rewrite H.
    apply IHwf_insns_ndterm; simpl; eauto with pres_eval_db.
    
    (* sva error *)
    crush.

    t_dup H. eapply evalload_propU in H; eauto. 
    destruct H. t_simp. rewrite H.
    apply IHwf_insns_ndterm; simpl; eauto with pres_eval_db.
    crush.

    t_dup H. eapply evalload_propU2 in H; eauto. 
    destruct H. t_simp. rewrite H.
    apply IHwf_insns_ndterm; simpl; eauto with pres_eval_db.
    crush.

    t_dup H. eapply evalload_propU3 in H; eauto. 
    destruct H. t_simp. rewrite H.
    apply IHwf_insns_ndterm; simpl; eauto with pres_eval_db.
    crush.

    t_dup H. eapply evalload_propU4 in H; eauto. 
    destruct H. t_simp. rewrite H.
    apply IHwf_insns_ndterm; simpl; eauto with pres_eval_db.
    crush.

    (* STORE case *)
    (* success *)
    t_dup H. eapply evalstore_prop in H; eauto.
    destruct H. t_simp. rewrite H.
    apply IHwf_insns_ndterm; eauto with pres_eval_db. 
    eapply evalstore_wf_meta; eauto.

    (* sva error *)
    crush.

    t_dup H. eapply evalstore_propU in H; eauto.
    destruct H. t_simp. rewrite H.
    apply IHwf_insns_ndterm; eauto with pres_eval_db. 
    eapply evalstore_wf_meta; eauto.
    crush.

    (* poolcheck case *)
    t_dup H. eapply evalpoolcheck_notstuck in H; eauto.
    destruct H. t_simp. rewrite H. apply IHwf_insns_ndterm; eauto with pres_eval_db. 
    rewrite H. auto.

    t_dup H. eapply evalpoolcheck_notstuck in H; eauto.
    destruct H. t_simp. rewrite H. apply IHwf_insns_ndterm; eauto with pres_eval_db. 
    rewrite H. auto.

    (* FREE case *)
    eapply evalfree_notstuck in H; eauto. t_simp. rewrite H. 
    apply IHwf_insns_ndterm; eauto with pres_eval_db.
    eapply evalfree_wf_meta; eauto.

    eapply evalfree_notstuck in H; eauto. t_simp. rewrite H. 
    apply IHwf_insns_ndterm; eauto with pres_eval_db.
    eapply evalfree_wf_meta; eauto.

    eapply evalfree_notstuck in H; eauto. t_simp. rewrite H. 
    apply IHwf_insns_ndterm; eauto with pres_eval_db.
    eapply evalfree_wf_meta; eauto.

    eapply evalfree_notstuck in H; eauto. t_simp. rewrite H. 
    apply IHwf_insns_ndterm; eauto with pres_eval_db.
    eapply evalfree_wf_meta; eauto.

    (* GEP case *)
    eapply evalgep_prop with (t := t1) in H25; eauto. destruct H25. crush.
    t_simp. simpl in *. rewrite H0.
    apply IHwf_insns_ndterm; eauto with pres_eval_db. simpl in *. rewrite H15 in *.
    auto. simpl in *. rewrite H15 in *. auto.
    eapply wf_typ_TS; eauto. inv H28; auto.

    (* GEP case2 *)
    eapply evalgep_prop2 with (t := t1) in H23; eauto. destruct H23. crush.
    t_simp. simpl in *. rewrite H0.
    apply IHwf_insns_ndterm; eauto with pres_eval_db.
    eapply wf_typ_TS; eauto. inv H25; auto.

    eapply evalgep_prop3 in H8; eauto. t_simp. destruct H8. rewrite H2.
    constructor. t_simp. rewrite H2.
    apply IHwf_insns_ndterm; eauto with pres_eval_db.
    omega.

    eapply evalgep_prop4 in H; eauto. t_simp. destruct H. rewrite H.
    constructor. t_simp. rewrite H.
    apply IHwf_insns_ndterm; eauto with pres_eval_db.

    (* GEP1 case *)
    eapply evalgep1_prop in H; eauto. t_simp. destruct H. rewrite H.
    constructor. t_simp. rewrite H.
    apply IHwf_insns_ndterm; eauto with pres_eval_db.

    eapply evalgep1_prop in H; eauto. t_simp. destruct H. rewrite H.
    constructor. t_simp. rewrite H.
    apply IHwf_insns_ndterm; eauto with pres_eval_db.

    eapply evalgep1_prop2 in H; eauto. t_simp. destruct H. rewrite H.
    constructor. t_simp. rewrite H.
    apply IHwf_insns_ndterm; eauto with pres_eval_db.

    (* EXTRACTVALUE case *)
    eapply evalextractvalue_prop in H; eauto. t_simp. rewrite H.
    eapply IHwf_insns_ndterm; eauto with pres_eval_db.

    (* INSERTVALUE case *)
    eapply evalinsertvalue_prop in H; eauto. t_simp. rewrite H.
    eapply IHwf_insns_ndterm; eauto with pres_eval_db.

    (* ICONV case *)
    eapply evaliconv_prop in H; eauto. t_simp. rewrite H.
    apply IHwf_insns_ndterm; eauto with pres_eval_db.

    (* FCONV case *)
    eapply evalfconv_prop in H; eauto. t_simp. rewrite H.
    apply IHwf_insns_ndterm; eauto with pres_eval_db.

    eapply evalfconv_prop2 in H; eauto. t_simp. rewrite H.
    apply IHwf_insns_ndterm; eauto with pres_eval_db.

    (* BITCAST case *)
    eapply evalbitcast_prop in H; eauto. t_simp. rewrite H.
    apply IHwf_insns_ndterm; eauto with pres_eval_db.

    eapply evalbitcast_propU in H; eauto. t_simp. rewrite H.
    apply IHwf_insns_ndterm; eauto with pres_eval_db.

    (* PTRTOINT case *)
    eapply evalptrtoint_prop in H; eauto. t_simp. rewrite H.
    apply IHwf_insns_ndterm; eauto with pres_eval_db.

    eapply evalptrtoint_propU in H; eauto. t_simp. rewrite H.
    apply IHwf_insns_ndterm; eauto with pres_eval_db.

    (* INTTOPTR case *)
    (* success *)
    eapply evalinttoptr_prop in H; eauto. destruct H.
    t_simp. rewrite H. apply IHwf_insns_ndterm; eauto with pres_eval_db.
    crush.

    eapply evalinttoptr_propU in H; eauto. destruct H. 
    t_simp. rewrite H. apply IHwf_insns_ndterm; eauto with pres_eval_db.
    crush.

    (* GEPU case *)
    t_dup H. eapply evalgepU_prop in H7; eauto. destruct H7.
    rewrite H0. auto.
    t_simp. rewrite H0. apply IHwf_insns_ndterm; eauto with pres_eval_db.

    t_dup H. eapply evalgepU_prop2 in H; eauto. destruct H.
    rewrite H. auto.
    t_simp. rewrite H. apply IHwf_insns_ndterm; eauto with pres_eval_db.

    t_dup H. eapply evalgepU_prop4 with (o1 := o) (o2 := o0) in H10; eauto. destruct H10.
    rewrite H0. auto.
    t_simp. rewrite H0. apply IHwf_insns_ndterm; eauto with pres_eval_db.

    t_dup H. eapply evalgepU_prop3 in H; eauto. destruct H.
    rewrite H. auto.
    t_simp. rewrite H. apply IHwf_insns_ndterm; eauto with pres_eval_db.

    t_dup H. eapply evalgepU_prop3 in H; eauto. destruct H.
    rewrite H. auto.
    t_simp. rewrite H. apply IHwf_insns_ndterm; eauto with pres_eval_db.

    (* POOLCHECKU case *)
    t_dup H. eapply evalpoolcheck_notstuckU in H; eauto.
    destruct H. t_simp. rewrite H. apply IHwf_insns_ndterm; eauto with pres_eval_db. 
    rewrite H. auto.

    t_dup H. eapply evalpoolcheck_notstuckU in H; eauto.
    destruct H. t_simp. rewrite H. apply IHwf_insns_ndterm; eauto with pres_eval_db. 
    rewrite H. auto.

    (* EXIT case *)
    constructor.
  }
Qed.

(* ---------------------------------------------------------------------- *)
(** * More Execution Context/Stack Lemmas *)

Lemma wf_ec_term : forall C D f b t env HT rmap_e rmap_b rgns live G l,
  wf_ec C D (mk_ec f b nil t env HT rmap_e rmap_b rgns live ) G ->
  wf_ec C D (mk_ec f b nil (Insn_term (Insn_br_uncond l)) env HT rmap_e rmap_b rgns live) G.
Proof.
  unfold wf_ec; simpl; intros. t_simp. subst.
  exists f. exists b. repeat (split; eauto).
Qed.
Hint Resolve wf_ec_term : ec_ext_db2.

Lemma wf_ec_stk_top_diff : forall fs lo tenv f b insns t env HT rmap_e rmap_b rgns live D1 D2 G stk lsD lsG b' insns' t' env' G' FD FT,
  wf_ec (mk_config fs lo tenv) D2 (mk_ec f b' insns' t' env' HT rmap_e rmap_b rgns live) G' ->
  match b_nd_term b' with
    | Insn_nd _ => True
    | Insn_term (Insn_return tau _) => f_ret f = Some tau
    | Insn_term Insn_return_void => f_ret f = None
    | _ => True
  end ->
  wf_ec_stk (mk_config fs lo tenv) FD FT (mk_ec f b insns t env HT rmap_e rmap_b rgns live) (D1,D2) G stk lsD lsG ->
  wf_ec_stk (mk_config fs lo tenv) FD FT (mk_ec f b' insns' t' env' HT rmap_e rmap_b rgns live) (D1,D2) G' stk lsD lsG.
Proof.
  intros. inv H1; eauto. inv H17; simpl in *. 
  { econstructor; eauto. eapply wf_call_return; eauto. inv H.
    t_simp. simpl in *. subst. destruct t'; crush. destruct t1; crush.
    rewrite <- H6 in H0. crush. }
  { econstructor; eauto. eapply wf_call_return_void; eauto. inv H.
    t_simp. simpl in *. subst. destruct t'; crush. destruct t0; crush. 
    destruct (b_nd_term b'); crush. }
Qed.

Lemma wf_ec_stk_malloc : forall C FD FT f b env HT rmap_e rmap_b rgns live D G stk lsD lsG x t r n l,
  wf_ec_stk C FD FT (mk_ec f b nil (Insn_nd (Insn_malloc x t r n l)) env HT rmap_e rmap_b rgns live) D G stk lsD lsG ->
  wf_ec_stk C FD FT (mk_ec f b nil (Insn_term (Insn_br_uncond l)) env HT rmap_e rmap_b rgns live) D G stk lsD lsG.
Proof.
  intros. inv H; econstructor; eauto with ec_ext_db2. inv H9; eauto.
Qed.

Lemma wf_ec_stk_ret : forall fs lo tenv FD FT P x t D1 D2 G b l stk lsD lsG env rmap_e rmap_b rgns live bs rt f o prgns args fprgn HT,
  wf_ec_stk (mk_config fs lo tenv) FD FT (mk_ec f b nil 
    (Insn_nd (Insn_call (Some x) (Some (sigma''
                                (inst_prgn fprgn prgns) t)) o prgns args l)) env HT rmap_e rmap_b rgns live) (D1,D2) G stk lsD lsG ->
  wf_value fs lo tenv live HT rt (sigma rmap_b (sigma (inst_prgn fprgn prgns) (flatten_typ lo tenv t))) ->
  wf_term (mk_config fs lo tenv) D2 P (Nenv.add x (sigma (inst_prgn fprgn prgns) (flatten_typ lo tenv t)) G) bs (b_lab b) (Insn_br_uncond l) -> 
  wf_ec_stk (mk_config fs lo tenv) FD FT (mk_ec f b nil (Insn_term (Insn_br_uncond l))
    (Nenv.add x rt env) HT rmap_e rmap_b rgns live) (D1,D2) (Nenv.add x (sigma (inst_prgn fprgn prgns) (flatten_typ lo tenv t)) G) stk lsD lsG.
Proof.
  intros. inv H; econstructor; eauto. 
  { eapply wf_ec_env_val_ext; eauto with ec_ext_db2. }
  { eapply wf_ec_env_val_ext; eauto with ec_ext_db2. }
  { inv H17; eauto. }
Qed.

Lemma wf_ec_stk_ret_void : forall fs lo tenv FD FT P D1 D2 G b l stk lsD lsG env rmap_e rmap_b rgns live bs f o prgns args HT,
  wf_ec_stk (mk_config fs lo tenv) FD FT (mk_ec f b nil 
    (Insn_nd (Insn_call None None o prgns args l)) env HT rmap_e rmap_b rgns live) (D1,D2) G stk lsD lsG ->
  wf_term (mk_config fs lo tenv) D2 P G bs (b_lab b) (Insn_br_uncond l) -> 
  wf_ec_stk (mk_config fs lo tenv) FD FT (mk_ec f b nil (Insn_term (Insn_br_uncond l))
    env HT rmap_e rmap_b rgns live) (D1,D2) G stk lsD lsG.
Proof.
  intros. inv H; econstructor; eauto. 
  { unfold wf_ec in *; t_simp; simpl in *. subst. exists f. exists b. repeat (split; eauto). }
  { unfold wf_ec in *; t_simp; simpl in *. subst. exists f. exists b. repeat (split; eauto). }
  { inv H16; eauto. }
Qed.

(* ---------------------------------------------------------------------- *)
(** * Rgn Stuff *)

Lemma alpha_same1 : forall t D live rmap1 rmap2 r,
  Nenv.find r D = Some t ->
  wf_rmap D live rmap1 ->
  rmap_subset rmap1 rmap2 ->
  alpha rmap1 r = alpha rmap2 r.
Proof.
  unfold alpha; intros; simpl in *. unfold rmap_subset in H1.
  case_eq (Nenv.find r rmap1); intros.
  apply H1 in H2. rewrite H2. reflexivity.
  unfold wf_rmap in H0. apply H0 in H. t_simp. crush.
Qed.

Lemma alpha_same2 : forall r rmap1 rmap2 fprgn prgn D t live,
  Nenv.find r D = Some t ->
  wf_rmap D live rmap1 ->
  rmap_subset2 rmap1 rmap2 (inst_prgn fprgn prgn) ->
  alpha rmap1 r = alpha rmap2 (alpha (inst_prgn fprgn prgn) r).
Proof.
  unfold alpha; intros; simpl in *. unfold rmap_subset2 in H1.
  case_eq (Nenv.find r rmap1); intros.
  apply H1 in H2. unfold alpha in *. rewrite H2. reflexivity.
  unfold wf_rmap in H0. apply H0 in H. t_simp. crush.
Qed.

Lemma sigma_same'' : forall tenv D t live rmap1 rmap2,
  wf_typ tenv D t ->
  wf_rmap D live rmap1 ->
  rmap_subset rmap1 rmap2 ->
  sigma'' rmap1 t = sigma'' rmap2 t.
Proof.
  induction t; simpl; intros; auto. 
  { inv H. f_equal. eauto. eapply alpha_same1; eauto. }
  { inv H. f_equal. eauto. clear H7. induction lr; simpl; auto. inv H6. f_equal.
    destruct H3. eapply alpha_same1; eauto. eapply IHlr; eauto. }
  { inv H. f_equal. eauto. }
  { inv H. f_equal. eapply alpha_same1; eauto. }
Qed.

Lemma sigma_same1' : forall tenv D t live rmap1 rmap2,
  wf_ftyp tenv D t ->
  wf_rmap D live rmap1 ->
  rmap_subset rmap1 rmap2 ->
  sigma' rmap1 t = sigma' rmap2 t .
Proof.
  induction t; simpl; intros; auto. 
  { inv H. f_equal. eapply sigma_same''; eauto. eapply alpha_same1; eauto. }
  { inv H. f_equal. eapply alpha_same1; eauto. }
Qed.

Lemma sigma_same1 : forall tenv t D live rmap1 rmap2,
  wf_ftyps tenv D t ->
  wf_rmap D live rmap1 ->
  rmap_subset rmap1 rmap2 ->
  sigma rmap1 t = sigma rmap2 t.
Proof.
  induction 1; simpl; intros; auto. f_equal; eauto. eapply sigma_same1'; eauto.
Qed.

Lemma sigma_same2'' : forall tenv D t rmap1 rmap2 fprgn prgn live,
  wf_typ tenv D t ->
  wf_rmap D live rmap1 ->
  rmap_subset2 rmap1 rmap2 (inst_prgn fprgn prgn) ->
  sigma'' rmap1 t = sigma'' rmap2 (sigma'' (inst_prgn fprgn prgn) t).
Proof.
  induction t; simpl; intros; auto.
  { inv H. f_equal. eauto. eapply alpha_same2; eauto. }
  { inv H. f_equal; eauto. clear H7. induction lr; simpl; auto. inv H6. f_equal.
    destruct H3. eapply alpha_same2; eauto. eauto. }
  { inv H. f_equal. eauto. }
  { inv H. f_equal. eapply alpha_same2; eauto. }
Qed.

Lemma sigma_same2' : forall tenv D t rmap1 rmap2 fprgn prgn live,
  wf_ftyp tenv D t ->
  wf_rmap D live rmap1 ->
  rmap_subset2 rmap1 rmap2 (inst_prgn fprgn prgn) ->
  sigma' rmap1 t = sigma' rmap2 (sigma' (inst_prgn fprgn prgn) t).
Proof.
  induction t; simpl; intros; auto. 
  { inv H. f_equal. eapply sigma_same2''; eauto. eapply alpha_same2; eauto. }
  { inv H. f_equal. eapply alpha_same2; eauto. }
Qed.

Lemma sigma_same2 : forall tenv t D rmap1 rmap2 fprgn prgn live,
  wf_ftyps tenv D t ->
  wf_rmap D live rmap1 ->
  rmap_subset2 rmap1 rmap2 (inst_prgn fprgn prgn) ->
  sigma rmap1 t = sigma rmap2 (sigma (inst_prgn fprgn prgn) t).
Proof.
  induction 1; simpl; intros; auto. f_equal; eauto. eapply sigma_same2'; eauto.
Qed.

Lemma bind_prgn_spec1 : forall fprgn prgn rmap1 rmap2,
  list_norepet fprgn ->
  bind_prgn fprgn prgn rmap1 = Some rmap2 ->
  rmap_subset2 rmap2 rmap1 (inst_prgn fprgn prgn).
Proof.
  induction fprgn; crush. destruct prgn; crush.
  unfold rmap_subset2; simpl; intros. rewrite NFacts.empty_o in H0. inv H0. 
  destruct prgn; crush.
  remember (Nenv.find r rmap1) as Hd.
  destruct Hd; crush.
  remember (bind_prgn fprgn prgn rmap1) as Hd2.
  destruct Hd2; crush.
  symmetry in HeqHd. symmetry in HeqHd2. inv H.
  t_dup HeqHd2.
  eapply IHfprgn in HeqHd2; eauto.  
  unfold rmap_subset2 in *; intros.
  simpl in *. 
  destruct (eq_nat_dec r1 a); subst.
  rewrite NFacts.add_eq_o in H; auto. inv H.
  unfold alpha. rewrite NFacts.add_eq_o; auto. auto.
  rewrite NFacts.add_neq_o in H; auto.
  apply HeqHd2 in H. unfold alpha. rewrite NFacts.add_neq_o; crush.
Qed.

Lemma bind_prgn_spec2 : forall fprgn D1 live D2 rmap prgn rmap',
  wf_prgn_inst D2 prgn ->
  wf_rmap D2 live rmap ->
  wf_prgns fprgn D1 ->
  bind_prgn (domain fprgn) prgn rmap = Some rmap' ->
  wf_rmap D1 live rmap'.
Proof.
  induction fprgn; crush. destruct prgn; crush. inv H1. unfold wf_rmap; crush.
  rewrite H2 in H1.
  rewrite NFacts.empty_o in H1. inv H1.
  destruct prgn; crush.
  remember (Nenv.find r rmap) as Hd.
  destruct Hd; crush.
  remember (bind_prgn (domain fprgn) prgn rmap) as Hd2.
  destruct Hd2; crush.
  symmetry in HeqHd. symmetry in HeqHd2.
  inv H. inv H1.
  eapply IHfprgn in HeqHd2; eauto.
  unfold wf_rmap in *; intros; simpl in *.
  destruct (eq_nat_dec r1 a0); subst.
  rewrite NFacts.add_eq_o in *; auto. inv H. apply H0 in H5. t_simp. 
  assert (r0 = x) by crush. subst. eauto.
  rewrite H8 in H.
  rewrite NFacts.add_neq_o in *; eauto. 
Qed.

Definition map_add_ls_unique (rmap:Nenv.t rgn) (ls: list nat) :=
  (forall r r', 
    Nenv.find r rmap = Some r' -> 
    In r ls).

Lemma bind_prgn_spec3 : forall fprgn prgn rmap rmap',
  list_norepet fprgn ->
  bind_prgn fprgn prgn rmap = Some rmap' ->
  map_add_ls_unique rmap' fprgn.
Proof.
  unfold map_add_ls_unique.
  induction fprgn; crush. destruct prgn; crush. 
  rewrite NFacts.empty_o in H1. inv H1.
  destruct prgn; crush.
  remember (Nenv.find r0 rmap) as Hd.
  destruct Hd; crush.
  remember (bind_prgn fprgn prgn rmap) as Hd2.
  destruct Hd2; crush. 
  destruct (eq_nat_dec r a); subst; auto.
  rewrite NFacts.add_neq_o in H1; auto.
  symmetry in HeqHd2. eapply IHfprgn in HeqHd2; eauto.
  inv H; eauto.
Qed.

Lemma bind_lrgn_spec1 : forall lrgn fprgn rmap,
  list_norepet (domain lrgn) ->
  list_disjoint (domain lrgn) fprgn ->
  map_add_ls_unique rmap fprgn ->
  rmap_subset rmap (bind_lrgn lrgn rmap).
Proof.
  induction lrgn; crush.
  assert (~ In a0 fprgn).
  inv H. unfold list_disjoint in H0. unfold not; intros.
  eapply H0 in H; simpl; eauto.
  eapply list_disjoint_cons_left in H0. 
  eapply IHlrgn in H0; eauto. unfold rmap_subset; intros.
  destruct (eq_nat_dec r a0); subst.
  rewrite NFacts.add_eq_o; auto. unfold map_add_ls_unique in H1.
  apply H1 in H3. contradiction.
  rewrite NFacts.add_neq_o in *; auto. inv H; auto.
Qed.

Lemma bind_lrgn_spec2 : forall C lrgn' lrgn fprgn D1 D2 live rmap,
  domain lrgn' = domain lrgn ->
  list_disjoint (domain lrgn') fprgn ->
  wf_lrgns C lrgn D1 D2 ->
  wf_rmap D1 live rmap ->
  map_add_ls_unique rmap fprgn ->
  wf_rmap D2 (range lrgn' ++ live) (bind_lrgn lrgn' rmap).
Proof.
  induction lrgn'; crush. 
  { unfold wf_rmap in *; crush. inv H1. eauto. crush. }
  { destruct lrgn. inv H.
    simpl in H. destruct p. simpl in H. 
    assert (a0 = r) by crush. subst.
    inv H. inv H1. 
    eapply IHlrgn' in H5; eauto.
    unfold wf_rmap in *; crush.
    destruct (eq_nat_dec r0 r); subst.
    rewrite NFacts.add_eq_o in *; auto. inv H. eauto.
    rewrite NFacts.add_neq_o in *; auto. apply H5 in H. t_simp. eauto.
    eapply list_disjoint_cons_left in H0. eauto. }
Qed.

(* ---------------------------------------------------------------------- *)
Lemma wf_typ_closed_ls : forall lr1 D live rmap,
  Forall (fun r : nat => exists t : typ, Nenv.find r D = Some t) lr1 ->
  wf_rmap D live rmap ->
  Forall (fun r => In r live) (map (alpha rmap) lr1).
Proof.
  induction lr1; crush. inv H. econstructor; eauto. t_simp. 
  unfold wf_rmap in H0. apply H0 in H. t_simp. unfold alpha. rewrite H; auto.
Qed.

Lemma wf_typ_closed : forall t D live rmap tenv,
  wf_typ tenv D t ->
  wf_rmap D live rmap ->
  wf_tenv_typ live (sigma'' rmap t).
Proof.
  induction 1; intros; try econstructor; eauto.
  { unfold wf_rmap in H2. apply H2 in H. t_simp. unfold alpha. rewrite H; auto. }
  { eapply wf_typ_closed_ls; eauto. }
  { unfold wf_rmap in H1. apply H1 in H. t_simp. unfold alpha. rewrite H; auto. }
Qed.

Lemma wf_ftyp_closed : forall t D live rmap tenv,
  wf_ftyp tenv D t ->
  wf_rmap D live rmap ->
  wf_tenv_ftyp live (sigma' rmap t).
Proof.
  induction 1; intros; try econstructor; eauto.
  { unfold wf_rmap in H1. apply H1 in H. t_simp. unfold alpha. rewrite H; auto. }
  { eapply wf_typ_closed; eauto. }
  { unfold wf_rmap in H0. apply H0 in H. t_simp. unfold alpha. rewrite H; auto. }
Qed.

Lemma wf_ftyps_closed : forall t D live rmap lo tenv,
  wf_ftyps tenv D (flatten_typ lo tenv t) ->
  wf_rmap D live rmap ->
  wf_tenv_ftyps live (sigma rmap (flatten_typ lo tenv t)).
Proof.
  induction 1; simpl; intros; auto. econstructor; eauto. eapply wf_ftyp_closed; eauto.
Qed.

Lemma wf_ftyps_closed_ls : forall ts D rmap rgns live lo tenv,
  Forall (fun t => wf_ftyps tenv D (flatten_typ lo tenv t)) ts ->
  wf_rmap D (rgns ++ live) rmap ->
  Forall (fun t => wf_tenv_ftyps (rgns++live) (sigma rmap (flatten_typ lo tenv t))) ts.
Proof.
  induction ts; crush. inv H. econstructor; eauto. eapply wf_ftyps_closed; eauto.
Qed.

(* ---------------------------------------------------------------------- *)
(** * Non-deterministic Instruction Helper Lemmas *)

(* ---------------------------------------------------------------------- *)
(* Phinode Helper Lemmas *)

Lemma update_phi_spec : forall ls l env D P G1 lo fs tenv G2 x t live HT rmap,
  wf_env (mk_config fs lo tenv) live HT rmap env G1 ->
  wf_phinode (mk_config fs lo tenv) D P (Insn_phi x t ls) l G1 G2 ->
  wf_tenv tenv ->
  wf_rmap D live rmap ->
  exists rt, update_phi lo tenv env l (Insn_phi x t ls) = Some (Nenv.add x rt env) /\
    wf_env (mk_config fs lo tenv) live HT rmap (Nenv.add x rt env) G2.
Proof.
  intros. inv H0. simpl in *. remember (mk_config fs lo tenv) as C. 
  remember (flatten_typ lo tenv t) as t'.
  induction H13; simpl in *; destruct_c lab_dec; eauto; subst; t_insn_simpl_pro.
  (* inv H13; simpl in *; destruct_c lab_dec; eauto; subst; t_insn_simpl_pro. *)
  { rewrite <- Heqt'. exists (RT_ptr x1 :: nil). split; auto. eapply wf_env_val_ext; eauto.
    repeat econstructor. destruct zeq; auto. inv H4. unfold wf_rmap in H2.
    apply H2 in H11. t_simp. unfold alpha. rewrite H4. auto.
    rewrite <- flatten_sigma_comm in *; auto. eapply check_HT_subset; eauto. }
  (*
  { rewrite <- Heqt'. exists (RT_ptr (Word.repr 0) :: nil). split; auto. 
    eapply wf_env_val_ext; eauto. repeat econstructor. }
  *)
  { rewrite <- Heqt'.
    exists (RT_ptr x1 :: nil). split; auto. eapply wf_env_val_ext; eauto.
    repeat econstructor. destruct zeq; auto. inv H4. unfold wf_rmap in H2.
    apply H2 in H8. t_simp. unfold alpha. rewrite H4. auto.
    rewrite bytes_sigma_inv with (rmap := rmap) in *.
    eapply check_HT_subset_bytes; eauto. omega. }
  { exists (weaken_val x0 (flatten_typ lo tenv t)). split; auto.
    eapply wf_env_val_ext; eauto. eapply wf_val_ftyps_weaken; eauto. }
Qed.

Lemma update_phis_spec : forall phis l env env' D P G1 lo fs tenv G2 live HT rmap,
  wf_phi_blk (mk_config fs lo tenv) D P phis l G1 G2 ->
  update_phis lo tenv env l phis = Some env' ->
  wf_env (mk_config fs lo tenv) live HT rmap env G1 ->
  wf_tenv tenv ->
  wf_rmap D live rmap ->
  wf_env (mk_config fs lo tenv) live HT rmap env' G2.
Proof.
  induction phis; crush. 
  { inv H. eauto. }
  { inversion H; subst. inversion H9; subst. eapply update_phi_spec in H9; eauto. 
    t_simp. rewrite H4 in H0. simpl in *. eapply IHphis; eauto. }
Qed.

(* ---------------------------------------------------------------------- *)
(* Argument Binding Lemmas *)

Lemma wf_env_val_ext2 : forall G2 G x fs lo tenv live HT v t env rmap,
  Nenv.Equal G2 (Nenv.add x t G) ->
  wf_value fs lo tenv live HT v (sigma rmap t) ->
  wf_env (mk_config fs lo tenv) live HT rmap env G ->
  wf_env (mk_config fs lo tenv) live HT rmap (Nenv.add x v env) G2.
Proof.
  unfold wf_env; simpl; intros.
  unfold Nenv.Equal in H. rewrite H in H2.
  destruct (eq_nat_dec x0 x); subst.
  { rewrite NFacts.add_eq_o in *; eauto. inv H2. eauto. }
  { rewrite NFacts.add_neq_o in *; eauto. }
Qed.

Lemma weaken_val_sigma : forall v t rmap,
  weaken_val v t = weaken_val v (sigma rmap t).
Proof.
  induction v; destruct t; simpl; intros; auto.
  f_equal. eauto.
Qed.

Lemma init_fun_spec : forall args env params fs lo tenv sig G1 G2 D P env' live HT rmap prgn fprgn rmap' lrgn D1,
  wf_rmap D1 live rmap' ->
  wf_rmap D live rmap ->
  wf_args (mk_config fs lo tenv) D P G1 (inst_prgn fprgn prgn) args sig ->
  wf_fparams (mk_config fs lo tenv) D1 params sig G2 ->
  rmap_subset rmap' (bind_lrgn lrgn rmap') ->
  rmap_subset2 rmap' rmap (inst_prgn fprgn prgn) ->
  init_fun env lo tenv params sig args = Some env' ->
  wf_env (mk_config fs lo tenv) live HT rmap env G1 ->
  wf_env (mk_config fs lo tenv) live HT (bind_lrgn lrgn rmap') env' G2.
Proof.
  induction args; intros. 
  { inv H1. inv H2. unfold wf_env; crush. rewrite H1 in H2.
    rewrite NFacts.empty_o in H2. inv H2. }
  { inv H1. inv H2. simpl in *. 
    remember (init_fun env lo tenv ids sig' args) as Hd.
    destruct_c Hd. symmetry in HeqHd.
    t_insn_simpl_pro. rewrite H1 in H5. inv H5. eapply IHargs in H15; eauto.
    eapply wf_env_val_ext2; eauto.
    erewrite <- sigma_same1; eauto.
    erewrite sigma_same2; eauto.
    eapply wf_val_ftyps_weaken in H18; eauto.
    erewrite <- weaken_val_sigma in H18; eauto.
    (*
    destruct_c (sigma (inst_prgn fprgn prgn) (flatten_typ lo tenv t)).
    destruct_c f. destruct_c f0. destruct_c t''. destruct_c f. destruct_c t''.
    destruct rgn_dec; try contradiction. destruct_c le_dec; try contradiction.
    subst. inv H2. inv H12. constructor. simpl. econstructor; eauto.
    rewrite bytes_sigma_inv with (rmap := rmap) in *. eapply check_HT_subset_bytes; eauto.
    omega. inv H14. constructor. 
    *)
  }
Qed.

(* ---------------------------------------------------------------------- *)
(* Malloc helper lemmas *)

Lemma evalmalloc_pres : forall fs lo tenv r t m rt n m' live rmap HT env,
  wf_tenv tenv ->
  TS tenv t ->
  eval_malloc env m lo tenv live rmap HT r (Some t) n = Some (rt, m') ->
  wf_mem fs lo tenv live HT m ->
  wf_value fs lo tenv live HT 
    rt
    (Ftyp_ptr (sigma'' rmap t) (alpha rmap r) :: nil) /\
  wf_mem fs lo tenv live HT m'.
Proof.
  unfold eval_malloc; intros. 
  destruct_c (op2rtv n env). destruct_c r0. destruct_c r0. destruct_c r1.
  remember (alloc m lo live HT (sigma rmap (flatten_typ lo tenv t)) (nat_of_Z (Word.unsigned i)) (alpha rmap r)) as Hd.
  destruct_c Hd. 
  symmetry in HeqHd. destruct p. inv H1. split. econstructor; eauto. 
  eapply alloc_typ; eauto. econstructor; eauto. unfold wf_mem in *; intros. 
  apply H2 in H1. t_simp. eapply load_alloc_same in H1; eauto.
Qed.

Lemma evalmalloc_presU : forall fs lo tenv r m rt x m' live rmap HT env,
  eval_malloc env m lo tenv live rmap HT r None (Op_reg x) = Some (rt, m') ->
  wf_mem fs lo tenv live HT m ->
  wf_value fs lo tenv live HT 
    rt
    (Ftyp_ptrU 0 (alpha rmap r) :: nil) /\
  wf_mem fs lo tenv live HT m'.
Proof.
  unfold eval_malloc; intros.
  destruct_c (op2rtv (Op_reg x) env). destruct_c r0. destruct_c r0. destruct_c r1.
  remember (alloc m lo live HT
          (sigma rmap (list_repeat (nat_of_Z (Word.unsigned i)) Ftyp_int8)) 1
          (alpha rmap r)) as Hd.
  destruct_c Hd. symmetry in HeqHd. destruct p. inv H. split. econstructor; eauto. 
  erewrite <- bytes_sigma_inv in HeqHd; eauto.
  eapply alloc_typU in HeqHd; eauto. 
  econstructor; eauto. inv HeqHd.
  assert (n = p) by crush. subst.
  destruct zeq; auto. unfold check_HT.
  destruct zeq; auto.
  constructor. unfold wf_mem in *; intros. 
    apply H0 in H. t_simp. eapply load_alloc_same in H; eauto.
  Grab Existential Variables.
  apply tenv. apply fs.  
Qed.

Lemma evalmalloc_presU2 : forall fs lo tenv r m rt sz pf i m' live rmap HT env,
  eval_malloc env m lo tenv live rmap HT r None (Op_const (Const_int sz pf i)) = Some (rt, m') ->
  wf_mem fs lo tenv live HT m ->
  wf_value fs lo tenv live HT 
    rt
    (Ftyp_ptrU (nat_of_Z (Word.unsigned i)) (alpha rmap r) :: nil) /\
  wf_mem fs lo tenv live HT m'.
Proof.
  unfold eval_malloc; intros. simpl in H. 
  remember (alloc m lo live HT
          (sigma rmap (list_repeat (nat_of_Z (Word.unsigned i)) Ftyp_int8))
          1 (alpha rmap r)) as Hd.
  destruct_c Hd. symmetry in HeqHd. destruct p. inv H. split. econstructor; eauto. 
  erewrite <- bytes_sigma_inv in HeqHd; eauto.
  eapply alloc_typU in HeqHd; eauto. constructor.
  unfold wf_mem in *; intros. 
  apply H0 in H. t_simp. eapply load_alloc_same in H; eauto.
Qed.

Lemma evalmalloc_wf_meta : forall HT mem lo tenv live rmap r t n rt mem' env,
  wf_mem_metadata HT mem ->
  eval_malloc env mem lo tenv live rmap HT r t n = Some (rt, mem') ->
  wf_mem_metadata HT mem'.
Proof.
  intros. unfold eval_malloc in H0.
  destruct_c (op2rtv n env). destruct_c r0. destruct_c r0. destruct_c r1. destruct t.
  { remember (alloc mem0 lo live HT (sigma rmap (flatten_typ lo tenv t)) (nat_of_Z (Word.unsigned i))
    (alpha rmap r)) as Hd. destruct_c Hd. destruct p; auto. symmetry in HeqHd.
    apply alloc_high_addr_same in HeqHd. unfold wf_mem_metadata in *; crush. }
  { remember (alloc mem0 lo live HT
           (sigma rmap (list_repeat (nat_of_Z (Word.unsigned i)) Ftyp_int8))
           1 (alpha rmap r)) as Hd.
    destruct_c Hd. destruct p. symmetry in HeqHd.
    apply alloc_high_addr_same in HeqHd. unfold wf_mem_metadata in *; crush. }
Qed.

(* ---------------------------------------------------------------------- *)
(* Return helper lemmas *)

Ltac t_norm := 
  repeat (
    match goal with
      | [ H1: Ienv.find ?i1 ?I = Some ?c,
          H2: Ienv.find ?i2 ?I = Some ?d |- _ ] => assert (c = d) by crush; subst; clear H1
      | [ H1: lookup_blk ?l1 ?bs = Some ?c,
          H2: lookup_blk ?l2 ?bs = Some ?d |- _ ] => assert (c = d) by crush; subst; clear H1
      | [ H1: lookup_fun ?l1 ?fs = Some ?c,
          H2: lookup_fun ?l2 ?fs = Some ?d |- _ ] => assert (c = d) by crush; subst; clear H1
    end).

Lemma stepret_typ : forall fs lo tenv FT FD f b t o env HT rmap_e rmap_b rgns live D G t',
  wf_functions (mk_config fs lo tenv) FT FD ->
  wf_ec (mk_config fs lo tenv) D (mk_ec f b nil (Insn_term (Insn_return t o)) env HT rmap_e rmap_b rgns live) G ->
  f_ret f = Some t' ->
  t = t' /\
  exists D1, exists D2, 
    Ienv.find (f_lab f) FD = Some (D1, D2) /\
    wf_ftyps tenv D1 (flatten_typ lo tenv t).
Proof.
  intros. inv H0. t_simp. simpl in *. subst.
  unfold wf_functions in H. t_simp. apply H in H3.
  t_simp. unfold wf_function in H3. t_simp.
  unfold wf_fbody in H24. t_simp. t_dup H4.
  apply H25 in H4. t_simp. apply H26 in H4. t_simp.
  t_norm. rewrite <- H5 in H28. split; crush; eauto.
Qed.

(* ---------------------------------------------------------------------- *)
(* Branch helper lemmas *)

Lemma evalbr_blk_prop : forall fs lo tenv FT FD P D1 D2 G f b l,
  wf_functions (mk_config fs lo tenv) FT FD ->
  wf_junction (mk_config fs lo tenv) D2 P G (f_body f) (b_lab b) l ->
  Ienv.find (f_lab f) FT = Some P ->
  Ienv.find (f_lab f) FD = Some (D1, D2) ->
  lookup_fun (f_lab f) fs = Some f ->
  exists b', exists G', 
    lookup_blk l (f_body f) = Some b' /\
    Ienv.find (b_lab b') P = Some G' /\
    wf_insns_ndterm (mk_config fs lo tenv) D2 P (f_body f) (b_lab b') (b_insns b') 
      (b_nd_term b') G' /\
    match b_nd_term b' with
      | Insn_nd _ => True
      | Insn_term (Insn_return t _) => 
        f_ret f = Some t /\
        wf_ftyps tenv D1 (flatten_typ lo tenv t)
      | Insn_term Insn_return_void => f_ret f = None
      | _ => True
    end.
Proof.
  intros. inv H0. t_simp. unfold wf_functions in H. t_simp.
  apply H in H3. t_simp. t_norm. unfold wf_function in H8.
  t_simp. unfold wf_fbody in H18. t_simp. t_dup H0. apply H20 in H0. 
  t_simp. assert (x1 = x9) by crush. subst.
  eapply lookup_blk_spec in H0; eauto. subst.
  assert (D1 = x2) by crush. 
  assert (D2 = x3) by crush. subst. eauto 10. 
Qed.

Lemma evalbr_wf_ec : forall phis l env env' D P G1 lo fs tenv G2 HT G3 f b rmap_e rmap_b rgns live,
  wf_phi_blk (mk_config fs lo tenv) D P phis l G1 G2 ->
  update_phis lo tenv env l phis = Some env' ->
  wf_env (mk_config fs lo tenv) live HT rmap_b env G1 ->
  extends_gamma G3 G2 ->
  lookup_fun (f_lab f) fs = Some f ->
  lookup_blk (b_lab b) (f_body f) = Some b ->
  wf_rmap D live rmap_b ->
  rmap_subset rmap_e rmap_b ->
  list_norepet rgns ->
  wf_HT lo HT ->
  wf_HT_live live HT ->
  wf_HT_bounds HT ->
  wf_tenv tenv ->
  wf_ec (mk_config fs lo tenv) D (mk_ec f b (b_insns b) (b_nd_term b) env' HT rmap_e rmap_b rgns live) G3.
Proof.
  intros. unfold wf_ec; simpl in *. exists f. exists b.
  eapply update_phis_spec in H1; eauto.
  eapply wf_env_subsume in H1; eauto. 
  repeat (split; eauto).
  destruct (b_nd_term b); eauto. destruct t; eauto.
  exists nil; eauto.
Qed.

Lemma wf_switch_prop : forall ls C D P G sz pf o bs l ldef env b live HT rmap,
  wf_junction C D P G bs l ldef ->
  wf_operand C D P G o (sigma rmap (Ftyp_int sz pf :: nil)) ->
  wf_env C live HT rmap env G ->
  wf_switch_arms C D P G bs (Typ_int sz pf) l ls ->
  eval_switch env bs o ldef ls = Some b ->
  wf_junction C D P G bs l (b_lab b) /\
  lookup_blk (b_lab b) bs = Some b.
Proof.
  induction ls; simpl; intros.
  { assert (ldef = (b_lab b)). eapply lookup_blk_spec; eauto. subst. auto. }
  { simpl in H3. destruct a. destruct p. destruct_c c. destruct C. inv H2. 
    t_dup H0. eapply wf_op_val in H0; eauto. t_simp. eapply canonical_form_int in H2; eauto.
    t_simp. subst.
    rewrite H0 in H3. destruct_c eq_nat_dec; subst. destruct_c Word.eq_dec; subst.
    assert (l0 = (b_lab b)). eapply lookup_blk_spec; eauto. subst. auto. 
    eapply IHls in H3; eauto.
    assert (pf1 = pf). apply proof_irr. subst. auto. }
Qed.

Lemma wf_indirect_br_prop : forall ls C D P G r o bs l env b live HT rmap,
  match o with
    | Op_reg x => Nenv.find x G = Some (Ftyp_ptr Typ_int8 r :: nil)
    | Op_const (Const_baddr _ _) => True
    | _ => False
  end ->
  wf_env C live HT rmap env G ->
  wf_indirect_br_arms C D P G bs l ls ->
  eval_indirect_br env bs o ls = Some b ->
  wf_junction C D P G bs l (b_lab b) /\
  lookup_blk (b_lab b) bs = Some b.
Proof.
  induction ls; simpl; intros. inv H2. destruct o. 
  { t_dup H. unfold op2rtv in H2. unfold wf_env in H0.  apply H0 in H. t_simp. 
    rewrite H in H2. eapply canonical_form_ptr in H3. t_simp. subst.
    unfold RT_ptr in H2.
    destruct_c Word.eq_dec.
    assert (a = b_lab b). eapply lookup_blk_spec; eauto. subst.
    inv H1. auto.
    inv H1. eapply IHls in H2; eauto. }
  { destruct c; try contradiction. simpl in H2. 
    destruct_c Word.eq_dec; subst.
    assert (a = b_lab b). eapply lookup_blk_spec; eauto. subst.
    inv H1. auto.
    inv H1. eapply IHls in H2; eauto. }
Qed.

(* ---------------------------------------------------------------------- *)
(* Function call helper lemmas *)

Lemma evalcall_fun_prop : forall fs lo tenv FT FD P D G o prgns sig t fid f env b live rmap HT,
  wf_functions (mk_config fs lo tenv) FT FD ->
  wf_operand (mk_config fs lo tenv) D P G o (Ftyp_fun prgns sig (Some t) :: nil) ->
  wf_env (mk_config fs lo tenv) live HT rmap env G ->
  op2fun o env = Some fid ->
  lookup_fun fid fs = Some f ->
  lookup_blk fid (f_body f) = Some b ->
  fid = Word.zero \/
  exists P', exists G', exists G'', exists D1, exists D2, exists D1', exists D2',
    Ienv.find (f_lab f) FT = Some P' /\
    Ienv.find (f_lab f) P' = Some G' /\
    Nenv.Equal G' G'' /\
    wf_fparams (mk_config fs lo tenv) D1 (f_params f) sig G'' /\
    wf_insns_ndterm (mk_config fs lo tenv) D2 P' (f_body f) (b_lab b) 
      (b_insns b) (b_nd_term b) G' /\
    match b_nd_term b with
      | Insn_nd _ => True
      | Insn_term (Insn_return t _) => 
        f_ret f = Some t /\
        wf_ftyps tenv D1 (flatten_typ lo tenv t)
      | Insn_term Insn_return_void => f_ret f = None
      | _ => True
    end /\
    f_ret f = Some t /\
    f_sig f = sig /\
    Ienv.find (f_lab f) FD = Some (D1, D2) /\
    list_disjoint (domain (f_lrgn f)) (domain (f_prgn f)) /\
    list_norepet (domain (f_prgn f)) /\
    list_norepet (domain (f_lrgn f)) /\
    Nenv.Equal D1 D1' /\
    Nenv.Equal D2 D2' /\
    wf_prgns (f_prgn f) D1' /\
    wf_lrgns (mk_config fs lo tenv) (f_lrgn f) D1' D2' /\
    Forall (fun t => wf_ftyps tenv D2 (flatten_typ lo tenv t)) (range (f_lrgn f)) /\
    domain (f_prgn f) = prgns.
Proof.
  intros. eapply wf_opfun_val in H0; eauto. t_simp. 
  destruct H5. assert (x = fid) by crush. crush.
  t_simp. subst.  rewrite H0 in H2.
  inv H2. unfold wf_functions in H. t_simp. t_dup H3.
  assert (fid = f_lab f). eapply lookup_fun_spec; eauto. subst.
  apply H in H3. t_simp. unfold wf_function in H6. t_simp.
  unfold wf_fbody in H18. t_simp. t_dup H4. apply H19 in H4. t_simp.
  t_dup H4. apply H20 in H4. t_simp. t_norm. right.
  exists x2. exists x7. exists x4. exists x. exists x1. exists x5. exists x6.
  simpl in *. repeat (split; eauto).
Qed.

Lemma evalcall_fun_prop2 : forall fs lo tenv FT FD P D G o prgns sig fid f env b live rmap HT,
  wf_functions (mk_config fs lo tenv) FT FD ->
  wf_operand (mk_config fs lo tenv) D P G o (Ftyp_fun prgns sig None :: nil) ->
  wf_env (mk_config fs lo tenv) live HT rmap env G ->
  op2fun o env = Some fid ->
  lookup_fun fid fs = Some f ->
  lookup_blk fid (f_body f) = Some b ->
  fid = Word.zero \/
  exists P', exists G', exists G'', exists D1, exists D2, exists D1', exists D2',
    Ienv.find (f_lab f) FT = Some P' /\
    Ienv.find (f_lab f) P' = Some G' /\
    Nenv.Equal G' G'' /\
    wf_fparams (mk_config fs lo tenv) D1 (f_params f) sig G'' /\
    wf_insns_ndterm (mk_config fs lo tenv) D2 P' (f_body f) (b_lab b) 
      (b_insns b) (b_nd_term b) G' /\
    match b_nd_term b with
      | Insn_nd _ => True
      | Insn_term (Insn_return t _) => 
        f_ret f = Some t /\
        wf_ftyps tenv D1 (flatten_typ lo tenv t)
      | Insn_term Insn_return_void => f_ret f = None
      | _ => True
    end /\
    f_ret f = None /\
    f_sig f = sig /\
    Ienv.find (f_lab f) FD = Some (D1, D2) /\
    list_disjoint (domain (f_lrgn f)) (domain (f_prgn f)) /\
    list_norepet (domain (f_prgn f)) /\
    list_norepet (domain (f_lrgn f)) /\
    Nenv.Equal D1 D1' /\
    Nenv.Equal D2 D2' /\
    wf_prgns (f_prgn f) D1' /\
    wf_lrgns (mk_config fs lo tenv) (f_lrgn f) D1' D2' /\
    Forall (fun t => wf_ftyps tenv D2 (flatten_typ lo tenv t)) (range (f_lrgn f)) /\
    domain (f_prgn f) = prgns.
Proof.
  intros. eapply wf_opfun_val in H0; eauto. t_simp. 
  destruct H5. assert (x = fid) by crush. crush.
  t_simp. subst.  rewrite H0 in H2.
  inv H2. unfold wf_functions in H. t_simp. t_dup H3.
  assert (fid = f_lab f). eapply lookup_fun_spec; eauto. subst.
  apply H in H3. t_simp. unfold wf_function in H6. t_simp.
  unfold wf_fbody in H18. t_simp. t_dup H4. apply H19 in H4. t_simp.
  t_dup H4. apply H20 in H4. t_simp. t_norm. right.
  exists x2. exists x7. exists x4. exists x. exists x1. exists x5. exists x6.
  simpl in *. repeat (split; eauto).
Qed.

(* ---------------------------------------------------------------------- *)
(** * Preservation *)

Lemma wf_env_live_ext : forall C HT live rmap env G rgns,
  wf_env C live HT rmap env G ->
  wf_env C (rgns++live) HT rmap env G.
Proof.
  unfold wf_env; intros. apply H in H0. t_simp.
  exists x0. split; crush. eapply wf_val_live_ext; eauto.
Qed.

Lemma wf_env_HT_ext : forall C live HT HT' rmap env G,
  heapt_ext HT HT' ->
  wf_env C live HT rmap env G ->
  wf_env C live HT' rmap env G.
Proof.
  unfold wf_env; intros. apply H0 in H1. t_simp.
  exists x0. split; crush. eapply wf_val_HT_ext; eauto.
Qed.

Lemma wf_rmap_subset_weaken : forall D live rmap1 rmap2,
  wf_rmap D live rmap1 ->
  rmap_subset rmap1 rmap2 ->
  wf_rmap D live rmap2.
Proof.
  unfold wf_rmap; intros. apply H in H1. t_simp. unfold rmap_subset in H0. eauto.
Qed.

Lemma check_HT_live_ctr' : forall t live lo HT HT' n r,
  In r live ->
  heapt_ext2 live HT' HT ->
  check_HT' lo HT n r t = true ->
  check_HT' lo HT' n r t = true.
Proof.
  induction t; crush.
  remember (Zenv.find n HT) as Hd. symmetry in HeqHd.
  destruct Hd; try congruence. destruct p; auto.
  destruct rgn_dec; try congruence.
  (* consider (ftyp_sub a f); intros; try congruence. subst. *)
  destruct ftyp_eq_dec; try congruence. subst. 
  unfold heapt_ext2 in H0. apply H0 in HeqHd; auto. rewrite HeqHd.
  destruct rgn_dec; try congruence.
  (* rewrite H1. eapply IHt; eauto. *)
  destruct ftyp_eq_dec; try congruence.
  eapply IHt; eauto.
Qed.
 
Lemma wf_val_live_ctr' : forall t v D live rgns rmap fs lo tenv HT HT',
  wf_tenv tenv ->
  wf_ftyp tenv D t ->
  wf_rmap D live rmap ->
  list_disjoint rgns live ->
  heapt_ext2 live HT' HT ->
  wf_value' fs lo tenv (rgns ++ live) HT v (sigma' rmap t) ->
  wf_value' fs lo tenv live HT' v (sigma' rmap t).
Proof.
  induction t; intros. 
  { inv H4. econstructor; eauto. }
  { inv H4. econstructor; eauto. }
  { inv H4. assert (pf0 = l). apply proof_irr. subst. econstructor; eauto. }
  { inv H4. destruct zeq. econstructor; eauto. destruct zeq; try congruence. 
    unfold check_HT. destruct zeq; try congruence. inv H0.
    assert (In (alpha rmap r) live).
    unfold wf_rmap in H1. apply H1 in H7. t_simp. unfold alpha in *.
    rewrite H0 in *; auto. econstructor; eauto.
    unfold check_HT in *. destruct zeq; try congruence.
    unfold check_HT in *. destruct zeq; try congruence.
    eapply check_HT_live_ctr'; eauto. }
  { inv H4. econstructor; eauto. }
  { inv H4. destruct zeq. econstructor; eauto. destruct_c zeq.
    unfold check_HT. destruct_c zeq. inv H0.
    assert (In (alpha rmap r) live).
    unfold wf_rmap in H1. apply H1 in H6. t_simp. unfold alpha in *.
    rewrite H0 in *; auto. econstructor; eauto.
    destruct_c zeq. unfold check_HT in *. destruct_c zeq.
    eapply check_HT_live_ctr'; eauto. }
Qed.

Lemma wf_val_live_ctr : forall t v D live rgns rmap fs lo tenv HT HT',
  wf_tenv tenv ->
  wf_ftyps tenv D t ->
  wf_rmap D live rmap ->
  list_disjoint rgns live ->
  heapt_ext2 live HT' HT ->
  wf_value fs lo tenv (rgns ++ live) HT v (sigma rmap t) ->
  wf_value fs lo tenv live HT' v (sigma rmap t).
Proof.
  induction t; intros. 
  { inv H4. repeat econstructor; eauto. }
  { inv H0. inv H4. repeat econstructor; eauto.
    eapply wf_val_live_ctr'; eauto.
    eapply IHt in H12; eauto. }
Qed.

Ltac t_pres_init :=
  match goal with
    | [ H: wf_ms _ _ |- _ ] => inv H
  end;
  match goal with
    | [ H: wf_insns_ndterm _ _ _ _ _ _ _ _ |- _ ] => inversion H; subst
  end;
  match goal with
    | [ H: wf_term _ _ _ _ _ _ _ |- _ ] => inversion H; subst
    | [ H: wf_nd _ _ _ _ _ _ _ |- _ ] => inversion H; subst
    | [ H: wf_insn _ _ _ _ _ _ |- _ ] => inversion H; subst
  end;
  match goal with
    | [ H: wf_ec_stk _ _ _ _ _ _ _ _ _ |- _ ] =>
      t_dup H
  end;
  match goal with
    | [ H: wf_ec_stk _ _ _ _ _ _ _ _ _ |- _ ] =>
      apply wf_ec_stk_proj_env in H
  end;
  match goal with
    | [ H: wf_ec_stk _ _ _ _ _ _ _ _ _ |- _ ] =>
      t_dup H
  end;
  match goal with
    | [ H: wf_ec_stk _ _ _ _ _ _ _ _ _ |- _ ] =>
      apply wf_ec_stk_proj_HT in H
  end.

Lemma wf_rmap_delta_eq : forall D live rmap D',
  Nenv.Equal D D' ->
  wf_rmap D live rmap ->
  wf_rmap D' live rmap.
Proof.
  unfold wf_rmap; intros. rewrite <- H in H1. eauto.
Qed.
  
Lemma wf_fparams_eq : forall params sig C D G G',
  wf_fparams C D params sig G ->
  Nenv.Equal G G' ->
  wf_fparams C D params sig G'.
Proof.
  induction params; destruct sig; simpl; intros.
  { inv H. rewrite H0 in H1. crush. }
  { inv H. }
  { inv H. }
  { inv H. econstructor; eauto. crush. }
Qed.

Lemma wf_typ_equal : forall t D D' tenv,
  Nenv.Equal D D' ->
  wf_typ tenv D t ->
  wf_typ tenv D' t.
Proof.
  induction t; simpl; intros; eauto.
  { inv H0. econstructor; eauto. }
  { inv H0. econstructor; eauto. }
  { inv H0. econstructor; eauto. }
  { inv H0. econstructor; eauto. rewrite H in *; crush. }
  { inv H0. econstructor; eauto. clear H3. clear H6. induction lr; crush. inv H5.
    t_simp. econstructor; eauto. rewrite H in *; crush; eauto. }
  { inv H0; econstructor; eauto. } 
  { inv H0. econstructor; eauto. }
  { inv H0. econstructor; eauto. rewrite H in *; crush. }
Qed.

Lemma wf_ftyp_equal : forall t D D' tenv,
  Nenv.Equal D D' ->
  wf_ftyp tenv D t ->
  wf_ftyp tenv D' t.
Proof.
  induction t; simpl; intros; eauto.
  { inv H0. econstructor; eauto. rewrite H in *; crush. eapply wf_typ_equal; eauto. }
  { inv H0; econstructor; eauto. }
  { inv H0. econstructor; eauto. rewrite H in *; crush. }
Qed.

Lemma wf_ftyps_equal : forall t D D' tenv,
  Nenv.Equal D D' ->
  wf_ftyps tenv D t ->
  wf_ftyps tenv D' t.
Proof.
  induction t; simpl; intros; eauto.
  inv H0. econstructor; eauto. eapply wf_ftyp_equal; eauto.
Qed.

Lemma wf_fparams_eq2 : forall params sig C D G D',
  wf_fparams C D params sig G ->
  Nenv.Equal D D' ->
  wf_fparams C D' params sig G.
Proof.
  induction params; destruct sig; simpl; intros.
  { inv H. crush. }
  { inv H. }
  { inv H. }
  { inv H. econstructor; eauto. eapply wf_ftyps_equal; eauto. }
Qed.

Lemma wf_ec_stk_ret2 : forall fs lo tenv FD FT P x t D1 D2 G b l stk lsD lsG env rmap_e rmap_b rgns live bs rt f o prgns args HT t',
  wf_ec_stk (mk_config fs lo tenv) FD FT (mk_ec f b nil 
    (Insn_nd (Insn_call (Some x) (Some t') o prgns args l)) env HT rmap_e rmap_b rgns live) (D1,D2) G stk lsD lsG ->
  wf_value fs lo tenv live HT rt (sigma rmap_b (flatten_typ lo tenv t')) ->
  wf_term (mk_config fs lo tenv) D2 P (Nenv.add x (flatten_typ lo tenv t) G) bs (b_lab b) (Insn_br_uncond l) -> 
  wf_ec_stk (mk_config fs lo tenv) FD FT (mk_ec f b nil (Insn_term (Insn_br_uncond l))
    (Nenv.add x rt env) HT rmap_e rmap_b rgns live) (D1,D2) (Nenv.add x (flatten_typ lo tenv t') G) stk lsD lsG.
Proof.
  intros. inv H; econstructor; eauto. 
  { eapply wf_ec_env_val_ext; eauto with ec_ext_db2. }
  { eapply wf_ec_env_val_ext; eauto with ec_ext_db2. }
  { inv H17; eauto. }
Qed.

Lemma mstep_return_pres : forall fs lo tenv f b t o env HT rmap_e rmap_b rgns live f' b' x' t' o' prgns' args' l' env' HT' rmap_e' rmap_b' rgns' live' stk mem mem' HT'' live'' rt,
  wf_ms (mk_config fs lo tenv) 
    (mk_mstate mem (mk_ec f b nil (Insn_term (Insn_return t o)) env HT rmap_e rmap_b rgns live) ((mk_ec f' b' nil (Insn_nd (Insn_call (Some x') (Some t') o' prgns' args' l')) env' HT' rmap_e' rmap_b' rgns' live')::stk)) ->
  del_regions mem lo live HT' HT rgns = Some (mem', HT'', live'') ->
  op2rtv o env = Some rt ->
  wf_ms (mk_config fs lo tenv) 
    (mk_mstate mem' (mk_ec f' b' nil (Insn_term (Insn_br_uncond l')) (Nenv.add x' (weaken_val rt (flatten_typ lo tenv t')) env') HT'' rmap_e' rmap_b' rgns' live'') stk).
Proof.
  intros. t_pres_init; simpl in *. inv H21; simpl in *.
  inv H32; simpl in *; try contradiction. 

  inv H26; simpl in *.

  assert (t = t0 /\ wf_ftyps tenv D1 (flatten_typ lo tenv t)). 
  eapply stepret_typ in H5; eauto. t_simp. subst.
  assert (D1 = x0) by crush. rewrite H. split; eauto. destruct H; subst.

  econstructor; eauto.
  t_dup H0. eapply del_regions_prop in H0. t_simp. apply app_inv_head in H. subst.
  eapply wf_ec_stk_ret2 with (rt := (weaken_val rt (flatten_typ lo tenv t''))) (lsD := lsD0) (lsG := lsG0); eauto. 
  eapply wf_ec_stk_proj_top in H33. inv H33. t_simp. simpl in *. subst.
  
  eapply wf_op_val in H12; eauto. t_simp. inv H5. t_simp. simpl in *. subst.
  assert (x0 = rt) by crush. subst. 
  erewrite <- sigma_same1 in H0; eauto.
  eapply wf_val_live_ctr in H0; eauto.
  erewrite sigma_same2 in H0; eauto.
  eapply wf_val_ftyps_weaken; eauto. 
  
  t_dup H0. eapply del_regions_prop in H0. t_simp. subst.
  apply app_inv_head in H. subst.
  eapply del_regions_wf_mem; eauto. 
  eapply wf_ec_stk_proj_top in H33. inv H33. t_simp; simpl in *; auto.
  eapply del_regions_wf_meta; eauto.
(*  
  inv H25; simpl in *.
  assert (t = t0 /\ wf_ftyps tenv D1 (flatten_typ lo tenv t)). 
  eapply stepret_typ in H5; eauto. t_simp. subst.
  assert (D1 = x0) by crush. rewrite H. split; eauto. destruct H; subst.
  
  econstructor; eauto.
  
  t_dup H0. eapply del_regions_prop in H0. t_simp. apply app_inv_head in H. subst.
  eapply wf_ec_stk_ret with (rt := rt) (lsD := lsD0) (lsG := lsG0); eauto. 
  eapply wf_ec_stk_proj_top in H33. inv H33. t_simp. simpl in *. subst.
  
  eapply wf_op_val in H12; eauto. t_simp. inv H5. t_simp. simpl in *. subst.
  assert (x0 = rt) by crush. subst. 
  erewrite <- sigma_same1 in H0; eauto.
  eapply wf_val_live_ctr in H0; eauto.
  erewrite sigma_same2 in H0; eauto.
  
  t_dup H0. eapply del_regions_prop in H0. t_simp. subst.
  apply app_inv_head in H. subst.
  eapply del_regions_wf_mem; eauto. 
  eapply wf_ec_stk_proj_top in H33. inv H33. t_simp; simpl in *; auto.
  eapply del_regions_wf_meta; eauto.
*)
Qed.

Lemma mstep_return_void_pres : forall fs lo tenv f b env HT rmap_e rmap_b rgns live f' b' o' prgns' args' l' env' HT' rmap_e' rmap_b' rgns' live' stk mem mem' HT'' live'',
  wf_ms (mk_config fs lo tenv) 
    (mk_mstate mem (mk_ec f b nil (Insn_term (Insn_return_void)) env HT rmap_e rmap_b rgns live) ((mk_ec f' b' nil (Insn_nd (Insn_call None None o' prgns' args' l')) env' HT' rmap_e' rmap_b' rgns' live')::stk)) ->
  del_regions mem lo live HT' HT rgns = Some (mem', HT'', live'') ->
  wf_ms (mk_config fs lo tenv) 
    (mk_mstate mem' (mk_ec f' b' nil (Insn_term (Insn_br_uncond l')) env' HT'' rmap_e' rmap_b' rgns' live'') stk).
Proof.
  intros. t_pres_init; simpl in *. inv H20. inv H29; simpl in *; try contradiction.
  inv H31; simpl in *.
  
  econstructor; eauto.
  t_dup H0. apply del_regions_prop in H0. t_simp. apply app_inv_head in H. subst.
  eapply wf_ec_stk_ret_void with (lsD := lsD0) (lsG := lsG0); eauto.
  t_dup H0. apply del_regions_prop in H0. t_simp. apply app_inv_head in H. subst.
  eapply del_regions_wf_mem; eauto.
  eapply wf_ec_stk_proj_top in H30; eauto. inv H30; t_simp; simpl in *. auto. 
  eapply del_regions_wf_meta; eauto.
Qed.

Lemma mstep_br_uncond_pres : forall fs lo tenv f b env HT rmap_e rmap_b rgns live b' env' stk mem,
  wf_ms (mk_config fs lo tenv) 
    (mk_mstate mem (mk_ec f b nil (Insn_term (Insn_br_uncond (b_lab b'))) env HT rmap_e rmap_b rgns live) stk) ->
  update_phis lo tenv env (b_lab b) (b_phis b') = Some env' ->
  lookup_blk (b_lab b') (f_body f) = Some b' ->
  wf_ms (mk_config fs lo tenv) 
    (mk_mstate mem (mk_ec f b' (b_insns b') (b_nd_term b') env' HT rmap_e rmap_b rgns live) stk).
Proof.
  intros. t_pres_init; simpl in *. 
  assert (lookup_fun (f_lab f) fs = Some f).
  apply wf_ec_stk_proj_top in H21. apply wf_ec_proj_fun in H21. eauto.
  inversion H9; subst. eapply evalbr_blk_prop in H9; eauto. t_simp.
  assert (x3 = x0) by crush. subst.
  assert (b' = x0) by crush. subst.
  econstructor; eauto.
  eapply wf_ec_stk_top_diff; eauto.
  t_norm. eapply wf_ec_stk_proj_top in H21. inv H21; simpl in *. t_simp. 
  subst. eapply evalbr_wf_ec; eauto.
  destruct (b_nd_term x0); crush. destruct t; crush. 
Qed.

Ltac t_canonical :=
  repeat 
    match goal with
      | [ H : match ?X with 
                | Some _ => _ 
                | None => _ 
              end = Some _ |- _ ] => destruct X
      | [ H : match ?X with 
                | Some _ => _ 
                | None => _ 
              end |- _ ] => destruct X
      | [ H : match ?X with
                | nil => _
                | _ :: _ => _
              end = Some _ |- _ ] => destruct X
      | [ H : match ?X with
                | nil => _
                | _ :: _ => _
              end |- _ ] => destruct X
      | [ H : match ?X with
                | RT_int _ _ _ => _ 
                | RT_fun _ => _
                (* | RT_ptr _ => _ *)
                (* | RT_float _ => _ *)
              end = Some _ |- _ ] => destruct X
      | [ H : match ?X with
                | RT_int _ _ _ => _ 
                | RT_fun _ => _
                (* | RT_ptr _ => _ *)
                (* | RT_float _ => _ *)
              end |- _ ] => destruct X
      | [ H: context [ eq_nat_dec ?n1 ?n2 ] |- _ ] =>
        destruct (eq_nat_dec n1 n2)
    end; try congruence; subst.

Lemma mstep_br_pres : forall fs lo tenv f b env HT rmap_e rmap_b rgns live b' env' stk mem o l1 l2,
  wf_ms (mk_config fs lo tenv) 
    (mk_mstate mem (mk_ec f b nil (Insn_term (Insn_br o l1 l2)) env HT rmap_e rmap_b rgns live) stk) ->
  update_phis lo tenv env (b_lab b) (b_phis b') = Some env' ->
  eval_br env (f_body f) o l1 l2 = Some b' ->
  wf_ms (mk_config fs lo tenv) 
    (mk_mstate mem (mk_ec f b' (b_insns b') (b_nd_term b') env' HT rmap_e rmap_b rgns live) stk).
Proof.
  intros. t_pres_init; simpl in *. unfold eval_br in *.
  consider (op2rtv o env); intros; try congruence. 
  assert (lookup_fun (f_lab f) fs = Some f). 
  apply wf_ec_stk_proj_top in H21. apply wf_ec_proj_fun in H21. auto.
  destruct_c r. destruct_c r. destruct_c sz. destruct_c r0. destruct Word.eq_dec.
  { inversion H12; subst. t_simp. 
    assert (l1 = b_lab x1). eapply lookup_blk_spec; eauto. subst. 
    eapply evalbr_blk_prop in H12; eauto. t_simp. t_norm.
    econstructor; eauto. eapply wf_ec_stk_top_diff; eauto.
    eapply wf_ec_stk_proj_top in H21. inv H21. t_simp. eapply evalbr_wf_ec; eauto.
    destruct (b_nd_term x2); crush. destruct t; crush. }
  { inversion H13; subst. t_simp.
    assert (l2 = b_lab x1). eapply lookup_blk_spec; eauto. subst.
    eapply evalbr_blk_prop in H13; eauto. t_simp. t_norm.
    econstructor; eauto. eapply wf_ec_stk_top_diff; eauto.
    eapply wf_ec_stk_proj_top in H21. inv H21. t_simp. eapply evalbr_wf_ec; eauto.
    destruct (b_nd_term x2); crush. destruct t; crush. }
Qed.

Lemma mstep_switch_pres : forall fs lo tenv f b env HT rmap_e rmap_b rgns live b' env' stk mem o ldef ls t,
  wf_ms (mk_config fs lo tenv) 
    (mk_mstate mem (mk_ec f b nil (Insn_term (Insn_switch t o ldef ls)) env HT rmap_e rmap_b rgns live) stk) ->
  update_phis lo tenv env (b_lab b) (b_phis b') = Some env' ->
  eval_switch env (f_body f) o ldef ls = Some b' ->
  wf_ms (mk_config fs lo tenv) 
    (mk_mstate mem (mk_ec f b' (b_insns b') (b_nd_term b') env' HT rmap_e rmap_b rgns live) stk).
Proof.
  intros. t_pres_init; simpl in *. 
  assert (lookup_fun (f_lab f) fs = Some f). 
  apply wf_ec_stk_proj_top in H21. apply wf_ec_proj_fun in H21. auto.
  eapply wf_switch_prop in H1; eauto. t_simp. inversion H1; subst. t_simp.
  eapply evalbr_blk_prop in H1; eauto. t_simp. t_norm.
  econstructor; eauto. eapply wf_ec_stk_top_diff; eauto.
  eapply wf_ec_stk_proj_top in H21. inv H21. t_simp.
  simpl in *. eapply evalbr_wf_ec; eauto.
  destruct (b_nd_term x2); crush. destruct t; crush.
Qed.

Lemma mstep_indirect_br_pres : forall fs lo tenv f b env HT rmap_e rmap_b rgns live b' env' stk mem o ls t,
  wf_ms (mk_config fs lo tenv) 
    (mk_mstate mem (mk_ec f b nil (Insn_term (Insn_indirect_br t o ls)) env HT rmap_e rmap_b rgns live) stk) ->
  update_phis lo tenv env (b_lab b) (b_phis b') = Some env' ->
  eval_indirect_br env (f_body f) o ls = Some b' ->
  wf_ms (mk_config fs lo tenv) 
    (mk_mstate mem (mk_ec f b' (b_insns b') (b_nd_term b') env' HT rmap_e rmap_b rgns live) stk).
Proof.
  intros. t_pres_init; simpl in *. 
  assert (lookup_fun (f_lab f) fs = Some f). 
  apply wf_ec_stk_proj_top in H21. apply wf_ec_proj_fun in H21. auto.
  eapply wf_indirect_br_prop in H1; eauto. t_simp. inversion H1; subst. t_simp.
  eapply evalbr_blk_prop in H1; eauto. t_simp. t_norm.
  econstructor; eauto. eapply wf_ec_stk_top_diff; eauto.
  eapply wf_ec_stk_proj_top in H21. inv H21. t_simp.
  simpl in *. eapply evalbr_wf_ec; eauto.
  destruct (b_nd_term x2); crush. destruct t; crush.
Qed.

Lemma mstep_malloc_pres : forall fs lo tenv f b env HT rmap_e rmap_b rgns live stk mem x t r o l rt mem',
  wf_ms (mk_config fs lo tenv) 
    (mk_mstate mem (mk_ec f b nil (Insn_nd (Insn_malloc x t r o l)) env HT rmap_e rmap_b rgns live) stk) ->
  eval_malloc env mem lo tenv live rmap_b HT r t o = Some (rt, mem') ->
  wf_ms (mk_config fs lo tenv) 
    (mk_mstate mem' (mk_ec f b nil (Insn_term (Insn_br_uncond l)) (Nenv.add x rt env) HT rmap_e rmap_b rgns live) stk).
Proof.
  intros. t_pres_init; simpl in *. 
  { t_dup H0. eapply evalmalloc_pres in H0; eauto. t_simp. econstructor; eauto. 
    eapply wf_ec_stk_env_ext; eauto. eapply wf_ec_stk_malloc; eauto.
    eapply evalmalloc_wf_meta; eauto. eapply wf_typ_TS; eauto. }
  { t_dup H0. eapply evalmalloc_presU in H0; eauto. t_simp. econstructor; eauto.
    eapply wf_ec_stk_env_ext; eauto. eapply wf_ec_stk_malloc; eauto.
    eapply evalmalloc_wf_meta; eauto. }
  { t_dup H0. eapply evalmalloc_presU2 in H0; eauto. t_simp. econstructor; eauto.
    eapply wf_ec_stk_env_ext; eauto. eapply wf_ec_stk_malloc; eauto.
    eapply evalmalloc_wf_meta; eauto. }
Qed.

Lemma mstep_call_pres : forall fs lo tenv f b x t o l env HT rmap_e rmap_b rgns live f' b' env' HT' rmap_e' rmap_b' rgns' live' stk mem mem' args prgns lrgns fid',
  wf_ms (mk_config fs lo tenv) 
    (mk_mstate mem (mk_ec f b nil (Insn_nd (Insn_call x t o prgns args l)) env HT rmap_e rmap_b rgns live) stk) ->
  op2fun o env = Some fid' ->
  lookup_fun fid' fs = Some f' ->
  lookup_blk fid' (f_body f') = Some b' ->
  init_fun env lo tenv (f_params f') (f_sig f') args = Some env' ->
  bind_prgn (domain (f_prgn f')) prgns rmap_b = Some rmap_e' ->
  bind_lrgn lrgns rmap_e' = rmap_b' ->
  freshn fresh_ctr live (f_lrgn f') = Some (lrgns, live', rgns') ->
  new_regions mem lo tenv rmap_b' live rgns' HT (f_lrgn f') = Some (mem', HT') ->
  fid' <> Word.repr 0 ->
  new_regions mem lo tenv (bind_lrgn lrgns rmap_e') live rgns' HT (f_lrgn f') = Some (mem', HT') ->
  wf_ms (mk_config fs lo tenv) 
    (mk_mstate mem' (mk_ec f' b' (b_insns b') (b_nd_term b') env' HT' rmap_e' rmap_b' rgns' live') ((mk_ec f b nil (Insn_nd (Insn_call x t o prgns args l)) env HT rmap_e rmap_b rgns live)::stk)).
Proof.
  intros. t_pres_init; simpl in *. eapply evalcall_fun_prop in H36; eauto.
  destruct H36. unfold Word.zero in H. congruence.
  t_simp. econstructor; eauto.
  
  assert (fid' = f_lab f'). eapply lookup_fun_spec; eauto. subst.
  assert (f_lab f' = b_lab b'). eapply lookup_blk_spec; eauto.
  rewrite H16 in H2.
  
  eapply SVAmem.freshn_prop in H6. t_simp. subst. t_dup H29.
  eapply wf_ec_stk_proj_top in H29. inv H29. t_simp; simpl in *. subst.
  t_dup H7. eapply SVAmem.new_regions_prop in H7; eauto. t_simp.
  
  rewrite H6 in H18.
  rewrite H6 in H21.
  
  t_dup H4. eapply bind_prgn_spec1 in H'3; eauto.
  t_dup H4. eapply bind_prgn_spec2 in H'4; eauto.
  t_dup H4. eapply bind_prgn_spec3 in H'5; eauto.
  t_dup H'5. eapply bind_lrgn_spec1 in H'6; eauto.
  t_dup H'5. eapply bind_lrgn_spec2 in H'7; eauto.
  eapply wf_ftyps_closed_ls in H39; eauto.
      
  econstructor; eauto.
  
  unfold wf_ec; simpl. exists f'. exists b'.
  repeat (split; eauto).
  destruct (b_nd_term b'); eauto. destruct t; crush.
  eapply wf_env_live_ext; eauto.
  eapply wf_env_HT_ext; eauto.
  eapply init_fun_spec with (D := D2); eauto. 
  apply NFacts.Equal_sym in H10.
  eapply wf_fparams_eq with (G' := x1) in H11; eauto.
  eapply wf_fparams_eq2; eauto.
  eapply new_regions_wf_HT_live in H'2; eauto.
  eapply new_regions_wf_mem; eauto.
  eapply new_regions_wf_mem; eauto.
  eapply new_regions_wf_mem; eauto.
  eapply new_regions_wf_HT_bounds in H'2; eauto.
  unfold wf_HT_bounds in *. crush. 
  eapply new_regions_wf_HT_bounds in H'2; eauto.
  unfold wf_HT_bounds in *. crush. 
  eapply wf_rmap_delta_eq; eauto. crush.
  exists nil; eauto.
  eapply wf_rmap_delta_eq; eauto. crush.
  
  eapply new_regions_wf_HT_bounds in H'2; eauto.
  unfold wf_HT_bounds in *. crush.
  
  econstructor; simpl; eauto. destruct (b_nd_term b'); eauto.
  destruct t; crush.
  
  eapply wf_rmap_delta_eq; eauto. crush.

  eapply SVAmem.freshn_prop in H6. t_simp. subst.
  eapply new_regions_wf_mem; eauto.
  
  eapply new_regions_wf_meta; eauto.

  (* call void *)
  inv H14; simpl in *.
  eapply evalcall_fun_prop2 in H36; eauto.
  destruct H36. unfold Word.zero in H. congruence.
  t_simp. econstructor; eauto.
  
  assert (fid' = f_lab f'). eapply lookup_fun_spec; eauto. subst.
  assert (f_lab f' = b_lab b'). eapply lookup_blk_spec; eauto.
  rewrite H15 in H2.
  
  eapply SVAmem.freshn_prop in H6. t_simp. subst. t_dup H29.
  eapply wf_ec_stk_proj_top in H29. inv H29. t_simp; simpl in *. subst.
  t_dup H7. eapply SVAmem.new_regions_prop in H7; eauto. t_simp.
  
  rewrite H6 in H17.
  rewrite H6 in H20.
  
  t_dup H4. eapply bind_prgn_spec1 in H'3; eauto.
  t_dup H4. eapply bind_prgn_spec2 in H'4; eauto.
  t_dup H4. eapply bind_prgn_spec3 in H'5; eauto.
  t_dup H'5. eapply bind_lrgn_spec1 in H'6; eauto.
  t_dup H'5. eapply bind_lrgn_spec2 in H'7; eauto.
  eapply wf_ftyps_closed_ls in H41; eauto.
  
  econstructor; eauto.
    
  unfold wf_ec; simpl. exists f'. exists b'.
  repeat (split; eauto).
  destruct (b_nd_term b'); eauto. destruct t; crush.
  eapply wf_env_live_ext; eauto.
  eapply wf_env_HT_ext; eauto.
  eapply init_fun_spec with (D := D2); eauto. 
  apply NFacts.Equal_sym in H10.
  eapply wf_fparams_eq with (G' := x0) in H11; eauto.
  eapply wf_fparams_eq2; eauto.
  eapply new_regions_wf_HT_live in H'2; eauto.
  eapply new_regions_wf_mem; eauto.
  eapply new_regions_wf_mem; eauto.
  eapply new_regions_wf_mem; eauto.
  eapply new_regions_wf_HT_bounds in H'2; eauto.
  unfold wf_HT_bounds in *. crush. 
  eapply new_regions_wf_HT_bounds in H'2; eauto.
  unfold wf_HT_bounds in *. crush. 
  eapply wf_rmap_delta_eq; eauto. crush.
  exists nil; eauto.
  eapply wf_rmap_delta_eq; eauto. crush.
  
  eapply new_regions_wf_HT_bounds in H'2; eauto.
  unfold wf_HT_bounds in *. crush.
  
  eapply wf_call_return_void; simpl; eauto. destruct (b_nd_term b'); eauto.
  destruct t; crush.
  
  eapply wf_rmap_delta_eq; eauto. crush.
  
  eapply SVAmem.freshn_prop in H6. t_simp. subst.
  eapply new_regions_wf_mem; eauto.
  
  eapply new_regions_wf_meta; eauto.
Qed.
  
(* We have preservation as long as we don't have unsafe calls *) 
Theorem preservation : forall fs lo tenv m f b env HT rmap_e rmap_b rgns live stk insns ndt,
  wf_ms (mk_config fs lo tenv) (mk_mstate m (mk_ec f b insns ndt env HT rmap_e rmap_b rgns live) stk) ->
  forall m' f' b' env' HT' rmap_e' rmap_b' rgns' live' stk' insns' ndt' bhalt,
  mstep (mk_config fs lo tenv) (mk_mstate m (mk_ec f b insns ndt env HT rmap_e rmap_b rgns live) stk)
  (mk_mstate m' (mk_ec f' b' insns' ndt' env' HT' rmap_e' rmap_b' rgns' live') stk') bhalt ->
  (forall xt op os l, ndt <> Insn_nd (Insn_unsafe_call xt op os l)) ->
  wf_ms (mk_config fs lo tenv) (mk_mstate m' (mk_ec f' b' insns' ndt' env' HT' rmap_e' rmap_b' rgns' live') stk').
Proof.
  intros. inv H0; auto.
  
  (* return *)
  { eapply mstep_return_pres; eauto. }
    
  (* return_void *)
  { eapply mstep_return_void_pres; eauto. }

  (* br_uncond *)
  { eapply mstep_br_uncond_pres; eauto. }
  
  (* br, same as br_uncond *)
  { eapply mstep_br_pres; eauto. }
    
  (* switch *)
  { eapply mstep_switch_pres; eauto. }

  (* indirect branch *)
  { eapply mstep_indirect_br_pres; eauto. }

  (* malloc - succeed *)
  { eapply mstep_malloc_pres; eauto. }

  (* call *)
  { eapply mstep_call_pres; eauto. }

  (* eval_blk *)
  { apply preservation_eval in H. inversion H; crush. }

  (* unsafe_call *)
  { specialize (H1 xt op os l). crush. }
Qed.

(* ---------------------------------------------------------------------- *)
(** * Progress *)


(* ---------------------------------------------------------------------- *)
(** * Non-deterministic Instruction Helper Lemmas *)

Lemma evalcall_notstuck : forall fs lo tenv FT FD D P o env G HT prgns sig ret live rmap,
  wf_operand (mk_config fs lo tenv) D P G o (Ftyp_fun prgns sig ret :: nil) ->
  wf_env (mk_config fs lo tenv) live HT rmap env G ->
  wf_functions (mk_config fs lo tenv) FT FD ->
  (exists fid, op2fun o env = Some fid /\ 
    fid = Word.zero) \/
  (exists f, 
    op2fun o env = Some (f_lab f) /\
    lookup_fun (f_lab f) fs = Some f /\
    f_sig f = sig /\
    f_ret f = ret /\
    domain (f_prgn f) = prgns).
Proof.
  intros. unfold op2fun. unfold op2rtv. inv H.
  { unfold wf_env in H0. apply H0 in H2. t_simp. t_dup H2. 
    apply canonical_form_fun in H2. destruct H2; subst.
    rewrite H. eauto. t_simp. subst. rewrite H. 
    simpl in *. inv H'. inv H8. t_norm.
    specialize (lookup_fun_spec _ _ _ H3); intros. subst. eauto 10. }
  { inv H2. simpl. eauto 10. inv H. inv H4. }
Qed.

Lemma evalcall_notstuck2 : forall args live rmap rmap2 env params fs lo tenv sig G1 G2 m P D D2,
  wf_args (mk_config fs lo tenv) D P G1 rmap2 args sig ->
  wf_env (mk_config fs lo tenv) m live rmap env G1 ->
  wf_fparams (mk_config fs lo tenv) D2 params sig G2 ->
  exists env', init_fun env lo tenv params sig args = Some env'.
Proof.
  induction args; crush. inv H. inv H1. unfold init_fun. eauto. 
  inversion H; subst. inversion H1; subst. simpl in *. 
  remember (init_fun env lo tenv ids sig' args) as Hd. destruct Hd; crush.
  symmetry in HeqHd. eapply wf_op_val in H14; eauto. t_simp. rewrite H2.
  eauto. eapply IHargs; eauto.
Qed.

Lemma evalcall_notstuck3 : forall prgn1 prgn2 rmap D live,
  length prgn1 = length prgn2 ->
  wf_rmap D live rmap ->
  wf_prgn_inst D prgn2 ->
  exists rmap', bind_prgn prgn1 prgn2 rmap = Some rmap'.
Proof.
  induction prgn1; crush. destruct prgn2; crush. eauto.
  destruct prgn2; crush. inv H1. eapply IHprgn1 in H; eauto.
  t_simp. rewrite H. unfold wf_rmap in H0. apply H0 in H5. t_simp.
  rewrite H1. eauto.
Qed.
 
Lemma evalcall_notstuck4 : forall lrgns rmap,
  exists rmap', bind_lrgn lrgns rmap = rmap'.
Proof.
  induction lrgns; crush; eauto.
Qed.

Lemma evalmalloc_notstuck : forall fs lo tenv FT FD D P bs l1 l2 x t r o G env mem rmap live HT,
  wf_insns_ndterm (mk_config fs lo tenv) D P bs l1 nil (Insn_nd (Insn_malloc x t r o l2)) G ->
  wf_functions (mk_config fs lo tenv) FT FD ->
  wf_env (mk_config fs lo tenv) live HT rmap env G ->
  (exists rt, exists mem', eval_malloc env mem lo tenv live rmap HT r t o = Some (rt, mem')) \/ 
  eval_malloc env mem lo tenv live rmap HT r t o = None.
Proof.
  intros. inv H. unfold eval_malloc in *. Opaque op2rtv. inv H8; t_insn_simpl_pro;
  match goal with
    | [ |- context [ match alloc ?mem ?lo ?live ?HT ?t ?i ?r with
                       | Some _ => _
                       | None => _
                     end ] ] => 
    let H' := fresh "H'" in
      case_eq (alloc mem lo live HT t i r); intros; eauto
  end; destruct p; eauto. Transparent op2rtv.
Qed.

Lemma evalbr_notstuck : forall C D P G o m env l1 l2 bs b1 b2 live rmap,
  wf_operand C D P G o (Ftyp_int1 :: nil) ->
  wf_env C m live rmap env G ->
  lookup_blk l1 bs = Some b1 ->
  lookup_blk l2 bs = Some b2 ->
  eval_br env bs o l2 l1 = Some b1 \/ 
  eval_br env bs o l2 l1 = Some b2.
Proof.
  intros. unfold eval_br. unfold Ftyp_int1 in H. destruct C. t_insn_simpl_pro. destruct Word.eq_dec; auto.
Qed.

Lemma update_phis_notstuck : forall phis fs lo tenv D P l G1 G2 env HT live rmap,
  wf_phi_blk (mk_config fs lo tenv) D P phis l G1 G2 ->
  wf_env (mk_config fs lo tenv) live HT rmap env G1 ->
  wf_rmap D live rmap ->
  wf_tenv tenv ->
  exists env', update_phis lo tenv env l phis = Some env'.
Proof.
  induction phis; simpl; intros; eauto. 
  inv H. destruct a. eapply update_phi_spec in H8; eauto. t_simp. rewrite H. eauto.
Qed.

Lemma evalswitch_notstuck : forall ls C D P G m env bs live rmap ldef sz pf o l,
  wf_junction C D P G bs l ldef ->
  wf_operand C D P G o (Ftyp_int sz pf :: nil) ->
  wf_env C m live rmap env G ->
  wf_switch_arms C D P G bs (Typ_int sz pf) l ls ->
  exists b, eval_switch env bs o ldef ls = Some b.
Proof.
  induction ls; intros. inv H. t_simp. eauto. destruct C; simpl in *.
  destruct a. destruct p. t_dup H0. eapply wf_op_val in H0; eauto. t_simp.
  eapply canonical_form_int in H3. t_simp. subst. rewrite H0. inv H2.
  destruct_c eq_nat_dec. destruct Word.eq_dec; subst. 
  inv H12. t_simp. eauto. eapply IHls; eauto.
  assert (pf1 = pf). apply proof_irr. subst. auto.
Qed.

Lemma del_regions_prog2 : forall ec_HT HT m lo rgns ec_live,
  wf_HT_bounds ec_HT ->
  wf_mem_metadata HT m ->
  max_HT ec_HT <= max_HT HT ->
  exists m', exists live', exists HT',
    del_regions m lo (rgns ++ ec_live) ec_HT HT rgns = Some (m', live', HT').
Proof.
  intros. unfold wf_HT_bounds in H. unfold wf_mem_metadata in H0. destruct H.
  eapply SVAmem.del_regions_prog; eauto. omega.
Qed.

Ltac t_eval_cases :=
  match goal with
    | [ H : match ?X with
              | Some _ => _ 
              | None => _ 
            end = _ |- _ ] => destruct_c X
    | [ H : match ?X with
              | Load_SvaErr => _
              | Load_MemErr => _
              | Load_Val _ => _
            end = _ |- _ ] => destruct_c X
    | [ H : match ?X with
              | Store_SvaErr => _
              | Store_MemErr => _
              | Store_Val _ => _ 
            end = _ |- _ ] => destruct_c X
  end.

Lemma evalblk_term : forall lo fs insns m f b t env stk ms HT rmap_e rmap_b rgns live,
  eval_blk lo fs insns (mk_mstate m (mk_ec f b insns t env HT rmap_e rmap_b rgns live) stk) = Delay ms ->
  ec_term (s_cec ms) = t.
Proof.
  induction insns; simpl; intros; auto.
  { inv H. simpl. auto. } 
  { destruct a; try t_eval_cases; eauto; try congruence. 
    destruct_c o. t_eval_cases; eauto.
    destruct_c o. t_eval_cases; eauto. }
Qed.

Lemma progress : forall fs lo tenv m f b insns env HT rmap_e rmap_b rgns live stk t,
  wf_ms (mk_config fs lo tenv) (mk_mstate m (mk_ec f b insns t env HT rmap_e rmap_b rgns live) stk) ->
  (exists f', exists b', exists t', exists insns', exists env', exists HT', exists rmap_e', exists rmap_b', exists rgns', exists live', exists m', exists stk', 
    mstep 
    (mk_config fs lo tenv) 
    (mk_mstate m (mk_ec f b insns t env HT rmap_e rmap_b rgns live) stk)
    (mk_mstate m' (mk_ec f' b' insns' t' env' HT' rmap_e' rmap_b' rgns' live') stk')
    false) \/
  final_state (mk_mstate m (mk_ec f b insns t env HT rmap_e rmap_b rgns live) stk) \/
  mstep
    (mk_config fs lo tenv)
    (mk_mstate m (mk_ec f b insns t env HT rmap_e rmap_b rgns live) stk)
    (mk_mstate m (mk_ec f b insns t env HT rmap_e rmap_b rgns live) stk)
    true.
Proof.
  intros. 

  (* nd/term v. eval *)
  destruct insns. 

  (* nd case *)
  destruct t.

  destruct i.
  (* call *)
  t_pres_init; simpl in *. 
  eapply evalcall_notstuck in H27; eauto. 
  destruct H27. t_simp. 

  right. right. eauto 20.

  t_simp. subst.
 
  destruct (Word.eq_dec (f_lab x0) (Word.repr 0)).
  right. right. eauto 20.

  eapply wf_ec_stk_proj_top in H19. unfold wf_ec in H19; simpl in *; t_simp.
  eapply evalcall_notstuck3 in H26; eauto. t_simp. subst.
  specialize (freshn_prog fresh_ctr live (f_lrgn x0)); intros. destruct H1.
  right. right. eauto.

  t_simp.
  specialize (evalcall_notstuck4 x1 x4); intros. t_simp.
  specialize (new_regions_prog m lo tenv (bind_lrgn x1 x4) live x5 HT (f_lrgn x0)); intros.
  destruct H27; eauto.
  right. right. eapply Mstep_call_fail2; eauto.
  left. t_simp. unfold wf_functions in H18. t_simp.
  t_dup H0. apply H18 in H0. t_simp. unfold wf_function in H31. t_simp.
  subst. 
  eapply evalcall_notstuck2 in H35; eauto. t_simp.
  unfold wf_fbody in H42. t_simp. apply H43 in H31. t_simp.
  eauto 20.
   
  (* call void *)
  eapply evalcall_notstuck in H24; eauto. 
  destruct H24. t_simp. 

  right. right. eauto 20.

  t_simp. subst.
 
  destruct (Word.eq_dec (f_lab x) (Word.repr 0)).
  right. right. eauto 20.

  eapply wf_ec_stk_proj_top in H19. unfold wf_ec in H19; simpl in *; t_simp.
  eapply evalcall_notstuck3 in H26; eauto. t_simp. subst.
  specialize (freshn_prog fresh_ctr live (f_lrgn x)); intros. destruct H1.
  right. right. eauto.

  t_simp.
  specialize (evalcall_notstuck4 x0 x3); intros. t_simp.
  specialize (new_regions_prog m lo tenv (bind_lrgn x0 x3) live x4 HT (f_lrgn x)); intros.
  destruct H27; eauto.
  right. right. eapply Mstep_call_fail2; eauto.
  left. t_simp. unfold wf_functions in H18. t_simp.
  t_dup H0. apply H18 in H0. t_simp. unfold wf_function in H29. t_simp.
  subst. 
  eapply evalcall_notstuck2 in H33; eauto. t_simp.
  unfold wf_fbody in H40. t_simp. apply H41 in H29. t_simp.
  eauto 20.

  (* malloc - success *)
  t_pres_init; simpl in *. 
  eapply evalmalloc_notstuck in H18; eauto. 
  destruct H18; eauto 20.
  t_simp; eauto 20.

  eapply evalmalloc_notstuck in H18; eauto. 
  destruct H18; eauto 20.
  t_simp; eauto 20.

  eapply evalmalloc_notstuck in H18; eauto. 
  destruct H18; eauto 20.
  t_simp; eauto 20.

  (* unsafe_call *)
  eauto 20.

  (* term case *)
  destruct t.

  (* return *)
  t_pres_init; simpl in *.
  inv H19. simpl. right. left. eauto. left. destruct ecbot. 
  inv H1; simpl in *. 

  eapply wf_op_val in H10; eauto. t_simp. subst. inv H25; simpl in *; try intuition.
  eapply wf_ec_stk_proj_top in H30; eauto. unfold wf_ec in H30; simpl in *; t_simp; subst.
  eapply del_regions_prog2 in H41; eauto. t_simp.
  assert (x3 = ec_HT). apply del_regions_prop in H; crush. subst.
  eauto 20.

  (* return_void *)
  t_pres_init; simpl in *. inv H19. right. left. simpl. eauto. left.
  destruct ecbot. inv H1; simpl in *. inv H23; simpl in *; try intuition.
  eapply wf_ec_stk_proj_top in H28; eauto. unfold wf_ec in H28; simpl in *; t_simp; subst.
  eapply del_regions_prog2 in H40; eauto. t_simp.
  assert (x0 = ec_HT). apply del_regions_prop in H; crush. subst.
  eauto 20.

  (* br_uncond *)
  t_pres_init; simpl in *. left. 
  inv H7. t_simp. eapply wf_ec_stk_proj_rmapb in H19. eapply update_phis_notstuck in H2; eauto.
  t_simp. t_dup H0. eapply lookup_blk_spec in H0. eapply ex_intro; eauto 20.
  
  (* br *)
  t_pres_init; simpl in *. left. inv H10. inv H11. t_simp. 
  eapply evalbr_notstuck with (b1 := x2) (b2 := x4) in H12; eauto.
  eapply wf_ec_stk_proj_rmapb in H19.
  destruct H12.

  eapply update_phis_notstuck in H3; eauto. t_simp. eapply ex_intro; eauto 20.
  eapply update_phis_notstuck in H7; eauto. t_simp. eapply ex_intro; eauto 20.

  (* switch *)
  t_pres_init; simpl in *. left.   
  t_dup H13. eapply evalswitch_notstuck in H13; eauto. t_simp. 
  t_dup H. eapply wf_switch_prop in H; eauto. t_simp.
  inversion H; subst. t_simp. 
  eapply wf_ec_stk_proj_rmapb in H19.
  eapply update_phis_notstuck in H4; eauto.
  t_simp. t_norm. eapply ex_intro; eauto 20.

  (* indirectbr *)
  t_pres_init; simpl in *.
  case_eq (eval_indirect_br env (f_body f) o l); intros. t_dup H.
  eapply wf_indirect_br_prop in H; eauto. t_simp.
  inversion H; subst. t_simp. 
  eapply wf_ec_stk_proj_rmapb in H19.
  eapply update_phis_notstuck in H4; eauto.
  t_simp. t_norm. left. eapply ex_intro; eauto 20.

  eauto 20.

  (* unreachable *)
  eauto 20.

  (* eval *)
  inversion H; subst. apply preservation_eval in H. 

  remember (i::insns) as Hd. remember t as Ht. inv H. eauto.

  symmetry in H0. left.

  inv H2.
  assert (t = term). eapply evalblk_term in H0; eauto.
  subst. eapply ex_intro; eauto 20.

  Grab Existential Variables.
  apply rmap_e.
  apply rmap_e.
  apply live.
  apply live.
  apply (Nenv.elements rmap_e).
  apply rmap_e.
  apply rmap_e.
  apply live.
  apply live.
  apply (Nenv.elements rmap_e).
Qed.

Print Assumptions preservation.
Print Assumptions progress.
