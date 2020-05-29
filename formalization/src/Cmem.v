(* Other library imports *)
Add LoadPath "../libs".
Add LoadPath "../libs/CompCert-Toolkit".
Require Import Tactics.
Require Import Consider.

Require Import Bits.
Require Import Coqlib.
Require Import Memory.

(* Illvm imports *)
Require Import Utility.
Require Import IllvmAST.
Require Import IllvmValues.
Require Import TargetData.
Require Import Amem.


Module SVAmem <: MemSig.

  (* Each byte has a shadow_cell *)
  Definition mem_cell := int8%type.
  Definition mem_t := Z -> mem_cell.

  Set Implicit Arguments.
  Definition update := Memory.update.  
  Definition update_s := Memory.update_s.
  Definition update_o := Memory.update_o.

  (*-------------------------------------------------------------------------*)
  (* This section from Compcert, with types changed to our types *)

  Fixpoint getN (p:Z) (n:nat) (c:mem_t) : list mem_cell :=
    match n with
      | O => nil
      | S n' => (c p)::(getN (p + 1) n' c)
    end.
  
  Fixpoint setN (p:Z) (vl:list mem_cell) (c:mem_t) : mem_t :=
    match vl with
      | nil => c
      | v::vl' => setN (p + 1) vl' (update p v c)
    end.

  Remark setN_other:
    forall vl c p q,
      (forall r, p <= r < p + Z_of_nat (length vl) -> r <> q) ->
      setN p vl c q = c q.
  Proof.
    induction vl; intros; simpl.
    auto. 
    simpl length in H. rewrite inj_S in H.
    transitivity (update p a c q).
    apply IHvl. intros. apply H. omega. 
    apply update_o. apply H. omega. 
  Qed.
  
  Remark setN_outside:
    forall vl c p q,
      q < p \/ q >= p + Z_of_nat (length vl) ->
      setN p vl c q = c q.
  Proof.
    intros. apply setN_other. 
    intros. omega. 
  Qed.
  
  Remark getN_setN_same:
    forall vl p c,
      getN p (length vl) (setN p vl c) = vl.
  Proof.
    induction vl; intros; simpl.
    auto.
    decEq. 
    rewrite setN_outside. apply update_s. omega. 
    apply IHvl. 
  Qed.
  
  Remark getN_exten:
    forall c1 c2 n p,
      (forall i, p <= i < p + Z_of_nat n -> c1 i = c2 i) ->
      getN p n c1 = getN p n c2.
  Proof.
    induction n; intros. auto. rewrite inj_S in H. simpl. decEq. 
    apply H. omega. apply IHn. intros. apply H. omega.
  Qed.
  
  Remark getN_setN_outside:
    forall vl q c n p,
      p + Z_of_nat n <= q \/ q + Z_of_nat (length vl) <= p ->
      getN p n (setN q vl c) = getN p n c.
  Proof.
    intros. apply getN_exten. intros. apply setN_outside. omega. 
  Qed.

  (*-------------------------------------------------------------------------*)

  (* Concrete memory *)
  Record cmem' : Type := mk_mem {
    mem: mem_t;
    s_fresh: nat;
    h_addr: nat;
    
    max_addr: Z_of_nat h_addr < Word.max_unsigned WORDSIZE_BITS;
    stuff: forall p, p >= Z_of_nat h_addr -> mem p = Word.zero
  }.
  Definition cmem := cmem'.

  Parameter empty : cmem.
  Definition nullptr : Z := 0.
  
  Definition load (m:cmem) (lo:layout) (n:Z) (t:ftyp) : option rt_tag :=
    if zle n 0 
      then None
      else 
        let mcells := getN n (size_ftyp_nat lo t) (mem m) in
          let bs := mcells in
            if zle (n + size_ftyp lo t) (Z_of_nat (h_addr m))
              then Some (decode_rttag lo t bs)
              else None.
  
  Program Definition store (m:cmem) (lo:layout) (n:Z) (t:ftyp) (v:rt_tag) : option cmem :=
    if zle n 0 
      then None
      else
        let bs := encode_rttag lo v in
          let mcells := getN n (size_ftyp_nat lo t) (mem m) in
            if zle (n + Z_of_nat (length bs)) (Z_of_nat (h_addr m)) 
              then 
                Some (mk_mem (setN n (encode_rttag lo v) (mem m)) (s_fresh m) (h_addr m) (max_addr m) _)
              else None.
  Next Obligation.
    intros. destruct m. simpl in *. assert (H2 := H1).
    rewrite setN_outside. crush. unfold mem_cell in *. omega.  
  Defined.
  
  Definition alloc (m:cmem) (lo:layout) (live:list rgn) (HT:heap_t) (t:ftyps) (s:nat) (r:rgn) : option (PTRTYP*cmem) :=
    match t with
      | nil => None
      | t'::ts => 
        if in_dec rgn_dec r live then
          if check_HT lo HT (Z_of_nat (h_addr m)) r t 
            then Some (Word.repr (Z_of_nat (h_addr m)), mk_mem (mem m) (s_fresh m) (h_addr m) (max_addr m) (stuff m))
            else None
          else None
    end.

  Definition free (m:cmem) (lo:layout) (addr:Z) : option cmem :=
    Some m.

  (* ---------------------------------------------------------------------- *)
  (** * Properties *)
  (* ---------------------------------------------------------------------- *)

  (* ---------------------------------------------------------------------- *)
  (* Load Properties *)
  Lemma load_typ : forall m n t v lo,
    load m lo n t = Some v ->
    match t with
      | Ftyp_float => exists f, v = RT_float f
      | Ftyp_double => exists d, v = RT_double d
      | Ftyp_int sz pf => exists i, v = RT_int sz pf i
      | Ftyp_ptr t' r => exists i, v = RT_ptr i
      | Ftyp_fun p s r => exists l, v = RT_fun l
      | Ftyp_ptrU sz r => exists i, v = RT_ptr i
    end.
  Proof.
    unfold load; intros. destruct (zle n 0); crush.
    destruct (zle (n + size_ftyp lo t) (Z.of_nat (h_addr m))); crush.
    destruct t; crush; eauto.
  Qed.

  Lemma load_null_fail : forall m t lo,
    load m lo 0 t = None.
  Proof.
    unfold load; intros. destruct (zle 0 0); crush.
  Qed.

  Lemma load_ptr_val : forall m n t lo v,
    load m lo n t = Some v ->
    n > 0.
  Proof.
    unfold load; intros. destruct zle; crush.
  Qed.

  Lemma store_ptr_val : forall m lo n t v m',
    store m lo n t v = Some m' ->
    n > 0.
  Proof.
    unfold store; intros. destruct zle; crush.
  Qed.

  (* ---------------------------------------------------------------------- *)
  (* Store Properties *)

  Lemma wf_value_encode_len_h : forall sz pf lo i,
    Z.of_nat
    (length
      (bytes_of_int (size_ftyp_nat lo (Ftyp_int sz pf))
        (@Word.unsigned sz i))) = Z.of_nat sz / 8 + 1.
  Proof.
    intros.
    rewrite length_bytes_of_int.
    unfold size_ftyp_nat. unfold size_ftyp. 
    rewrite nat_of_Z_eq; auto. 
    assert (0 <= Z.of_nat sz / 8). apply Z_div_pos; omega. omega.
  Qed.

  Lemma wf_value_encode_len : forall t v tenv live HT fs lo,
    wf_value' fs lo tenv live HT v t ->
    Z.of_nat (length (encode_rttag lo v)) = size_ftyp lo t.
  Proof.
    intros. unfold encode_rttag. unfold encode_int.
    inv H; destruct (endian lo); simpl in *; try reflexivity.
    rewrite rev_length.
    apply wf_value_encode_len_h. apply wf_value_encode_len_h.
  Qed.

  Lemma wf_value_encode_len_nat : forall t v tenv live HT fs lo,
    wf_value' fs lo tenv live HT v t ->
    length (encode_rttag lo v) = size_ftyp_nat lo t.
  Proof.
    intros. unfold encode_rttag. unfold encode_int. 
    inv H; destruct (endian lo); simpl in *; crush.
    rewrite rev_length. rewrite length_bytes_of_int. auto.
    rewrite length_bytes_of_int. auto.
  Qed.

  Lemma load_store_valid : forall m1 n t v v' lo tenv fs HT live,
    wf_value' fs lo tenv HT live v' t ->
    load m1 lo n t = Some v ->
    exists m2, store m1 lo n t v' = Some m2.
  Proof.
    unfold load; unfold store; intros. destruct (zle n 0); crush.
    apply wf_value_encode_len in H. rewrite <- H in *.
    destruct zle; crush. eauto.
  Qed.

  Lemma load_store_other : forall m1 m2 n t v n' t' fs lo tenv HT live,
    wf_value' fs lo tenv HT live v t ->
    store m1 lo n t v = Some m2 ->
    n' + size_ftyp lo t' <= n
    \/ n + size_ftyp lo t <= n' ->
    load m2 lo n' t' = load m1 lo n' t'.
  Proof.
    unfold store; intros. unfold load. destruct (zle n 0); try congruence.
    destruct (zle (n + Z.of_nat (length (encode_rttag lo v))) (Z.of_nat (h_addr m1))); try congruence.
    inv H0. destruct (zle n' 0); try congruence. simpl in *.
    erewrite getN_setN_outside; eauto.
    unfold size_ftyp_nat.
    apply wf_value_encode_len in H; auto. 
    unfold mem_cell. rewrite H.  
    rewrite nat_of_Z_eq. omega. 
    apply size_ftyp_nonneg.
  Qed.

  Lemma load_store_same : forall m1 m2 n t v fs lo tenv HT live,
    wf_value' fs lo tenv HT live v t ->
    store m1 lo n t v = Some m2 ->
    load m2 lo n t = Some v.
  Proof.
    unfold store; unfold load; intros. destruct zle; try congruence.
    t_dup H. apply wf_value_encode_len_nat in H. rewrite <- H in *.
    destruct zle; try congruence. inv H0. simpl in *.
    destruct zle; try omega. f_equal. rewrite getN_setN_same.
    eapply decode_encode_same; eauto. 
    rewrite H in l. unfold size_ftyp_nat in l. 
    rewrite nat_of_Z_eq in l. crush. apply size_ftyp_nonneg.
  Qed.
    
  Lemma load_store_valid_sub : forall m1 n t1 t2 v v' lo tenv fs HT live rmap,
    ftyp_sub t1 t2 = true ->
    wf_value' fs lo tenv HT live v' (sigma' rmap t1) ->
    load m1 lo n (sigma' rmap t2) = Some v ->
      exists m2, store m1 lo n (sigma' rmap t2) v' = Some m2.
  Proof.
    unfold load; unfold store; intros. destruct_c (zle n 0).
    unfold size_ftyp_nat in H1. apply ftyp_sub_sigma with (rmap := rmap) in H.
    erewrite <- size_ftyp_sub_same in H1; eauto.
    erewrite <- wf_value_encode_len in H1; eauto.
    destruct_c zle. inv H1. eauto. 
  Qed.
  
  Lemma load_store_same_sub : forall m1 m2 n t1 t2 v fs lo tenv HT live rmap,
    ftyp_sub t1 t2 = true ->
    wf_value' fs lo tenv HT live v (sigma' rmap t1) ->
    store m1 lo n (sigma' rmap t2) v = Some m2 ->
    load m2 lo n (sigma' rmap t2) = Some v.
  Proof.
    unfold store; unfold load; intros. destruct zle; try congruence.
    t_dup H. t_dup H0. apply wf_value_encode_len_nat in H0. 
    destruct zle; try congruence. inv H1. simpl in *.
    destruct zle; try omega. f_equal. unfold size_ftyp_nat in H0.
    unfold size_ftyp_nat. rewrite size_ftyp_sigma_inv with (rmap := rmap).
    assert (nat_of_Z (size_ftyp lo t2) = size_ftyp_nat lo t2).
    unfold size_ftyp_nat. reflexivity. 
    rewrite size_ftyp_sigma_inv in H0. erewrite <- size_ftyp_sub_same; eauto.
    rewrite <- H0. rewrite getN_setN_same. eapply decode_encode_same; eauto.
    eapply wf_val_ftyp_sub2; eauto.

    rewrite H0 in l. unfold size_ftyp_nat in l. rewrite size_ftyp_sigma_inv in l. 
    rewrite nat_of_Z_eq in l. rewrite size_ftyp_sigma_inv in g0. 
    erewrite <- size_ftyp_sub_same in g0; eauto. crush. apply size_ftyp_nonneg.
  Qed.

  Lemma store_null_fail : forall m tenv t v,
    store m tenv 0 t v = None.
  Proof.
    unfold store; intros. destruct zle; crush.
  Qed.

  (* ---------------------------------------------------------------------- *)
  (* Alloc Properties *)
  Lemma alloc_typ : forall m t m' n r fs lo tenv HT live rmap s,
    wf_tenv tenv ->
    TS tenv t ->
    alloc m lo live HT (sigma rmap (flatten_typ lo tenv t)) s (alpha rmap r) = Some (n,m') ->
    wf_value' fs lo tenv live HT 
      (RT_ptr n) 
      (Ftyp_ptr (sigma'' rmap t) (alpha rmap r)).
  Proof.
    unfold alloc; intros.
    remember (sigma rmap (flatten_typ lo tenv t)) as Hd.
    symmetry in HeqHd. destruct Hd; crush.
    destruct in_dec; try congruence.
    remember (check_HT lo HT (Z.of_nat (h_addr m)) (alpha rmap r) (f :: Hd)) as Hd2.
    symmetry in HeqHd2. destruct Hd2; crush.
    econstructor; eauto. 
    destruct zeq; crush.
    rewrite <- flatten_sigma_comm; eauto. 
    rewrite <- HeqHd in HeqHd2.
    assert (Word.unsigned (@Word.repr WORDSIZE_BITS (Z.of_nat (h_addr m))) = Z.of_nat (h_addr m)).
    rewrite Word.unsigned_repr; auto. destruct m; crush.
    unfold WORDSIZE_BITS in H1. unfold WORDSIZE_BITS. rewrite H1. crush.
  Qed.

  Lemma load_alloc_same : forall m lo live HT t m' n n' t' v r s,
    alloc m lo live HT t s r = Some (n, m') ->
    load m lo n' t' = Some v ->
    load m' lo n' t' = Some v.
  Proof.
    unfold load; intros. destruct zle; try congruence.
    unfold alloc in H. destruct t; try congruence. 
    destruct in_dec; try congruence.
    destruct (check_HT lo HT (Z.of_nat (h_addr m)) r (f :: t)); crush.
  Qed.

  Lemma alloc_typU : forall m m' n r fs lo tenv HT live rmap s sz,
    alloc m lo live HT (list_repeat sz Ftyp_int8) s (alpha rmap r) = Some (n,m') ->
    wf_value' fs lo tenv live HT
      (RT_ptr n)
      (Ftyp_ptrU sz (alpha rmap r)).
  Proof.
    unfold alloc; intros.
    remember (list_repeat sz Ftyp_int8) as Hd.
    symmetry in HeqHd. destruct_c Hd. destruct_c in_dec.
    remember (check_HT lo HT (Z.of_nat (h_addr m)) (alpha rmap r) (f :: Hd)) as Hd2.
    symmetry in HeqHd2. destruct_c Hd2. inv H.
    econstructor; eauto. destruct_c zeq; auto.
    rewrite <- HeqHd in HeqHd2. 
    assert (Word.unsigned (@Word.repr WORDSIZE_BITS (Z.of_nat (h_addr m))) = Z.of_nat (h_addr m)).
    rewrite Word.unsigned_repr; auto. destruct m; crush.
    unfold WORDSIZE_BITS in H. unfold WORDSIZE_BITS. rewrite H. crush.
  Qed.

  (* ---------------------------------------------------------------------- *)
  (* Free Properties *)
  Lemma load_free_valid : forall m lo n t v,
    load m lo n t = Some v ->
    exists m', free m lo n = Some m'.
  Proof.
    unfold free; crush; eauto.
  Qed.

  Lemma load_free_same : forall m lo n m' t v,
    free m lo n = Some m' ->
    load m lo n t = Some v ->
    load m' lo n t = Some v.
  Proof.
    unfold free; crush.
  Qed.

  (* ---------------------------------------------------------------------- *)
  (** * Crazy Memory Operations *)
  (* ---------------------------------------------------------------------- *)

  (* ---------------------------------------------------------------------- *)
  Definition next (HT:heap_t) : option Z :=
    Some (max_HT HT + ftyp_max).

  (* ---------------------------------------------------------------------- *)
  (* construct_HT properties *)

  Lemma construct_HT_ext : forall t HT tenv n r,
    (forall n' t', Zenv.find n' HT = Some t' -> n' < n) ->
    heapt_ext HT (construct_HT tenv HT n r t).
  Proof.
    induction t; simpl; intros; try congruence. unfold heapt_ext in *; intros. 
    simpl in *.
    destruct (OrderedTypeEx.Z_as_OT.eq_dec n0 n); subst.
    apply H in H0. crush.
    eapply IHt; eauto. intros. apply H in H1; auto. 
    assert (size_ftyp tenv a >= 0). apply size_ftyp_nonneg. omega.
  Qed.

  Lemma construct_HT_ext2 : forall t HT tenv n r live,
    ~ In r live ->
    heapt_ext2 live HT (construct_HT tenv HT n r t).
  Proof.
    induction t; simpl; intros; try congruence. 
    unfold heapt_ext2 in *; simpl in *; intros.
    destruct (OrderedTypeEx.Z_as_OT.eq_dec n0 n); try congruence.
    eapply IHt in H1; eauto.
  Qed.

  Lemma construct_HT_spec : forall t n' n tenv t' HT r r',
    Zenv.find n' (construct_HT tenv HT n r t) = Some (t',r') ->
    Zenv.find n' HT = Some (t',r') \/ (n' >= n /\ r = r').
  Proof.
    induction t; simpl; intros; auto.
    destruct (OrderedTypeEx.Z_as_OT.eq_dec n' n); subst. right. inv H. split; eauto. omega.
    eapply IHt in H; eauto. destruct H; auto.
    right. assert (size_ftyp tenv a >= 0). apply size_ftyp_nonneg.
    destruct H. split; eauto. omega.
  Qed.

  Lemma construct_HT_wf_HT' : forall t HT lo n a r,
    wf_HT lo HT ->
    wf_HT lo (construct_HT lo HT (n + size_ftyp lo a) r t) ->
    (forall n' t', Zenv.find n' HT = Some t' -> n' + ftyp_max <= n) ->
    0 < n ->
    n + size_ftyp lo a < Word.modulus WORDSIZE_BITS ->
    wf_HT lo (Zenv.add n (a,r) (construct_HT lo HT (n + size_ftyp lo a) r t)).
  Proof.
    unfold wf_HT; intros. split; intros. simpl in H4.
    destruct (OrderedTypeEx.Z_as_OT.eq_dec n0 n); subst. inv H4.
    simpl in H6. destruct (OrderedTypeEx.Z_as_OT.eq_dec n' n); subst. crush.
    
    eapply construct_HT_spec in H6. destruct H6. apply H1 in H4. left.
    assert (size_ftyp lo t' < ftyp_max). apply size_ftyp_max. omega.
    right. omega. 
    
    simpl in H6. destruct (OrderedTypeEx.Z_as_OT.eq_dec n' n); subst. inv H6.
    eapply construct_HT_spec in H4; eauto. destruct H4. apply H1 in H4. right.
    assert (size_ftyp lo t0 < ftyp_max). apply size_ftyp_max. omega. omega.
    eapply H0 in H6. destruct H6. eapply H6 in H4; eauto. destruct H4; eauto.

    simpl in H4. destruct (OrderedTypeEx.Z_as_OT.eq_dec n0 n); subst. inv H4.
    omega. eapply H0; eauto.
  Qed.

  Lemma construct_HT_wf_HT : forall t HT lo n r,
    wf_HT lo HT ->
    (forall n' t', Zenv.find n' HT = Some t' -> n' + ftyp_max <= n) ->
    0 < n -> 
    n + size_ftyps lo t < Word.modulus WORDSIZE_BITS ->
    wf_HT lo (construct_HT lo HT n r t).
  Proof.
    induction t; crush. eapply construct_HT_wf_HT'; eauto. eapply IHt; eauto.
    intros. apply H0 in H3.
    assert (size_ftyp lo a >= 0). apply size_ftyp_nonneg. omega. 
    assert (size_ftyp lo a >= 0). apply size_ftyp_nonneg. omega. omega.
    assert (size_ftyp lo a >= 0). apply size_ftyp_nonneg. 
    assert (size_ftyps lo t >= 0). apply size_ftyps_nonneg. omega.
  Qed.

  Lemma construct_HT_typ_spec2 : forall t lo HT n t' n' r' live rgns,
    wf_tenv_ftyps (rgns ++ live) t ->
    n' >= n ->
    wf_HT_live (rgns++live) HT ->
    Zenv.find n' (construct_HT lo HT n r' t) = Some (t', r') ->
    wf_tenv_ftyp (rgns ++ live) t'.
  Proof.
    induction t; crush. unfold wf_HT_live in H1. apply H1 in H2; auto.
    inv H. 
    destruct OrderedTypeEx.Z_as_OT.eq_dec; crush. t_dup H2.
    eapply construct_HT_spec in H2. destruct H2.
    unfold wf_HT_live in H1. apply H1 in H. auto.
    eapply IHt in H'; eauto. crush.
  Qed.

  Lemma construct_HT_wf_HT_live' : forall t HT n a r live lo rgns,
    wf_tenv_ftyps (rgns ++ live) (a :: t) ->
    wf_HT_live (rgns++live) HT ->
    (forall n' t', Zenv.find n' HT = Some t' -> n' + ftyp_max <= n) ->
    wf_HT_live (rgns ++ live) (Zenv.add n (a, r) (construct_HT lo HT (n + size_ftyp lo a) r t)).
  Proof.
    unfold wf_HT_live; simpl; intros.
    destruct (OrderedTypeEx.Z_as_OT.eq_dec); subst. inv H2. inv H; auto.
    t_dup H2.
    eapply construct_HT_spec in H2. destruct H2.
    apply H0 in H2. auto. 
    destruct H2. subst. eapply construct_HT_typ_spec2 in H'; eauto. 
    inv H; auto.
  Qed.

  Lemma construct_HT_wf_HT_live : forall t HT lo n r rgns live,
    wf_tenv_ftyps (rgns ++ live) t ->
    wf_HT_live (rgns++live) HT ->
    (forall n' t', Zenv.find n' HT = Some t' -> n' + ftyp_max <= n) ->
    wf_HT_live (rgns++live) (construct_HT lo HT n r t).
  Proof.
    induction t; crush. unfold wf_HT_live in *; intros. 
    eapply construct_HT_wf_HT_live'; eauto.
  Qed.

  (* ---------------------------------------------------------------------- *)
  (* fresh region generation *)

  Fixpoint fresh (n:rgn) (live:list rgn) : option rgn :=
    match n with
      | O => None
      | S n' => if in_dec rgn_dec n live then fresh n' live else Some n
    end.

  Fixpoint freshn (n:rgn) (live:list rgn) (lrgns:list (rgn*typ)) : option (list (rgn*rgn)*list rgn*list rgn) :=
    match lrgns with
      | nil => Some (nil, live, nil)
      | (r,t)::lrgns' => 
        match freshn n live lrgns' with
          | Some (rmap,live',rgns) => 
            match fresh n live' with
              | Some r' => Some ((r,r')::rmap, r'::live', r'::rgns)
              | None => None
            end
          | None => None
        end
    end.

  Lemma freshn_prop1 : forall lrgns n live rmap rgns live',
    freshn n live lrgns = Some (rmap, live', rgns) ->
    domain lrgns = domain rmap.
  Proof.
    induction lrgns; simpl; intros. inv H. simpl. reflexivity.
    destruct a; auto. 
    remember (freshn n live lrgns) as Hd. destruct Hd; try congruence.
    destruct p; subst. destruct p; subst.
    destruct (fresh n l1); try congruence. inv H. simpl. f_equal; eauto.
  Qed.
  
  Lemma freshn_prop2 : forall lrgns n live rmap rgns live',
    freshn n live lrgns = Some (rmap, live', rgns) ->
    rgns = range rmap /\ live' = rgns ++ live.
  Proof.
    induction lrgns; simpl; intros. inv H. simpl. split; reflexivity.
    destruct a; auto.
    remember (freshn n live lrgns) as Hd. destruct Hd; try congruence.
    destruct p; subst. destruct p; subst. 
    destruct (fresh n l1); try congruence. inv H. simpl.
    symmetry in HeqHd. apply IHlrgns in HeqHd. destruct HeqHd. subst.
    split; f_equal; eauto.
  Qed.

  Lemma fresh_prop : forall n live r,
    fresh n live = Some r ->
    ~ In r live.
  Proof.
    induction n; crush. destruct in_dec; crush. eauto.
  Qed.
  
  Lemma freshn_prop3 : forall lrgns n live rmap rgns live',
    freshn n live lrgns = Some (rmap, live', rgns) ->
    list_disjoint (range rmap) live.
  Proof.
    induction lrgns; simpl; intros. inv H. simpl. unfold list_disjoint; crush. 
    destruct a; auto.
    remember (freshn n live lrgns) as Hd. destruct Hd; try congruence.
    destruct p; subst. destruct p; subst.
    remember (fresh n l1) as Hd2. destruct Hd2; try congruence. inv H.
    symmetry in HeqHd. assert (H3 := HeqHd). eapply IHlrgns in HeqHd.
    eapply freshn_prop2 in H3. destruct H3. subst.
    symmetry in HeqHd2. apply fresh_prop in HeqHd2.
    unfold list_disjoint in *; crush; eauto.
  Qed.
  
  Lemma freshn_prop4 : forall lrgns n live rmap rgns live',
    freshn n live lrgns = Some (rmap, live', rgns) ->
    list_norepet (range rmap).
  Proof.
    induction lrgns; simpl; intros. inv H. simpl. constructor.
    destruct a; auto.
    remember (freshn n live lrgns) as Hd. destruct Hd; try congruence.
    destruct p; subst. destruct p; subst.
    remember (fresh n l1) as Hd2. destruct Hd2; try congruence.
    symmetry in HeqHd. assert (H3 := HeqHd). eapply IHlrgns in HeqHd.
    eapply freshn_prop2 in H3. destruct H3. inv H.
    constructor; auto. symmetry in HeqHd2. apply fresh_prop in HeqHd2.
    crush; eauto.
  Qed.
  
  Lemma freshn_prop : forall lrgns n live rmap rgns live',
    freshn n live lrgns = Some (rmap, live', rgns) ->
    domain lrgns = domain rmap /\
    rgns = range rmap /\
    live' = rgns ++ live /\
    list_disjoint (range rmap) live /\
    list_norepet (range rmap).
  Proof.
    intros. assert (H1 := H). assert (H2 := H). assert (H3 := H).
    apply freshn_prop1 in H.
    apply freshn_prop2 in H1.
    apply freshn_prop3 in H2.
    apply freshn_prop4 in H3.
    crush.
  Qed.

  (* ---------------------------------------------------------------------- *)
  (* new_regions' *)

  Program Definition new_regions' (m:cmem) (lo:layout) (r:rgn) (HT:heap_t) (t:ftyps) : option (cmem*heap_t) :=
    match next HT with
      | Some p =>
        if zle p 0 then None else
          if zle (Z.of_nat (h_addr m)) p then
            let HT' := construct_HT lo HT p r t in
              if zlt (p + size_ftyps lo t + ftyp_max) (Word.max_unsigned WORDSIZE_BITS) then
                if zlt (max_HT HT' + ftyp_max) (Word.max_unsigned WORDSIZE_BITS) then
                  Some (mk_mem (mem m) (s_fresh m) (nat_of_Z (p + size_ftyps lo t + ftyp_max)) _ _, HT')
                  else None
              else None
            else
              None
      | None => None
    end.
  Next Obligation.
    assert (size_ftyps lo t >= 0). apply size_ftyps_nonneg.
    rewrite nat_of_Z_eq; try omega. 
    unfold ftyp_max in *. omega.
  Qed.
  Next Obligation.
    destruct m; simpl in *. 
    assert (size_ftyps lo t >= 0). apply size_ftyps_nonneg.
    rewrite nat_of_Z_eq in H3; try omega.
    assert (p0 >= Z.of_nat h_addr0). unfold ftyp_max in *. omega. eauto.
    unfold ftyp_max in *; omega.
  Qed.

  Lemma new_regions_heapt_ext' : forall m lo HT t m' HT' r',
    new_regions' m lo r' HT t = Some (m', HT') ->
    heapt_ext HT HT'.
  Proof.
    unfold new_regions'; simpl; intros.
    destruct zle; try congruence. 
    destruct zle; try congruence.
    destruct zlt; try congruence.
    destruct zlt; try congruence.
    inv H.
    eapply construct_HT_ext; eauto; intros. eapply max_HT_spec in H. unfold ftyp_max in *. omega.
  Qed.
  
  Lemma new_regions_heapt_ext2' : forall t HT r live HT' lo m m',
    ~ In r live ->
    new_regions' m lo r HT t = Some (m', HT') ->
    heapt_ext2 live HT HT'.
  Proof.
    unfold new_regions'; simpl; intros.
    destruct zle; try congruence.
    destruct zle; try congruence.
    destruct zlt; try congruence.
    destruct zlt; try congruence.
    inv H0.
    eapply construct_HT_ext2; eauto; intros.
  Qed.

  Lemma new_regions_wf_HT' : forall m lo HT t m' HT' r',
    wf_HT lo HT ->
    new_regions' m lo r' HT t = Some (m', HT') ->
    wf_HT lo HT'.
  Proof.
    unfold new_regions'; intros. simpl in *.
    destruct zle; try congruence. destruct zle; try congruence. 
    destruct zlt; try congruence. destruct zlt; try congruence. inv H0.
    remember (construct_HT lo HT (max_HT HT + ftyp_max) r' t) as HT'. rewrite HeqHT'.
    eapply construct_HT_wf_HT; eauto; intros. eapply max_HT_spec in H0. omega. 
    omega. assert (size_ftyps lo t >= 0). apply size_ftyps_nonneg. 
    unfold Word.max_unsigned in l0. unfold ftyp_max in *. omega.
  Qed.
  
  Lemma max_HT_larger : forall t lo HT r' n,
    n >= 0 ->
    max_HT HT <= max_HT (construct_HT lo HT (max_HT HT + n) r' t).
  Proof.
    induction t; simpl; intros. omega.
    destruct zlt. omega. 
    assert (max_HT HT + n + size_ftyp lo a = max_HT HT + (n + size_ftyp lo a)). omega.
    rewrite H0.
    eapply IHt with (n := n + size_ftyp lo a).
    assert (size_ftyp lo a >= 0). apply size_ftyp_nonneg. omega.
  Qed.

  Lemma new_regions_wf_HT_bounds' : forall m lo HT m' HT' t r',
    wf_HT_bounds HT ->
    new_regions' m lo r' HT t = Some (m', HT') ->
    wf_HT_bounds HT' /\
    max_HT HT <= max_HT HT'.
  Proof.
    unfold new_regions'; simpl; intros.
    destruct zle; try congruence. destruct zle; try congruence. 
    destruct zlt; try congruence. inv H0. destruct zlt; try congruence. inv H2.
    split.
    unfold wf_HT_bounds in *; intros. split. omega.
    assert (max_HT HT <= max_HT (construct_HT lo HT (max_HT HT + ftyp_max) r' t)). apply max_HT_larger. unfold ftyp_max. omega.
    omega.
    apply max_HT_larger. unfold ftyp_max. omega.
  Qed.
  
  Lemma new_regions_wf_HT_live' : forall m lo HT t m' HT' r' rgns live,
    wf_tenv_ftyps (rgns ++ live) t ->
    wf_HT_live (rgns++live) HT ->
    new_regions' m lo r' HT t = Some (m', HT') ->
    wf_HT_live (rgns ++ live) HT'.
  Proof.
    unfold new_regions'; simpl; intros.
    destruct zle; try congruence. 
    destruct zle; try congruence.
    destruct zlt; try congruence. 
    destruct zlt; try congruence. 
    inv H1.
    eapply construct_HT_wf_HT_live; eauto; intros.
    eapply max_HT_spec in H1; eauto. omega.
  Qed.

  Lemma new_regions_prop' : forall m lo HT t m' HT' r',
    wf_HT lo HT ->
    new_regions' m lo r' HT t = Some (m', HT') ->
    heapt_ext HT HT' /\
    wf_HT lo HT'.
  Proof.
    intros. split. eapply new_regions_heapt_ext'; eauto. eapply new_regions_wf_HT'; eauto.
  Qed.

  (* ---------------------------------------------------------------------- *)

  (* Allocate a list of new regions and produce the appropriate memory and HT *)
  Fixpoint new_regions4 (m:cmem) (lo:layout) (tenv:tenv_t) (rmap:Nenv.t rgn) (live rgns:list rgn) (HT:heap_t) (lrgn:list (rgn * typ)) : option (cmem * heap_t) :=
    match rgns, lrgn with
      | nil, nil => 
        if zle (max_HT HT + ftyp_max) 0 then None else
          if zle (Word.max_unsigned WORDSIZE_BITS) (max_HT HT +ftyp_max) then None else
            if zle (Z.of_nat (h_addr m)) (max_HT HT + ftyp_max) then None
              else Some (m, HT)
      | r::rgns', (r',t)::lrgn' => 
        match new_regions4 m lo tenv rmap live rgns' HT lrgn' with
          | Some (m', HT') => new_regions' m' lo r HT' (sigma rmap (flatten_typ lo tenv t))
          | None => None
        end
      | _, _ => None
    end.

  (* ughh ... same as new_regions4 except it has a weaker inductive step *)
  Fixpoint new_regions3 (m:cmem) (lo:layout) (tenv:tenv_t) (rmap:Nenv.t rgn) (live rgns1 rgns2:list rgn) (HT:heap_t) (lrgn:list (rgn * typ)) : option (cmem * heap_t) :=
    match rgns2, lrgn with
      | nil, nil => Some (m, HT)
      | r::rgns', (r',t)::lrgn' => 
        match new_regions3 m lo tenv rmap live rgns1 rgns' HT lrgn' with
          | Some (m', HT') => new_regions' m' lo r HT' (sigma rmap (flatten_typ lo tenv t))
          | None => None
        end
      | _, _ => None
    end.

  Lemma new_regions_heapt_ext : forall rgns m lo HT rmap m' HT' live tenv lrgn,
    new_regions4 m lo tenv rmap live rgns HT lrgn = Some (m', HT') ->
    heapt_ext HT HT'.
  Proof.
    induction rgns; destruct lrgn; crush.
    destruct zle; try congruence. destruct zle; try congruence. destruct zle; try congruence.
    destruct p; auto.
    remember (new_regions4 m lo tenv rmap live rgns HT lrgn) as Hd.
    symmetry in HeqHd. destruct Hd; try congruence. destruct p; auto.
    apply IHrgns in HeqHd; auto.
    eapply new_regions_heapt_ext' in H; eauto.
    unfold heapt_ext in *; crush.
  Qed.

  Lemma new_regions_heapt_ext2 : forall rgns m lo HT rmap m' HT' live tenv lrgn,
    list_norepet rgns ->
    list_disjoint rgns live ->
    new_regions4 m lo tenv rmap live rgns HT lrgn = Some (m', HT') ->
    heapt_ext2 live HT HT'.
  Proof.
    induction rgns; destruct lrgn; crush.
    destruct zle; try congruence. destruct zle; try congruence. destruct zle; try congruence.
    destruct p; auto.
    remember (new_regions4 m lo tenv rmap live rgns HT lrgn) as Hd.
    symmetry in HeqHd. destruct Hd; try congruence. destruct p; auto.
    inv H. eapply IHrgns in HeqHd; eauto.
    assert (~ In a live). unfold list_disjoint in H0. unfold not. intros.
    specialize (H0 a a). crush.
    eapply new_regions_heapt_ext2' in H1; eauto.
    unfold heapt_ext2; crush.
    unfold list_disjoint in *; intros.
    specialize (H0 y y). crush.
  Qed.

  Lemma new_regions_wf_HT_bounds2 : forall rgns m lo HT rmap m' HT' live tenv lrgn,
    wf_HT_bounds HT ->
    new_regions4 m lo tenv rmap live rgns HT lrgn = Some (m', HT') ->
    wf_HT_bounds HT' /\
    max_HT HT <= max_HT HT'.
  Proof.
    induction rgns; destruct lrgn; simpl; intros.
    destruct zle; try congruence. destruct zle; try congruence. destruct zle; try congruence. inv H0. crush.
    inv H0. inv H0.
    destruct p; auto.
    remember (new_regions4 m lo tenv rmap live rgns HT lrgn) as Hd.
    symmetry in HeqHd. destruct Hd; try congruence. destruct p; auto.
    inv H0. eapply IHrgns in HeqHd; eauto. destruct HeqHd.
    eapply new_regions_wf_HT_bounds' in H2; eauto. crush.
  Qed.

  Lemma new_regions_wf_HT2 : forall rgns m lo HT rmap m' HT' live tenv lrgn,
    wf_HT lo HT ->
    new_regions4 m lo tenv rmap live rgns HT lrgn = Some (m', HT') ->
    wf_HT lo HT'.
  Proof.
    induction rgns; destruct lrgn; crush.
    destruct zle; try congruence. destruct zle; try congruence. destruct zle; try congruence. crush.
    destruct p; auto.
    remember (new_regions4 m lo tenv rmap live rgns HT lrgn) as Hd.
    symmetry in HeqHd. destruct Hd; try congruence. destruct p; auto.
    apply IHrgns in HeqHd; auto.
    eapply new_regions_wf_HT'; eauto.
  Qed.
  
  Definition list_subset {A:Type} (ls1 ls2: list A) :=
    forall x, In x ls1 -> In x ls2.

  Lemma new_regions_wf_HT_live_weak : forall lrgn rgns1 rgns2 m lo HT rmap m' HT' live tenv,
    list_subset rgns2 rgns1 ->
    Forall (fun t => wf_tenv_ftyps (rgns1++live) (sigma rmap (flatten_typ lo tenv t))) (range lrgn) ->
    wf_HT_live live HT ->
    new_regions3 m lo tenv rmap live rgns1 rgns2 HT lrgn = Some (m', HT') ->
    wf_HT_live (rgns1++live) HT'.
  Proof.
    induction lrgn; destruct rgns2; crush. unfold wf_HT_live in *; intros. apply H1 in H2.
    apply wf_tenv_ftyp_live_ext; auto.
    remember (new_regions3 m lo tenv rmap live rgns1 rgns2 HT lrgn) as Hd.
    symmetry in HeqHd. destruct Hd; try congruence. destruct p; auto.
    inv H0. apply IHlrgn in HeqHd; eauto.   

    eapply new_regions_wf_HT_live' in H2; eauto.
    unfold list_subset in *; crush.
  Qed.

  Lemma new_regions_4_3_same : forall lrgn rgns1 rgns2 m lo HT rmap m' HT' live tenv,
    list_subset rgns2 rgns1 ->
    new_regions4 m lo tenv rmap live rgns2 HT lrgn = Some (m', HT') ->
    new_regions3 m lo tenv rmap live rgns1 rgns2 HT lrgn = Some (m', HT').
  Proof.
    induction lrgn; destruct rgns2; crush.
    destruct zle; try congruence. destruct zle; try congruence. destruct zle; try congruence.
    remember (new_regions4 m lo tenv rmap live rgns2 HT lrgn) as Hd.
    symmetry in HeqHd. destruct Hd; try congruence. destruct p; auto.
    eapply IHlrgn with (rgns1 := rgns1) in HeqHd; eauto.
    rewrite HeqHd. crush.
    unfold list_subset in *; crush.
  Qed.

  Lemma new_regions_wf_HT_liveh : forall lrgn rgns m lo HT rmap m' HT' live tenv,
    Forall (fun t => wf_tenv_ftyps (rgns++live) (sigma rmap (flatten_typ lo tenv t))) (range lrgn) ->
    wf_HT_live live HT ->
    new_regions4 m lo tenv rmap live rgns HT lrgn = Some (m', HT') ->
    wf_HT_live (rgns++live) HT'.
  Proof.
    intros. 
    assert (list_subset rgns rgns). crush.
    eapply new_regions_4_3_same in H1; eauto.
    eapply new_regions_wf_HT_live_weak in H1; eauto.
  Qed.

  (* ---------------------------------------------------------------------- *)
  (* New Region Properties *)

  Definition wf_mem (fs:functions) (lo:layout) (tenv:tenv_t) (live:list rgn) (HT:heap_t) (m:cmem) : Prop :=
    forall n t r,
      Zenv.find n HT = Some (t,r) ->
      exists v, load m lo n t = Some v /\ wf_value' fs lo tenv live HT v t.
  
  Lemma getN_zero : forall size n mem0 addr,
    n >= addr ->
    (forall p, p >= addr -> mem0 p = Word.zero) ->
    getN n size mem0 = list_repeat size Word.zero.
  Proof.
    induction size; crush. f_equal. eapply IHsize; eauto. omega.
  Qed.

  Lemma construct_HT_typ_spec : forall t lo HT rmap n t' n' r r',
    n' >= ftyp_max ->
    n > max_HT HT ->
    Zenv.find n (construct_HT lo HT (max_HT HT + n') r (sigma rmap t)) = Some (t',r') ->
    exists t'', t' = sigma' rmap t''.
  Proof.
    induction t; crush.
    apply max_HT_spec in H1. crush.
    destruct (OrderedTypeEx.Z_as_OT.eq_dec n (max_HT HT + n')); crush.
    eauto.
    assert (max_HT HT + n' + size_ftyp lo (sigma' rmap a) = 
      max_HT HT + (n' + size_ftyp lo (sigma' rmap a))). omega.
    rewrite H2 in H1. eapply IHt in H1; eauto.
    assert (size_ftyp lo (sigma' rmap a) >= 0). apply size_ftyp_nonneg.
    omega. 
  Qed.

  Lemma construct_HT_max_spec : forall t t' n n' tenv HT r r',
    n >= ftyp_max ->
    Zenv.find n' (construct_HT tenv HT (max_HT HT + n) r t) = Some (t',r') ->
    (n' + size_ftyp tenv t' <= ((max_HT HT) + n) + size_ftyps tenv t).
  Proof.
    induction t; crush.
    apply max_HT_spec in H0; auto. 
    assert (size_ftyp tenv t' < ftyp_max). apply size_ftyp_max. omega.
    
    destruct (OrderedTypeEx.Z_as_OT.eq_dec n' (max_HT HT + n)). inv H0. 
    assert (size_ftyps tenv t >= 0). apply size_ftyps_nonneg. crush.
    assert (max_HT HT + n + size_ftyp tenv a = 
      max_HT HT + (n + size_ftyp tenv a)). omega.
    rewrite H1 in H0.
    eapply IHt in H0; eauto. omega. 
    assert (size_ftyp tenv a >= 0). apply size_ftyp_nonneg. omega.
  Qed.

  Lemma wf_val_zero : forall fs lo tenv t live HT rmap,
    wf_value' fs lo tenv live HT
    (decode_rttag lo (sigma' rmap t)
      (list_repeat (size_ftyp_nat lo (sigma' rmap t))
        Word.zero)) (sigma' rmap t).
  Proof.
    intros. destruct t; simpl. econstructor. econstructor. 
    destruct (endian lo); simpl. econstructor; eauto. simpl. auto.
    econstructor; eauto. simpl. auto.
    destruct (endian lo); simpl. econstructor; eauto. destruct_c zeq; auto.
    crush. econstructor; eauto. destruct_c zeq; auto. crush.
    destruct (endian lo); simpl. econstructor; eauto.
    unfold check_fun.
    destruct lab_dec; crush.
    econstructor; eauto. unfold check_fun. destruct lab_dec; crush.
    destruct (endian lo); simpl. econstructor; simpl; eauto. 
    econstructor; simpl; eauto.
  Qed.

  Lemma new_regions_wf_mem' : forall m fs lo tenv t HT rmap m' HT' r' live,
    wf_HT lo HT ->
    wf_tenv tenv ->
    new_regions' m lo r' HT (sigma rmap t) = Some (m', HT') ->
    wf_mem fs lo tenv live HT m ->
    wf_mem fs lo tenv (r'::live) HT' m'.
  Proof.
    unfold wf_mem; intros. t_dup H1. apply new_regions_prop' in H1; auto. destruct H1.
    unfold new_regions' in H'. unfold next in H'. 
    destruct zle; try congruence. destruct zle; try congruence. 
    destruct zlt; try congruence. destruct zlt; try congruence. inv H'.
    
    unfold load in *; simpl in *.
    
    destruct (zlt n (max_HT HT + ftyp_max)).
    assert (Zenv.find n HT = Some (t0,r)). 
    apply construct_HT_spec in H3. destruct H3; crush.
    apply H2 in H5. t_simp. exists x. split; auto. 
    destruct zle; try congruence.
    destruct zle; try congruence.
    destruct zle; try congruence.
    
    assert (max_HT HT + ftyp_max >= 0). omega.
    assert (size_ftyps lo (sigma rmap t) >= 0). apply size_ftyps_nonneg.
    unfold ftyp_max in *. rewrite nat_of_Z_eq in g1; try omega.

    eapply wf_val_HT_ext'; eauto. eapply wf_val_live_ext2; eauto.
    
    destruct zle; try congruence. omegaContradiction.


    destruct zle; try congruence.
    
    destruct m; simpl in *. 
    assert (n >= Z.of_nat h_addr0). omega.
    apply getN_zero with (size := size_ftyp_nat lo t0) (mem0 := mem0) in H5; auto.
    rewrite H5.
    exists (decode_rttag lo t0
        (list_repeat (size_ftyp_nat lo t0) Word.zero)).
    split; eauto.
    eapply construct_HT_typ_spec in H3; eauto; try omega. t_simp. subst. eapply wf_val_live_ext2; eauto.
    eapply wf_val_zero.

    assert (size_ftyps lo (sigma rmap t) >= 0). apply size_ftyps_nonneg.
    rewrite nat_of_Z_eq in l2; try omega. unfold ftyp_max in *; omega.
    unfold ftyp_max in *; omega.
    
    intros. eapply construct_HT_max_spec in H3; try omega. unfold ftyp_max in *.
    rewrite nat_of_Z_eq in g2. omega. omega.
  Qed.

  Lemma new_regions_wf_mem2 : forall rgns lrgn m tenv HT rmap m' HT' live lo fs,
    wf_HT lo HT ->
    wf_tenv tenv ->
    new_regions4 m lo tenv rmap live rgns HT lrgn = Some (m', HT') ->
    wf_mem fs lo tenv live HT m ->
    wf_mem fs lo tenv (rgns ++ live) HT' m' /\ wf_HT lo HT'.
  Proof.
    induction rgns; destruct lrgn; crush.
    destruct zle; try congruence. destruct zle; try congruence. destruct zle; try congruence. crush.
    destruct zle; try congruence. destruct zle; try congruence. destruct zle; try congruence. crush.
    remember (new_regions4 m lo tenv rmap live rgns HT lrgn) as Hd.
    symmetry in HeqHd. destruct Hd; crush. destruct p; auto.
    eapply IHrgns in HeqHd; eauto. destruct HeqHd. 
    eapply new_regions_wf_mem' in H1; eauto.
    remember (new_regions4 m lo tenv rmap live rgns HT lrgn) as Hd.
    symmetry in HeqHd. destruct Hd; crush. destruct p; auto.
    eapply IHrgns in HeqHd; eauto. destruct HeqHd. 
    eapply new_regions_wf_HT' in H1; eauto.
  Qed.

  Definition new_regions (m:cmem) (lo:layout) (tenv:tenv_t) (rmap:Nenv.t rgn) (live rgns:list rgn) (HT:heap_t) (lrgn:list (rgn*typ)) : option (cmem * heap_t) :=
    new_regions4 m lo tenv rmap live rgns HT lrgn.

  Lemma new_regions_prop : forall m lo live rgns HT lrgn m' HT' rmap tenv,
    list_norepet rgns ->
    list_disjoint rgns live ->
    new_regions m lo tenv rmap live rgns HT lrgn = Some (m', HT') ->
    heapt_ext HT HT' /\
    heapt_ext2 live HT HT'.
  Proof.
    unfold new_regions; intros. split. 
    eapply new_regions_heapt_ext; eauto.
    eapply new_regions_heapt_ext2; eauto.
  Qed.
    
  Lemma new_regions_wf_HT_live : forall lrgn m lo HT rmap m' HT' live rgns tenv,
    Forall (fun t => wf_tenv_ftyps (rgns++live) (sigma rmap (flatten_typ lo tenv t))) (range lrgn) ->
    wf_HT_live live HT ->
    new_regions m lo tenv rmap live rgns HT lrgn = Some (m', HT') ->
    wf_HT_live (rgns++live) HT'.
  Proof.
    unfold new_regions; intros. eapply new_regions_wf_HT_liveh; eauto.
  Qed.

  Lemma new_regions_wf_mem : forall m lo live rgns HT lrgn m' HT' rmap fs tenv,
    wf_HT lo HT ->
    wf_tenv tenv ->
    new_regions m lo tenv rmap live rgns HT lrgn = Some (m', HT') ->
    wf_mem fs lo tenv live HT m ->
    wf_mem fs lo tenv (rgns++live) HT' m' /\ wf_HT lo HT'.
  Proof.
    unfold new_regions; intros. eapply new_regions_wf_mem2; eauto.
  Qed.

  Lemma new_regions_wf_HT_bounds : forall lrgn m lo HT rmap m' HT' live rgns tenv,
    wf_HT_bounds HT ->
    new_regions m lo tenv rmap live rgns HT lrgn = Some (m', HT') ->
    wf_HT_bounds HT' /\
    max_HT HT <= max_HT HT'.
  Proof.
    unfold new_regions; intros. eapply new_regions_wf_HT_bounds2; eauto.
  Qed.

  Lemma freshn_prog : forall n live lrgn,
    freshn n live lrgn = None \/
    exists lrgns, exists live', exists rgns',
      freshn n live lrgn = Some (lrgns, live', rgns').
  Proof.
    intros. generalize dependent n. generalize dependent live.
    induction lrgn; simpl; intros.
    right. eauto. destruct a; auto.
    remember (freshn n live lrgn) as Hd. destruct Hd; auto.
    destruct p; auto. destruct p; auto.
    destruct (fresh n l1); eauto.
  Qed.
  
  Lemma new_regions_prog'' : forall m lo a h t,
    new_regions' m lo a h t = None \/
    (exists m', exists HT',
      new_regions' m lo a h t = Some (m', HT')).
  Proof.
    unfold new_regions'; intros. unfold next.
    destruct zle; eauto.
    destruct zle; eauto.
    destruct zlt; eauto.
    destruct zlt; eauto. 
  Qed.

  Lemma new_regions_prog' : forall rgns lrgn m lo tenv rmap live HT,
    new_regions m lo tenv rmap live rgns HT lrgn = None \/
    exists m', exists HT',
      new_regions m lo tenv rmap live rgns HT lrgn = Some (m', HT').
  Proof.
    induction rgns; destruct lrgn; simpl; intros; eauto.
    destruct zle; try congruence; eauto. 
    destruct zle; try congruence; eauto. 
    destruct zle; try congruence; eauto.
    destruct p; auto.
    remember (new_regions m lo tenv rmap live rgns HT lrgn) as Hd.
    destruct Hd; auto. destruct p; eauto. eapply new_regions_prog''; eauto.
  Qed.

  Lemma new_regions_prog : forall m lo tenv rmap live rgns HT lrgn,
    new_regions m lo tenv rmap live rgns HT lrgn = None \/
    exists m', exists HT',
      new_regions m lo tenv rmap live rgns HT lrgn = Some (m', HT').
  Proof.
    intros. eapply new_regions_prog'; eauto.
  Qed.

  (* ---------------------------------------------------------------------- *)
  (* Delete Region Properties *)

  (* Delete the rgns specified in live, returning the new memory, heap-typing, and live
   * list *)
  Fixpoint del_regionsh (live lsr:list rgn) : option (list rgn) :=
    match live, lsr with
      | nil, nil => Some nil
      | r1::live', r2::lsr' => if rgn_dec r1 r2 then del_regionsh live' lsr' else None
      | _, nil => Some live
      | _, _ => None
    end.
  
  Program Definition del_regions2 (m:cmem) (lo:layout) (live:list rgn) (HT1 HT2:heap_t) (rgns:list rgn) : option (cmem * heap_t) :=
    match next HT1 with
      | Some n =>
        if zle n 0 then None else
          if zle (Word.max_unsigned WORDSIZE_BITS) n then None
            else
              if zle n (Z.of_nat (h_addr m))
                then
                  let n' := (Z.of_nat (h_addr m) - n) in
                    Some ((mk_mem (setN n (list_repeat (h_addr m) Word.zero) (mem m)) (s_fresh m) (nat_of_Z n) _ _), HT1)
                else None
      | None => None
    end.
  Next Obligation.
    rewrite nat_of_Z_eq. omega. omega.
  Qed.
  Next Obligation.
    destruct m; simpl in *. rewrite nat_of_Z_eq in H2; try omega.
    destruct (zlt p (max_HT HT1 + ftyp_max + Z.of_nat h_addr0)).

    Lemma setN_get_zero : forall k n mem0,
      n > 0 ->
      (* n <= Z.of_nat k -> *)
      (forall p, 
        p >= n ->
        p < n + Z.of_nat k ->
        setN n (list_repeat k Word.zero) mem0 p = Word.zero).
    Proof.
      induction k; intros. crush. rewrite <- NPeano.Nat.add_1_l in *. simpl.
      destruct (zeq p n); subst.
      rewrite setN_outside; try omega.
      rewrite update_s; auto.
      rewrite Nat2Z.inj_add in *. 
      assert (Z.of_nat 1 = 1). crush. rewrite H2 in *.
      eapply IHk with (p := p); eauto; try omega. 
    Qed.
      
    erewrite setN_get_zero; eauto.
    rewrite setN_outside; auto. 
    assert (p >= Z.of_nat h_addr0). omega. eauto. 
    right. rewrite length_list_repeat. omega.
  Qed.

  Definition del_regions (m:cmem) (lo:layout) (live:list rgn) (HT1 HT2:heap_t) (rgns:list rgn) : option (cmem * heap_t * list rgn) :=
    match del_regionsh live rgns with
      | Some live' => 
        match del_regions2 m lo live' HT1 HT2 rgns with
          | Some (m', HT') => Some (m', HT', live')
          | None => None
        end
      | None => None
    end.

  Lemma del_regionh_prop : forall live rgns live',
    del_regionsh live rgns = Some live' ->
    live = rgns ++ live'.
  Proof.
    induction live; destruct rgns; simpl; intros. 
    inv H. reflexivity. inv H. inv H. reflexivity. 
    destruct rgn_dec; try congruence. subst. f_equal; auto.
  Qed.

  Lemma del_regions_prop : forall m lo live HT HT' rgns m' HT'' live',
    del_regions m lo live HT HT' rgns = Some (m', HT'', live') ->
    live = rgns ++ live' /\
    HT = HT''.
  Proof.
    unfold del_regions; intros.
    remember (del_regionsh live rgns) as Hd. 
    symmetry in HeqHd. destruct Hd; try congruence.
    remember (del_regions2 m lo l HT HT' rgns) as Hd2.
    symmetry in HeqHd2. destruct Hd2; try congruence.
    destruct p; subst. inv H.
    apply del_regionh_prop in HeqHd. subst. split; crush.
    unfold del_regions2 in *. unfold next in *.
    destruct zle; try congruence.
    destruct zle; try congruence.
    destruct zle; try congruence.
  Qed.

  Lemma check_HT_live_ctr' : forall t tenv live HT HT' lo n r,
    wf_HT_live live HT ->
    wf_tenv_typ live t ->
    heapt_ext2 live HT HT' ->
    In r live ->
    check_HT' lo HT' n r (flatten_typ lo tenv t) = true ->
    check_HT' lo HT n r (flatten_typ lo tenv t) = true.
  Proof.
    induction t; simpl; intros. 
    
    remember (Zenv.find n HT') as Hd.
    symmetry in HeqHd. destruct Hd; try congruence.
    destruct p; auto. destruct rgn_dec; try congruence. subst.
    unfold heapt_ext2 in H1. apply H1 in HeqHd; auto.
    rewrite HeqHd.
    destruct rgn_dec; try congruence.

    remember (Zenv.find n HT') as Hd.
    symmetry in HeqHd. destruct Hd; try congruence.
    destruct p; auto. destruct rgn_dec; try congruence. subst.
    unfold heapt_ext2 in H1. apply H1 in HeqHd; auto.
    rewrite HeqHd.
    destruct rgn_dec; try congruence.

    remember (Zenv.find n HT') as Hd.
    symmetry in HeqHd. destruct Hd; try congruence.
    destruct p; auto. destruct rgn_dec; try congruence. subst.
    unfold heapt_ext2 in H1. apply H1 in HeqHd; auto.
    rewrite HeqHd.
    destruct rgn_dec; try congruence.

    t_simpl_check_HT. unfold heapt_ext2 in H1. apply H1 in H3; auto.
    rewrite H3. destruct_c rgn_dec. destruct_c ftyp_eq_dec.

    remember (Nenv.find x tenv) as Hd.
    symmetry in HeqHd. destruct Hd; crush.
    destruct p; auto. destruct p; auto.
    rewrite pad_ftyps_sigma_comm in *.
    
    Lemma check_HT_live_ls_ctr' : forall f l lr r live HT HT' lo n,
      In r live ->
      heapt_ext2 live HT HT' ->
      check_HT' lo HT' n r (sigma (inst_prgn l lr) f) = true ->
      check_HT' lo HT n r (sigma (inst_prgn l lr) f) = true.
    Proof.
      induction f; crush.
      remember (Zenv.find n HT') as Hd. symmetry in HeqHd. 
      destruct Hd; try congruence. destruct p; auto.
      destruct rgn_dec; try congruence.
      destruct ftyp_eq_dec; try congruence. subst.
      eapply IHf in H1; eauto.
      unfold heapt_ext2 in H0. apply H0 in HeqHd; auto.
      rewrite HeqHd. 
      destruct rgn_dec; try congruence.
      destruct ftyp_eq_dec; try congruence.
    Qed.

    destruct b; auto.
    eapply check_HT_live_ls_ctr'; eauto.
    eapply check_HT_live_ls_ctr'; eauto.
    
    remember (Zenv.find n HT') as Hd.
    symmetry in HeqHd. destruct Hd; try congruence.
    destruct p; auto. destruct rgn_dec; try congruence. subst.
    unfold heapt_ext2 in H1. apply H1 in HeqHd; auto.
    rewrite HeqHd.
    destruct rgn_dec; try congruence.

    Lemma check_HT_app' : forall t1 t2 lo HT n r,
      check_HT' lo HT n r (t1 ++ t2) = check_HT' lo HT n r t1 && check_HT' lo HT (n + size_ftyps lo t1) r t2.
    Proof.
      induction t1; simpl; intros. 
      assert (n + 0 = n). omega. rewrite H. auto.
      remember (Zenv.find n HT) as Hd. destruct Hd; try intuition.
      destruct p. destruct rgn_dec; try intuition. 
      (* destruct_c ftyp_sub; try intuition. *)
      destruct ftyp_eq_dec; try intuition. subst.
      (* assert (n + (size_ftyp lo a + size_ftyps lo t1) = n + size_ftyp lo a + size_ftyps lo t1). omega. *)
      assert (n + (size_ftyp lo f + size_ftyps lo t1) = n + size_ftyp lo f + size_ftyps lo t1). omega.
      rewrite H. eauto.
    Qed.

    generalize dependent n. induction sz; intros; auto. inv H0.
    assert (wf_tenv_typ live (Typ_array t sz)). constructor; auto.
    simpl. rewrite check_HT_app'. rewrite check_HT_app' in H3. 
    rewrite andb_true_iff in H3. destruct H3. eapply IHt in H3; eauto.
    rewrite H3. rewrite andb_true_l. eauto.
    
    remember (Zenv.find n HT') as Hd.
    symmetry in HeqHd. destruct Hd; try congruence.
    destruct p; auto. destruct rgn_dec; try congruence. subst.
    unfold heapt_ext2 in H1. apply H1 in HeqHd; auto.
    rewrite HeqHd.
    destruct rgn_dec; try congruence.
    
  Qed.
  
  Lemma check_HT_live_ctr_ls' : forall live HT HT' lo sz n r,
    wf_HT_live live HT ->
    heapt_ext2 live HT HT' ->
    In r live ->
    check_HT' lo HT' n r (list_repeat sz Ftyp_int8) = true ->
    check_HT' lo HT n r (list_repeat sz Ftyp_int8) = true.
  Proof.
    induction sz; simpl; intros; auto.
    remember (Zenv.find n HT') as Hd. 
    symmetry in HeqHd. destruct Hd; try congruence.
    destruct p. destruct rgn_dec; try congruence. subst.
    unfold heapt_ext2 in H0. apply H0 in HeqHd; auto.
    rewrite HeqHd. destruct rgn_dec; try congruence.
    destruct ftyp_eq_dec; try congruence. eauto.
  Qed.

  Lemma del_regions_wf_mem2 : forall m lo HT HT' rgns live fs tenv m',
    wf_HT_live live HT ->
    list_disjoint rgns live ->
    heapt_ext HT HT' ->
    heapt_ext2 live HT HT' ->
    del_regions2 m lo live HT HT' rgns = Some (m', HT) ->
    wf_mem fs lo tenv (rgns ++ live) HT' m ->
    wf_mem fs lo tenv live HT m'.
  Proof.
    unfold wf_mem; intros.
    unfold heapt_ext in H1. t_dup H5.
    eapply H1 in H5. t_dup H5. 
    apply H4 in H5. t_simp. exists x.
    split. 

    unfold del_regions2 in H3. unfold next in H3.
    destruct zle; try congruence. destruct zle; try congruence.
    destruct zle; try congruence.
    inv H3. unfold load in *.
    destruct zle; try congruence. destruct zle; try congruence.
    simpl in *. rewrite nat_of_Z_eq; try omega.
    destruct zle.

    rewrite getN_setN_outside; auto.
    left. unfold size_ftyp_nat.
    assert (size_ftyp lo t >= 0). apply size_ftyp_nonneg. 
    rewrite nat_of_Z_eq; auto.
    
    apply max_HT_spec in H'. 
    assert (size_ftyp lo t >= 0). apply size_ftyp_nonneg. 
    assert (size_ftyp lo t < ftyp_max). apply size_ftyp_max.
    omegaContradiction.

    inv H6.
    econstructor; eauto.
    econstructor; eauto.
    econstructor; eauto.
    econstructor; eauto. destruct zeq; try congruence.
    unfold wf_HT_live in H. apply H in H'. inv H'; auto.
    unfold wf_HT_live in H. apply H in H'. inv H'.
    unfold check_HT in *. destruct zeq; try congruence.
    eapply check_HT_live_ctr'; eauto.
    econstructor; eauto.
    econstructor; eauto. destruct zeq; try congruence.
    unfold wf_HT_live in H. apply H in H'. inv H'; auto.
    unfold wf_HT_live in H. apply H in H'. inv H'.
    unfold check_HT in *. destruct zeq; try congruence.
    eapply check_HT_live_ctr_ls'; eauto.
  Qed.

  Lemma del_regions_wf_mem : forall m lo HT HT' rgns live fs tenv m',
    wf_HT_live live HT ->
    list_disjoint rgns live ->
    heapt_ext HT HT' ->
    heapt_ext2 live HT HT' ->
    del_regions m lo (rgns ++ live) HT HT' rgns = Some (m', HT, live) ->
    wf_mem fs lo tenv (rgns ++ live) HT' m ->
    wf_mem fs lo tenv live HT m'.
  Proof.
    unfold del_regions; intros.
    remember (del_regionsh (rgns ++ live) rgns) as Hd.
    symmetry in HeqHd. destruct Hd; try congruence.
    remember (del_regions2 m lo l HT HT' rgns) as Hd2.
    symmetry in HeqHd2. destruct Hd2; try congruence.
    destruct p; subst. inv H3.
    eapply del_regions_wf_mem2; eauto.
  Qed.

  Definition high_addr (m:cmem) : nat :=
    h_addr m.

  Lemma del_regionh_prog : forall rgns live,
    del_regionsh (rgns ++ live) rgns = Some live.
  Proof.
    induction rgns; destruct live; simpl; intros; eauto.
    destruct rgn_dec; crush.
    destruct rgn_dec; crush.
  Qed.

  Lemma store_high_addr_same : forall m lo n t v m',
    store m lo n t v = Some m' ->
    high_addr m = high_addr m'.
  Proof.
    unfold store; intros. destruct zle; try congruence.
    destruct zle; try congruence. inv H. crush.
  Qed.

  Lemma alloc_high_addr_same : forall m lo live HT t r r' n m',
    alloc m lo live HT t r r' = Some (n,m') ->
    high_addr m = high_addr m'.
  Proof.
    unfold alloc; intros. destruct t; try congruence.
    destruct in_dec; try congruence.
    destruct check_HT; try congruence.
    inv H. crush.
  Qed.
  
  Lemma free_high_addr_same : forall m lo n m',
    free m lo n = Some m' ->
    high_addr m = high_addr m'.
  Proof.
    unfold free; crush.
  Qed.

  Lemma new_regions_high_addr_prop' : forall m lo a HT t m' HT',
    new_regions' m lo a HT t = Some (m', HT') ->
    Z.of_nat (high_addr m) <= Z.of_nat (high_addr m').
  Proof.
    unfold new_regions'; intros. unfold next in H.
    destruct zle; try congruence.
    destruct zle; try congruence.
    destruct zlt; try congruence.
    destruct zlt; try congruence. 
    inv H. simpl in *. unfold high_addr.
    assert (size_ftyps lo t >= 0). apply size_ftyps_nonneg.
    rewrite nat_of_Z_plus; try omega.
    rewrite Nat2Z.inj_add. rewrite nat_of_Z_eq; omega. unfold ftyp_max in *. omega.
  Qed.
    
  Lemma new_regions_high_addr_prop : forall rgns m lo HT rmap m' HT' live tenv lrgn,
    new_regions m lo tenv rmap live rgns HT lrgn = Some (m', HT') ->
    max_HT HT + ftyp_max <= Z.of_nat (high_addr m') /\
    max_HT HT + ftyp_max < Word.max_unsigned WORDSIZE_BITS /\
    max_HT HT + ftyp_max > 0.
  Proof.
    unfold high_addr.
    induction rgns; destruct lrgn; simpl; intros; eauto.
    destruct zle; try congruence. destruct zle; try congruence. destruct zle; try congruence.
    repeat split; crush.
    crush.
    crush.
    destruct p; auto.
    remember (new_regions m lo tenv rmap live rgns HT lrgn) as Hd.
    destruct Hd; try congruence. destruct p; auto.
    symmetry in HeqHd. eapply IHrgns in HeqHd; eauto.
    t_simp. repeat split; crush.
    eapply new_regions_high_addr_prop'; eauto.
  Qed.

  Lemma del_regions_prog : forall m lo live HT HT' rgns,
    max_HT HT + ftyp_max <= Z.of_nat (high_addr m) ->
    max_HT HT + ftyp_max > 0 ->
    exists m', exists HT'', exists live', 
      del_regions m lo (rgns ++ live) HT HT' rgns = Some (m', HT'', live').
  Proof.
    unfold del_regions; intros. rewrite del_regionh_prog.
    remember (del_regionsh (rgns ++ live) rgns) as Hd.
    unfold del_regions2. unfold next.
    destruct zle; try congruence; eauto.
    destruct zle; try congruence; eauto. 
    destruct m. simpl in *. omegaContradiction.
    destruct zle; try congruence; eauto. unfold high_addr in H. omegaContradiction.
  Qed.

  Definition wf_mem_metadata (HT:heap_t) (m:cmem) : Prop :=
    max_HT HT + ftyp_max <= Z.of_nat (high_addr m).

  Lemma max_HT_total_size : forall t n lo HT a,
    n >= 0 ->
    max_HT (construct_HT lo HT (max_HT HT + n) a t) <= max_HT HT + n + size_ftyps lo t.
  Proof.
    induction t; crush.
    destruct zlt. 
    assert (size_ftyp lo a >= 0). apply size_ftyp_nonneg.
    assert (size_ftyps lo t >= 0). apply size_ftyps_nonneg.
    omega.
    assert (max_HT HT + n + (size_ftyp lo a + size_ftyps lo t) =
            (max_HT HT + n + size_ftyp lo a) + size_ftyps lo t). omega.
    rewrite H0.
    assert (max_HT HT + n + size_ftyp lo a = max_HT HT + (n + size_ftyp lo a)).
    omega.
    rewrite H1.
    eapply IHt; eauto.
    assert (size_ftyp lo a >= 0). apply size_ftyp_nonneg.
    omega.
  Qed.

  Lemma new_regions_wf_meta : forall rgns m lo HT rmap m' HT' live tenv lrgn,
    new_regions m lo tenv rmap live rgns HT lrgn = Some (m', HT') ->
    wf_mem_metadata HT' m'.
  Proof.
    induction rgns; destruct lrgn; simpl; intros; eauto.
    destruct zle; try congruence. destruct zle; try congruence. destruct zle; try congruence.
    inv H. unfold wf_mem_metadata; unfold high_addr; crush. 
    inv H. inv H. destruct p; auto.
    remember (new_regions m lo tenv rmap live rgns HT lrgn) as Hd.
    destruct Hd; try congruence. destruct p; auto.
    symmetry in HeqHd. eapply IHrgns in HeqHd; eauto.
    unfold new_regions' in H. unfold next in H.
    destruct zle; try congruence. destruct zle; try congruence.
    destruct zlt; try congruence. destruct zlt; try congruence.
    inv H. unfold wf_mem_metadata. unfold high_addr. simpl in *. 
    rewrite nat_of_Z_eq.
    assert ( max_HT (construct_HT lo h (max_HT h + ftyp_max) a (sigma rmap (flatten_typ lo tenv t))) <=
      max_HT h + ftyp_max + size_ftyps lo (sigma rmap (flatten_typ lo tenv t))).
    apply max_HT_total_size. unfold ftyp_max in *. omega.
    omega. 
    assert (size_ftyps lo (sigma rmap (flatten_typ lo tenv t)) >= 0).
    apply size_ftyps_nonneg.
    unfold ftyp_max in *. omega.
  Qed.
    
  Lemma del_regions_wf_meta : forall m lo live HT HT' rgns m' HT'' live',
    del_regions m lo live HT HT' rgns = Some (m', HT'', live') ->
    wf_mem_metadata HT'' m'.
  Proof.
    unfold del_regions; intros. destruct (del_regionsh live rgns); try congruence.
    remember (del_regions2 m lo l HT HT' rgns) as Hd.
    symmetry in HeqHd. destruct Hd; try congruence.
    destruct p; auto. inv H.
    unfold del_regions2 in HeqHd. unfold next in HeqHd.
    destruct zle; try congruence.
    destruct zle; try congruence.
    destruct zle; try congruence. inv HeqHd.
    unfold wf_mem_metadata. unfold high_addr. simpl in *.
    rewrite nat_of_Z_eq; omega.
  Qed.
    
End SVAmem.

