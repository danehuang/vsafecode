(* Other library imports *)
Add LoadPath "../libs".
Add LoadPath "../libs/CompCert-Toolkit".
Require Import Tactics.
Require Import Bits.
Require Import Consider.

Require Import Flocq.Appli.Fappli_IEEE_bits.

Require Import Coqlib.
Require Import Axioms.


(* Illvm imports *)
Require Import Utility.
Require Import IllvmAST.
Require Import TargetData.


(* ---------------------------------------------------------------------- *)
(* Run-time tags and values *)

(* Tags that a run-time value can have *)
Inductive rt_tag :=
| RT_int : forall sz, (sz < MAX_I_BITS)%nat -> Word.int sz -> rt_tag
| RT_fun : lab -> rt_tag. (* We can get rid of this ... *)

(* Floats, doubles and pointers are just bit-vectors. *) 
Definition RT_float (f:float_t) := RT_int 31 lt_31_MAX_I_BITS (Word.repr (Word.unsigned f)).
Definition RT_double (d:double_t) := RT_int 63 lt_63_MAX_I_BITS (Word.repr (Word.unsigned d)).
Definition RT_ptr i := RT_int WORDSIZE_BITS lt_63_MAX_I_BITS i.
 
(* Run-time value, note that its flat, i.e., the typ's give it structure. *)
Definition rt_val := list rt_tag.

(* Convert a tag into a run-time value *)
Definition tag2rt (tag:rt_tag) := tag :: nil.

(* Size of a tag in bytes *)
Definition size_rttag (lo:layout) (tag:rt_tag) : Z :=
  match tag with
    | RT_int sz pf _ => size_ftyp lo (Ftyp_int sz pf)
    | RT_fun _ => size_ftyp lo (Ftyp_fun nil nil None)
  end.
Definition size_rttag_nat (lo:layout) (tag:rt_tag) : nat :=
  nat_of_Z (size_rttag lo tag).

(* Random bit-pattern generator. *)
Parameter UNDEF_STREAM : unit -> Z.

Fixpoint undef_ls ts :=
  match ts with
    | nil => nil
    | t::ts =>
      match t with
        | Ftyp_float => (RT_float (Word.repr (UNDEF_STREAM tt)) :: undef_ls ts)
        | Ftyp_double => (RT_double (Word.repr (UNDEF_STREAM tt)) :: undef_ls ts)
        | Ftyp_int sz pf => (RT_int sz pf (Word.repr (UNDEF_STREAM tt)) :: undef_ls ts)
        | Ftyp_ptr _ _ => (RT_ptr (Word.repr (UNDEF_STREAM tt)) :: undef_ls ts)
        | Ftyp_fun _ _ _ => (RT_fun (Word.repr (UNDEF_STREAM tt)) :: undef_ls ts)
        | Ftyp_ptrU _ _ => (RT_ptr (Word.repr (UNDEF_STREAM tt)) :: undef_ls ts)
      end
  end.

(* Convert a constant to rt_val *)
Definition const2rtv (c:const) : rt_val :=
  match c with
    | Const_null => (RT_ptr (Word.repr 0) :: nil)
    | Const_nullU => (RT_ptr (Word.repr 0) :: nil)
    | Const_float f => (RT_float f :: nil)
    | Const_double d => (RT_double d :: nil)
    | Const_int sz pf i => (RT_int sz pf i :: nil)
    | Const_fun l => (RT_fun l :: nil)
    | Const_undef ts => undef_ls ts
    | Const_baddr l1 l2 => (RT_ptr l2 :: nil)
    (* | Const_struct ls => List.fold_left (fun acc c => const2rtv c ++ acc) ls nil *)
  end.

Section OP.
  Variable o : operand.
  Variable env : Nenv.t rt_val.

  (* Convert an operand to rt_val *)
  Definition op2rtv : option rt_val :=
    match o with
      | Op_reg x => Nenv.find x env
      | Op_const c => Some (const2rtv c)
    end.

  (* Convert an operand to a pointer *)
  Definition op2ptr : option PTRTYP :=
    match op2rtv with
      | Some rt => match rt with
                     | RT_int WORDSIZE_BITS _ addr :: nil => Some (Word.repr (Word.unsigned addr))
                     | _ => None
                   end
      | None => None
    end.

  (* Convert an operand to a function pointer *)
  Definition op2fun : option lab :=
    match op2rtv with
      | Some rt => match rt with
                     | RT_fun l :: nil => Some l
                     | _ => None
                   end
      | None => None
    end.
End OP.

(* ---------------------------------------------------------------------- *)
(* Value Typing *)

(* ---------------------------------------------------------------------- *)
(* Heap Typing Definitions *)

Definition heap_t := Zenv.t (ftyp * rgn).

Section HT_SEC.
 
  Variable lo : layout.
  Variable HT : heap_t.

  Fixpoint check_HT' (base:Z) (r:rgn) (t:ftyps) : bool :=
    match t with
      | nil => true
      | t'::ts => 
        match Zenv.find base HT with
          | Some (t'',r'') => 
            if rgn_dec r r'' 
              then
                if ftyp_eq_dec t' t'' (* ftyp_sub t' t'' *)
                  then check_HT' (base + size_ftyp lo t') r ts 
                  else false
            else false
          | None => false
        end
  end.
                    
  Definition check_HT (base:Z) (r:rgn) (t:ftyps) : bool :=
    if zeq base 0 then true else check_HT' base r t.

  Fixpoint construct_HT (base:Z) (r:rgn) (t:ftyps) : heap_t :=
    match t with
      | nil => HT
      | t'::ts => 
        let HT' := construct_HT (base + size_ftyp lo t') r ts in
          Zenv.add base (t',r) HT'
    end.

End HT_SEC.

Ltac t_simpl_check_HT :=
  repeat 
    match goal with
      | [ H: context [ match ?p with | (_, _) => _ end ] |- _ ] => destruct p
      | [ H: context [ match ?x with | Some _ => _ | None => _ end ] |- _ ] => 
        (consider x); intros; try congruence
      | [ H: context [ if ?x then _ else _ ] |- _ ] =>
        (consider x); intros; try congruence
    end; simpl in *; subst.

(* Heap type extension *)
Definition heapt_ext (HT HT':heap_t) : Prop :=
  forall n t r,
    Zenv.find n HT = Some (t,r) ->
    Zenv.find n HT' = Some (t,r).

(* Another heap type extension stating all values in the new heap type that are 
   in the previous live regions also belong to the old heap type. *)
Definition heapt_ext2 (live:list rgn) (HT HT':heap_t) : Prop :=
  forall n t r,
    Zenv.find n HT' = Some (t,r) ->
    In r live ->
    Zenv.find n HT = Some (t,r).

(* Well-formed heap-type *)
Definition wf_HT (lo:layout) (HT:heap_t) : Prop :=
  forall n t r,
    Zenv.find n HT = Some (t,r) ->
    (forall n' t' r',
      n <> n' ->
      Zenv.find n' HT = Some (t',r') ->
      n' + size_ftyp lo t' <= n \/ 
      n + size_ftyp lo t <= n') /\
    0 < n /\ 
    n + size_ftyp lo t < Word.modulus WORDSIZE_BITS.

(* The regions a heap-type mentions is closed under live *)
Definition wf_HT_live (live:list rgn) (HT:heap_t) : Prop :=
  forall n r t,
    Zenv.find n HT = Some (t, r) ->
    wf_tenv_ftyp live t.

(* Get the maximum address mapped in the heap-typing *)
Fixpoint max_HT (HT:heap_t) : Z :=
    match HT with
      | nil => 0
      | (x,y)::HT' => 
        let n := max_HT HT' in if zlt n x then x else n
    end.

Lemma max_HT_spec : forall HT n t,
  Zenv.find n HT = Some t ->
  n <= max_HT HT.
Proof.
  induction HT; simpl; intros; try congruence. destruct a.
  destruct (OrderedTypeEx.Z_as_OT.eq_dec n z); subst.
  destruct zlt; omega.
  destruct zlt; crush.
Qed.

Definition wf_HT_bounds (HT:heap_t) : Prop :=
  max_HT HT + ftyp_max < Word.max_unsigned WORDSIZE_BITS /\
  max_HT HT + ftyp_max > 0.
 
(* ---------------------------------------------------------------------- *)
(* Value Typing *)

Definition check_fun (fs:functions) (l:lab) (prgn:list rgn) (sig:list typ) (r:option typ) : bool :=
  if lab_dec l Word.zero then true
    else 
      match lookup_fun l fs with
        | Some f => 
          if list_eq_dec typ_eq_dec (f_sig f) sig then
            if list_eq_dec rgn_dec (domain (f_prgn f)) prgn then
              match r, (f_ret f) with
                | Some t1, Some t2 => if typ_eq_dec t1 t2 then true else false
                | None, None => true
                | _, _ => false
              end
              else false
            else false
        | None => false
      end.

Section VALUE_SEC.

  Variable fs : functions.
  Variable lo : layout.
  Variable tenv : tenv_t.

  Inductive wf_value' : list rgn -> heap_t -> rt_tag -> ftyp -> Prop :=
  | wf_val_float : forall live HT f,
    wf_value' live HT (RT_float f) Ftyp_float
  | wf_val_double : forall live HT d,
    wf_value' live HT (RT_double d) Ftyp_double
  | wf_val_int : forall live HT sz pf (i:Word.int sz),
    wf_value' live HT (RT_int sz pf i) (Ftyp_int sz pf)
  | wf_val_ptr : forall live HT n t r t',
    t' = flatten_typ lo tenv t ->
    (if zeq (Word.unsigned n) 0 then True else In r live) ->
    check_HT lo HT (Word.unsigned n) r t' = true ->
    wf_value' live HT (RT_ptr n) (Ftyp_ptr t r)
  | wf_val_fun : forall live HT prgn sig ret l,
    check_fun fs l prgn sig ret = true ->
    wf_value' live HT (RT_fun l) (Ftyp_fun prgn sig ret)
  | wf_val_ptrU : forall live HT n sz r t',
    t' = list_repeat sz Ftyp_int8 ->
    (if zeq (Word.unsigned n) 0 then True else In r live) ->
    check_HT lo HT (Word.unsigned n) r t' = true ->
    wf_value' live HT (RT_ptr n) (Ftyp_ptrU sz r).
  Hint Constructors wf_value'.
  
  Inductive wf_value : list rgn -> heap_t -> rt_val -> ftyps -> Prop :=
  | wf_val_nil : forall live HT,
    wf_value live HT nil nil
  | wf_val_cons : forall live HT v t vs ts,
    wf_value' live HT v t ->
    wf_value live HT vs ts ->
    wf_value live HT (v::vs) (t::ts).
  Hint Constructors wf_value.
  
End VALUE_SEC.

(* ---------------------------------------------------------------------- *)
(* Value Typing Properties *)

Lemma wf_val_live_ext2 : forall fs lo tenv t v live HT r,
  wf_value' fs lo tenv live HT v t ->
  wf_value' fs lo tenv (r :: live) HT v t.
Proof.
  induction 1; econstructor; eauto; destruct_c zeq; intuition.
Qed.

Lemma wf_val_live_ext' : forall fs lo tenv t HT live v rgns,
  wf_value' fs lo tenv live HT v t ->
  wf_value' fs lo tenv (rgns++live) HT v t.
Proof.
  induction 1; econstructor; eauto; destruct_c zeq; intuition.
Qed.

Lemma wf_val_live_ext : forall fs lo tenv t HT live v rgns,
  wf_value fs lo tenv live HT v t ->
  wf_value fs lo tenv (rgns++live) HT v t.
Proof.
  induction 1; econstructor; eauto. eapply wf_val_live_ext'; eauto.
Qed.

Lemma check_HT_HT_ext' : forall lo t HT HT' n r,
  heapt_ext HT HT' ->
  check_HT' lo HT n r t = true ->
  check_HT' lo HT' n r t = true.
Proof.
  induction t; simpl; intros; auto. t_simpl_check_HT.
  unfold heapt_ext in H. apply H in H0. rewrite H0. 
  destruct_c rgn_dec. destruct_c ftyp_eq_dec. eauto.
Qed.

Lemma check_HT_HT_ext : forall lo t HT HT' n r,
  heapt_ext HT HT' ->
  check_HT lo HT n r t = true ->
  check_HT lo HT' n r t = true.
Proof.
  unfold check_HT; intros. destruct_c zeq. eapply check_HT_HT_ext'; eauto.
Qed.
  
Lemma wf_val_HT_ext' : forall fs lo tenv t HT HT' live v,
  heapt_ext HT HT' ->
  wf_value' fs lo tenv live HT v t ->
  wf_value' fs lo tenv live HT' v t.
Proof.
  induction 2; econstructor; eauto; eapply check_HT_HT_ext; eauto.
Qed.

Lemma wf_val_HT_ext : forall fs lo tenv t HT HT' live v,
  heapt_ext HT HT' ->
  wf_value fs lo tenv live HT v t ->
  wf_value fs lo tenv live HT' v t.
Proof.
  induction 2; econstructor; eauto. eapply wf_val_HT_ext'; eauto.
Qed.

(* ---------------------------------------------------------------------- *)
(* Encoding and Decoding bytes *)

(* ---------------------------------------------------------------------- *)
(* From Compcert with minor changes *)
Fixpoint bytes_of_int (n : nat) (x : Z) {struct n} : list int8 :=
  match n with
  | 0%nat => nil
  | S m => Word.repr x :: bytes_of_int m (x / 256)
  end.

Fixpoint int_of_bytes (l : list int8) : Z :=
  match l with
  | nil => 0
  | b :: l' => Word.unsigned b + int_of_bytes l' * 256
  end.

Lemma int_of_bytes_of_int:
  forall n x,
  int_of_bytes (bytes_of_int n x) = x mod (two_p (Z_of_nat n * 8)).
Proof.
  induction n; intros.
  simpl. rewrite Zmod_1_r. auto.
  Opaque Word.wordsize.
  rewrite inj_S. simpl.
  replace (Zsucc (Z_of_nat n) * 8) with (Z_of_nat n * 8 + 8) by omega.
  rewrite two_p_is_exp; try omega. 
  rewrite Zmod_recombine. rewrite IHn. rewrite Zplus_comm. reflexivity. 
  apply two_p_gt_ZERO. omega. apply two_p_gt_ZERO. omega.
  Transparent Word.wordsize.
Qed.

Lemma length_bytes_of_int:
  forall n x, length (bytes_of_int n x) = n.
Proof.
  induction n; simpl; intros. auto. decEq. auto.
Qed.

(* ---------------------------------------------------------------------- *)
(* Decoding and encoding runtime tags / bits *)

Definition encode_rttag (lo:layout) (tag:rt_tag) : list int8 :=
  let bytes :=
  match tag with
    | RT_int n pf i => bytes_of_int (size_ftyp_nat lo (Ftyp_int n pf)) (Word.unsigned i)
    | RT_fun l => bytes_of_int (size_ftyp_nat lo (Ftyp_ptr Typ_int32 0%nat)) (Word.unsigned l)
  end in
  if endian lo then rev bytes else bytes.

Fixpoint encode_rtval (lo:layout) (ftls:ftyps) (rt:rt_val) : list int8 :=
  match rt with
    | nil => nil
    | tag :: tl' => encode_rttag lo tag ++ (encode_rtval lo ftls tl')
  end.

(* Turn a list of bytes into a run-time value as indicated by its ftyps *)
Definition decode_rttag (lo:layout) (ft:ftyp) (bytes:list int8) : rt_tag :=
  let bytes := if endian lo then rev bytes else bytes in
  match ft with
    | Ftyp_float => RT_float (Word.repr (int_of_bytes bytes))
    | Ftyp_double => RT_double (Word.repr (int_of_bytes bytes))
    | Ftyp_int n pf => RT_int n pf (Word.repr (int_of_bytes bytes))
    | Ftyp_ptr _ _ => RT_ptr (Word.repr (int_of_bytes bytes))
    | Ftyp_fun _ _ _ => RT_fun (Word.repr (int_of_bytes bytes))
    | Ftyp_ptrU _ _ => RT_ptr (Word.repr (int_of_bytes bytes))
  end.
Fixpoint decode_rtval (lo:layout) (ftls:ftyps) (bytes:list int8) : rt_val :=
  match ftls with 
    | ft' :: ftls' => 
      decode_rttag lo ft' (firstn (size_ftyp_nat lo ft') bytes) ::
      decode_rtval lo ftls' (skipn (size_ftyp_nat lo ft') bytes)
    | nil => nil
  end.

Lemma decode_encode_int_same : forall sz pf (i:Word.int sz) lo,
  RT_int sz pf
  (Word.repr 
    (int_of_bytes
      (bytes_of_int (size_ftyp_nat lo (Ftyp_int sz pf))
        (Word.unsigned i)))) = RT_int sz pf i.
Proof.
  intros. f_equal; auto. rewrite int_of_bytes_of_int. unfold size_ftyp_nat. unfold size_ftyp.
  rewrite nat_of_Z_eq. rewrite Z.mul_add_distr_r. destruct i. apply Word.mkint_eq. simpl. 
  unfold Word.modulus in *. unfold Word.wordsize in *. rewrite two_power_nat_two_p in *.
  
  assert (8 > 0). omega.
      
  assert (Z.of_nat (S sz) <= Z.of_nat sz / 8 * 8 + 8).
  specialize (Z_div_mod_eq (Z.of_nat sz) 8 H); intros.
  assert (Z.of_nat sz - Z.of_nat sz mod 8 = 8 * (Z.of_nat sz / 8)). omega.
  rewrite Zmult_comm. rewrite <- H1.
  rewrite inj_S. rewrite <- Z.add_1_l.
  specialize (Z_mod_lt (Z.of_nat sz) 8 H); intros. omega.
  
  assert (two_p (Z.of_nat (S sz)) > 0). apply two_p_gt_ZERO. omega.
  specialize (Z_mod_lt intval (two_p (Z.of_nat (S sz))) H1); intros.
  
  assert (0 <= Z.of_nat (S sz) <= Z.of_nat sz / 8 * 8 + 8). omega.
  apply two_p_monotone in H3.
  assert (0 <= intval mod two_p (Z.of_nat (S sz)) < two_p (Z.of_nat sz / 8 * 8 + 8)). omega.
  
  assert (intval mod (two_p (Z.of_nat (S sz))) = intval).
  rewrite Zmod_small; auto.
  rewrite H5 in *.
  
  rewrite Zmod_small in *; auto. rewrite Zmod_small; auto.
  rewrite Zmod_small; auto.
  
  assert (0 <= Z.of_nat sz / 8). apply Z_div_pos; omega. omega.
Qed.

Lemma decode_encode_fun_same : forall n lo,
  RT_fun
  (Word.repr
    (int_of_bytes
      (bytes_of_int (size_ftyp_nat lo (Ftyp_ptr Typ_int32 0%nat))
        (Word.unsigned n)))) = RT_fun n.
Proof.
  intros. f_equal. rewrite int_of_bytes_of_int. simpl. destruct n.
  apply Word.mkint_eq. simpl. unfold Word.modulus in *.
  unfold Word.wordsize in *. rewrite two_power_nat_two_p.
  unfold two_p. simpl. rewrite Zmod_mod. rewrite Zmod_small; auto.
Qed.

Lemma decode_encode_same : forall t v fs lo tenv HT live,
  wf_value' fs lo tenv HT live v t ->
  decode_rttag lo t (encode_rttag lo v) = v.
Proof.
  intros. inv H; unfold decode_rttag; unfold encode_rttag.
  { unfold RT_float. destruct (endian lo). rewrite rev_involutive.
    rewrite Word.repr_unsigned. apply decode_encode_int_same.
    rewrite Word.repr_unsigned. apply decode_encode_int_same. }
  { unfold RT_double. destruct (endian lo). rewrite rev_involutive. 
    rewrite Word.repr_unsigned. apply decode_encode_int_same.
    rewrite Word.repr_unsigned. apply decode_encode_int_same. }
  { destruct (endian lo). rewrite rev_involutive.
    apply decode_encode_int_same. apply decode_encode_int_same. }
  { destruct (endian lo). rewrite rev_involutive. 
    apply decode_encode_int_same. apply decode_encode_int_same. }
  { destruct (endian lo). rewrite rev_involutive.
    apply decode_encode_fun_same. apply decode_encode_fun_same. }
  { destruct (endian lo). rewrite rev_involutive. 
    apply decode_encode_int_same. apply decode_encode_int_same. }
Qed.

(* ---------------------------------------------------------------------- *)

Fixpoint bytestoint' (rt:rt_val) : list int8 :=
  match rt with
    | nil => nil
    | v::rt' => match v with 
                  | RT_int 7 _ b => b :: bytestoint' rt'
                  | _ => Word.zero :: bytestoint' rt'
                end
  end.
Definition bytestoint16 (lo:layout) (rt:rt_val) : rt_val :=
  RT_int 15 lt_15_MAX_I_BITS (Word.repr (int_of_bytes (bytestoint' rt))) :: nil.
Definition bytestoint (lo:layout) (rt:rt_val) : rt_val :=
  RT_int 31 lt_31_MAX_I_BITS (Word.repr (int_of_bytes (bytestoint' rt))) :: nil.
Definition bytestoint64 (lo:layout) (rt:rt_val) : rt_val :=
  RT_int 63 lt_63_MAX_I_BITS (Word.repr (int_of_bytes (bytestoint' rt))) :: nil.

(* ---------------------------------------------------------------------- *)

Fixpoint anytobytes' (lo:layout) (rt:rt_val) : list int8 :=
  match rt with
    | nil => nil
    | v::rt' => match v with
                  | RT_int n pf i => bytes_of_int (size_ftyp_nat lo (Ftyp_int n pf)) (Word.unsigned i) ++ anytobytes' lo rt'
                  | RT_fun l => bytes_of_int (size_ftyp_nat lo (Ftyp_ptr Typ_int32 0%nat)) (Word.unsigned l) ++ anytobytes' lo rt'
                end
  end.

Definition anytobytes (lo:layout) (rt:rt_val) : rt_val :=
  map (fun b => RT_int 7 lt_7_MAX_I_BITS b) (anytobytes' lo rt).

Lemma wf_val_anytobytesh : forall n bs fs lo tenv live HT,
  n = length bs ->
  wf_value fs lo tenv live HT (map (fun b => RT_int 7 lt_7_MAX_I_BITS b) bs) (list_repeat n Ftyp_int8).
Proof.
  induction n; destruct bs; crush. econstructor; eauto.
  econstructor; eauto. destruct i. 
  assert (Word.repr intval = Word.mkint _ intval intrange). 
  apply Word.mkint_eq. rewrite Zmod_small; auto. rewrite <- H.
  econstructor; eauto.
Qed.

Lemma wf_val_anytobytes : forall b fs lo tenv live HT n,
  n = length (anytobytes lo b) ->
  wf_value fs lo tenv live HT (anytobytes lo b) (list_repeat n Ftyp_int8).
Proof.
  intros. specialize (wf_val_anytobytesh n (anytobytes' lo b) fs lo tenv live HT); intros. 
  unfold anytobytes in *. rewrite map_length in H. crush.
Qed.

Lemma wf_val_any_size_nat' : forall fs lo tenv live HT t v,
  wf_value' fs lo tenv live HT v t ->
  (length (anytobytes lo (v::nil))) = size_ftyp_nat lo t.
Proof.
  induction 1; unfold anytobytes; simpl; intros; auto. rewrite map_length.
  unfold size_ftyp_nat. unfold size_ftyp. rewrite app_length.
  rewrite length_bytes_of_int. auto.
Qed.

Lemma wf_val_any_size_nat : forall fs lo tenv live HT t v,
  wf_value fs lo tenv live HT v t ->
  (length (anytobytes lo v) = size_ftyps_nat lo t)%nat.
Proof.
  induction t; simpl; intros.
  { inv H. simpl. auto. }
  { assert (forall lo t1 t2, 
    size_ftyps_nat lo (t1 :: t2) = (size_ftyp_nat lo t1 + size_ftyps_nat lo t2)%nat).
    intros. unfold size_ftyps_nat. unfold size_ftyp_nat. simpl.
    rewrite nat_of_Z_plus; auto. apply size_ftyp_nonneg. apply size_ftyps_nonneg.
    rewrite H0. inv H. eapply IHt in H7.
    unfold anytobytes in *. rewrite map_length in *. 
    inv H6; simpl; repeat f_equal; auto. 
    unfold size_ftyp_nat. unfold size_ftyp. rewrite app_length. rewrite length_bytes_of_int.
    auto. }
Qed.

Lemma wf_val_any_size : forall fs lo tenv live HT t v,
  wf_value fs lo tenv live HT v t ->
  Z.of_nat (length (anytobytes lo v)) = size_ftyps lo t.
Proof.
  intros. apply wf_val_any_size_nat in H. unfold size_ftyps_nat in H. 
  assert (Z.of_nat (length (anytobytes lo v)) = Z.of_nat (nat_of_Z (size_ftyps lo t))).
  omega. rewrite H0. rewrite nat_of_Z_eq; auto. apply size_ftyps_nonneg.
Qed.

(* ---------------------------------------------------------------------- *)

Lemma check_HT_mid' : forall t t' s addr lo HT f,
  ftyps_subset t' t = true ->
  check_HT' lo HT (addr + size_ftyp lo f) s t = true ->
  check_HT' lo HT (addr + size_ftyp lo f) s t' = true.
Proof.
  induction t; destruct t'; crush.
  (* case_eq (ftyp_subset f a); intros. rewrite H1 in H. *)
  destruct ftyp_eq_dec; try congruence.
  remember (Zenv.find (addr + size_ftyp lo f0) HT) as Hd.
  symmetry in HeqHd. destruct Hd; try congruence.
  destruct p. destruct rgn_dec; try congruence. subst.
  destruct_c ftyp_eq_dec; eauto.
Qed.

Lemma check_HT_mid : forall t n t' lo HT addr r rmap,
  addr > 0 ->
  (n < length t)%nat ->
  ftyps_subset t' (skipn n t) = true ->
  check_HT lo HT addr (alpha rmap r) (sigma rmap t) = true ->
  check_HT lo HT (addr + walk_offset lo n t) (alpha rmap r) (sigma rmap t') = true.
Proof.
  induction t; crush.
  destruct n; simpl in *.
  { unfold check_HT in *. destruct zeq; crush. destruct_c zeq.
    remember (Zenv.find addr HT) as Hd. destruct_c Hd.
    destruct p. destruct_c rgn_dec. subst.
    destruct t'. 
    simpl in H1. unfold check_HT'. reflexivity.
    simpl in H1. destruct_c ftyp_eq_dec. subst.
    assert (addr + 0 = addr). omega. rewrite H3.
    simpl. rewrite <- HeqHd. destruct_c rgn_dec. destruct_c ftyp_eq_dec.
    eapply check_HT_mid'; eauto. eapply ftyps_subset_sigma; eauto. }
  { assert (addr + (walk_offset lo n t + size_ftyp lo a) = 
    (addr + size_ftyp lo a) + (walk_offset lo n t)). omega.
    rewrite H3. eapply IHt; eauto. size_ftyp_prop. omega. omega.
    unfold check_HT in *. destruct zeq; crush. destruct_c zeq.
    destruct_c (Zenv.find addr HT). destruct p. destruct_c rgn_dec.
    destruct_c ftyp_eq_dec. erewrite <- size_ftyp_sigma_inv; eauto. }
Qed.

Lemma check_HT_bounds : forall t r n lo HT,
  n > 0 ->
  t <> nil ->
  wf_HT_bounds HT ->
  check_HT lo HT n r t = true ->
  n <= Word.max_unsigned WORDSIZE_BITS.
Proof.
  destruct t; intros. 
  { unfold check_HT in H2. destruct zeq; crush. }
  { unfold check_HT in H2. destruct zeq; crush. 
    remember (Zenv.find n HT) as Hd. destruct_c Hd. 
    symmetry in HeqHd. unfold wf_HT_bounds in H1. destruct H1.
    apply max_HT_spec in HeqHd. unfold ftyp_max in *. omega. }
Qed.

Lemma check_HT_subset' : forall t2 t1 lo HT addr r rmap,
  ftyps_subset t2 t1 = true ->
  check_HT' lo HT addr r (sigma rmap t1) = true ->
  check_HT' lo HT addr r (sigma rmap t2) = true.
Proof.
  induction t2; simpl; intros; auto.
  destruct_c t1. destruct_c ftyp_eq_dec. subst. simpl in *.
  destruct_c (Zenv.find addr HT). destruct p.
  destruct_c rgn_dec. destruct_c ftyp_eq_dec.
  eapply IHt2; eauto.
Qed.

Lemma check_HT_subset : forall t2 t1 lo HT addr r rmap,
  ftyps_subset t2 t1 = true ->
  check_HT lo HT addr r (sigma rmap t1) = true ->
  check_HT lo HT addr r (sigma rmap t2) = true.
Proof.
  intros. unfold check_HT in *. destruct_c zeq.
  eapply check_HT_subset'; eauto.
Qed.

Lemma check_HT_subset_bytes : forall sz1 sz2 lo HT rmap addr r,
  check_HT lo HT addr r (sigma rmap (list_repeat sz1 Ftyp_int8)) = true ->
  Z.of_nat sz2 <= Z.of_nat sz1 ->
  check_HT lo HT addr r (sigma rmap (list_repeat sz2 Ftyp_int8)) = true.
Proof.
  intros. eapply check_HT_subset; eauto. eapply ftyps_subset_ls_repeat; eauto. omega.
Qed.

Lemma check_HT_range' : forall sz lo HT i1 i2 r,
  i1 <= Word.modulus WORDSIZE_BITS ->
  wf_HT lo HT ->
  i2 < Z.of_nat sz ->
  check_HT' lo HT i1 r (list_repeat sz Ftyp_int8) = true ->
  i1 + i2 < Word.modulus WORDSIZE_BITS.
Proof.
  induction sz; simpl; intros; auto.
  crush.
  remember (Zenv.find i1 HT) as Hd. symmetry in HeqHd.
  destruct_c Hd. destruct p. destruct_c rgn_dec. destruct_c ftyp_eq_dec. subst.
  eapply IHsz with (i2 := i2 - 1) in H2; eauto. omega.
  unfold wf_HT in H0. apply H0 in HeqHd. t_simp. simpl in H5. omega.
  rewrite Zpos_P_of_succ_nat in H1. omega.
Qed.

Lemma check_HT_range : forall sz lo HT i1 i2 r,
  i1 <= Word.modulus WORDSIZE_BITS ->
  wf_HT lo HT ->
  i2 < Z.of_nat sz <= Word.modulus WORDSIZE_BITS ->
  check_HT lo HT i1 r (list_repeat sz Ftyp_int8) = true ->
  i1 + i2 < Word.modulus WORDSIZE_BITS.
Proof.
  unfold check_HT; intros. destruct_c zeq. subst. omega.
  eapply check_HT_range'; eauto. omega.
Qed.

Lemma check_HT_mid_bytes' : forall sz i1 i2 lo HT r,
  check_HT' lo HT i1 r (list_repeat sz Ftyp_int8) = true ->
  (i2 < sz)%nat ->
  check_HT' lo HT (i1 + Z.of_nat i2) r (list_repeat (sz - i2) Ftyp_int8) = true.
Proof.
  induction sz; simpl; intros; auto.
  remember (Zenv.find i1 HT) as Hd. destruct_c Hd. symmetry in HeqHd.
  destruct p. destruct_c rgn_dec. destruct_c ftyp_eq_dec. subst.
  destruct i2. simpl. 
  { assert (i1 + 0 = i1) by omega. rewrite H1. rewrite HeqHd.
    destruct_c rgn_dec. destruct_c ftyp_eq_dec. }
  rewrite Nat2Z.inj_succ. rewrite <- Z.add_1_r. 
  { assert (i1 + (Z.of_nat i2 + 1) = i1 + 1 + Z.of_nat i2) by omega.
    rewrite H1. eapply IHsz; eauto. omega. }
Qed.
 
Lemma check_HT_mid_bytes : forall sz i1 i2 lo HT r,
  i1 > 0 ->
  (i2 < sz)%nat ->
  check_HT lo HT i1 r (list_repeat sz Ftyp_int8) = true ->
  check_HT lo HT (i1 + Z.of_nat i2) r (list_repeat (sz - i2) Ftyp_int8) = true.
Proof.
  intros. unfold check_HT in *. destruct_c zeq. destruct zeq; auto. subst. inv H.
  destruct zeq; auto. eapply check_HT_mid_bytes'; eauto. 
Qed.

(* ---------------------------------------------------------------------- *)

Lemma check_HT_disj' : forall t1 t2 lo HT addr r,
  check_HT' lo HT addr r (t1 ++ t2) = true ->
  check_HT' lo HT addr r t1 = true /\
  check_HT' lo HT (addr + size_ftyps lo t1) r t2 = true.
Proof.
  induction t1; simpl; intros; auto.
  split; auto. cutrewrite (addr + 0 = addr); [ | omega]. auto. 
  case_eq (Zenv.find addr HT); intros. rewrite H0 in H. destruct p. destruct_c rgn_dec; subst.
  destruct_c ftyp_eq_dec; subst.
  apply IHt1 in H. 
  assert ((addr + (size_ftyp lo f + size_ftyps lo t1)) = (addr + size_ftyp lo f + size_ftyps lo t1)). omega. 
  rewrite H1. auto.
  rewrite H0 in H. crush.
Qed.

Lemma check_HT_comb : forall t1 t2 lo HT addr r,
  check_HT' lo HT addr r t1 = true ->
  check_HT' lo HT (addr + size_ftyps lo t1) r t2 = true ->
  check_HT' lo HT addr r (t1 ++ t2) = true.
Proof.
  induction t1; simpl; intros; auto.
  cutrewrite (addr + 0 = addr) in H0; [ | omega]. auto.
  case_eq (Zenv.find addr HT); intros. rewrite H1 in H. destruct p. destruct_c rgn_dec; subst.
  destruct_c ftyp_eq_dec; subst.
  apply IHt1 with (t2 := t2) in H; auto.
  cutrewrite (addr + (size_ftyp lo f + size_ftyps lo t1) = addr + size_ftyp lo f + size_ftyps lo t1) in H0; [ | omega].
  auto.
  rewrite H1 in H. crush.
Qed.

Lemma check_HT_array'' : forall sz,
  (0 < sz)%nat ->
  forall lo HT addr r rmap tenv t,
  check_HT' lo HT addr r (sigma rmap (flatten_typ lo tenv (Typ_array t sz))) = true ->
  check_HT' lo HT addr r (sigma rmap (flatten_typ lo tenv t)) = true.
Proof.
  induction 1; intros. simpl in *. rewrite app_nil_r in H. auto.
  simpl in H0. unfold sigma in H0. rewrite map_app in H0. 
  eapply check_HT_disj' in H0. destruct H0; auto.
Qed.

Lemma check_HT_array : forall sz,
  (0 < sz)%nat ->
  forall lo HT addr r rmap tenv t,
  check_HT lo HT addr r (sigma rmap (flatten_typ lo tenv (Typ_array t sz))) = true ->
  check_HT lo HT addr r (sigma rmap (flatten_typ lo tenv t)) = true.
Proof.
  unfold check_HT; intros. destruct_c zeq.
  eapply check_HT_array''; eauto.
Qed.

Lemma check_HT_array_subset' : forall sz lo HT addr r tenv t rmap,
  check_HT' lo HT addr r (sigma rmap (flatten_typ lo tenv (Typ_array t sz))) = true ->
  check_HT' lo HT (addr + size_ftyps lo (flatten_typ lo tenv t)) r (sigma rmap (flatten_typ lo tenv (Typ_array t (sz - 1)))) = true.
Proof.
  destruct sz; simpl; intros; auto.
  unfold sigma in H. rewrite map_app in H. apply check_HT_disj' in H. destruct H. unfold sigma.
  replace (sz - 0)%nat with sz by omega. auto.
  erewrite <- size_ftyps_sigma_inv; eauto.
Qed.

Lemma check_HT_range_general' : forall t lo HT i1 r,
  i1 < Word.modulus WORDSIZE_BITS ->
  wf_HT lo HT ->
  check_HT' lo HT i1 r t = true ->
  i1 + size_ftyps lo t < Word.modulus WORDSIZE_BITS.
Proof.
  induction t; simpl; intros; auto. omega.
  replace (i1 + (size_ftyp lo a + size_ftyps lo t)) with (i1 + size_ftyp lo a + size_ftyps lo t) by omega.
  case_eq (Zenv.find i1 HT); intros.
  rewrite H2 in H1. destruct p. destruct_c rgn_dec; subst.
  destruct_c ftyp_eq_dec; subst.
  eapply IHt in H1; eauto.
  unfold wf_HT in H0. apply H0 in H2. destruct H2. intuition.
  rewrite H2 in H1. crush.
Qed.

Lemma check_HT_range_general : forall t lo HT i1 r,
  i1 > 0 ->
  i1 < Word.modulus WORDSIZE_BITS ->
  wf_HT lo HT ->
  check_HT lo HT i1 r t = true ->
  i1 + size_ftyps lo t < Word.modulus WORDSIZE_BITS.
Proof.
  unfold check_HT; intros. destruct_c zeq. omegaContradiction. 
  eapply check_HT_range_general'; eauto.
Qed.

(* ---------------------------------------------------------------------- *)
Lemma wf_val_ftyp_sub : forall t1 t2 fs lo tenv HT live v,
  ftyp_sub t1 t2 = true ->
  wf_value' fs lo tenv HT live v t1 ->
  wf_value' fs lo tenv HT live v t2.
Proof.
  induction t1; destruct t2; simpl; intros; 
    try destruct_c ftyp_eq_dec; eauto.
  { inv H0. destruct_c eq_nat_dec; subst. 
    assert (lt_31_MAX_I_BITS = l). apply proof_irr. subst. econstructor; eauto. }
  { inv H0. destruct_c eq_nat_dec; subst. 
    assert (lt_63_MAX_I_BITS = l). apply proof_irr. subst. econstructor; eauto. }
  { inv H0. destruct_c eq_nat_dec; subst. 
    assert (RT_float i0 = RT_int 31 pf0 i0). unfold RT_float. f_equal.
    apply proof_irr. rewrite Word.repr_unsigned. reflexivity. 
    rewrite <- H0. econstructor; eauto. }
  { inv H0. destruct_c eq_nat_dec; subst. 
    assert (RT_double i0 = RT_int 63 pf0 i0). unfold RT_double. f_equal.
    apply proof_irr. rewrite Word.repr_unsigned. reflexivity. 
    rewrite <- H0. econstructor; eauto. }
  { inv H0. unfold RT_ptr. destruct_c eq_nat_dec; subst. 
    assert (lt_63_MAX_I_BITS = l). apply proof_irr. subst.
    econstructor; eauto. }
  { inv H0. unfold RT_ptr. destruct_c eq_nat_dec; subst. 
    assert (lt_63_MAX_I_BITS = l). apply proof_irr. subst.
    econstructor; eauto. }
  { destruct_c rgn_dec. destruct_c zle. inv H0. econstructor; eauto.
    assert (forall n rmap, list_repeat n Ftyp_int8 = sigma rmap (list_repeat n Ftyp_int8)).
    induction n2; crush. erewrite H0. erewrite H0 in H8.
    eapply check_HT_subset_bytes; eauto.
    Grab Existential Variables.
    apply Nenv.empty.
  }
Qed.

Lemma wf_val_ftyp_sub2 : forall t1 t2 fs lo tenv HT live v rmap,
  ftyp_sub t1 t2 = true ->
  wf_value' fs lo tenv HT live v (sigma' rmap t1) ->
  wf_value' fs lo tenv HT live v (sigma' rmap t2).
Proof.
  induction t1; destruct t2; simpl; intros; 
    try destruct_c ftyp_eq_dec; eauto.
  { inv H0. destruct_c eq_nat_dec; subst. 
    assert (lt_31_MAX_I_BITS = l). apply proof_irr. subst. econstructor; eauto. }
  { inv H0. destruct_c eq_nat_dec; subst. 
    assert (lt_63_MAX_I_BITS = l). apply proof_irr. subst. econstructor; eauto. }
  { inv H0. destruct_c eq_nat_dec; subst. 
    assert (RT_float i0 = RT_int 31 pf0 i0). unfold RT_float. f_equal.
    apply proof_irr. rewrite Word.repr_unsigned. reflexivity. 
    rewrite <- H0. econstructor; eauto. }
  { inv H0. destruct_c eq_nat_dec; subst. 
    assert (RT_double i0 = RT_int 63 pf0 i0). unfold RT_double. f_equal.
    apply proof_irr. rewrite Word.repr_unsigned. reflexivity. 
    rewrite <- H0. econstructor; eauto. }
  { inv H0. unfold RT_ptr. destruct_c eq_nat_dec; subst. 
    assert (lt_63_MAX_I_BITS = l). apply proof_irr. subst.
    econstructor; eauto. }
  { inv H0. unfold RT_ptr. destruct_c eq_nat_dec; subst. 
    assert (lt_63_MAX_I_BITS = l). apply proof_irr. subst.
    econstructor; eauto. }
  { destruct_c rgn_dec. destruct_c zle. inv H0. econstructor; eauto.
    assert (forall n rmap, list_repeat n Ftyp_int8 = sigma rmap (list_repeat n Ftyp_int8)).
    induction n2; crush.
    rewrite H0 with (rmap := rmap) in H8.
    rewrite H0 with (rmap := rmap).
    eapply check_HT_subset_bytes; eauto. }
Qed.

Fixpoint weaken_val (v:rt_val) (t:ftyps) : rt_val :=
  match v, t with
    | v::vs, t::ts => v :: weaken_val vs ts
    | _, nil => nil
    | nil, _ => nil
  end.

Lemma wf_val_ftyps_weaken : forall t1 t2 fs lo tenv HT live v rmap,
  ftyps_weaken t1 t2 = true ->
  wf_value fs lo tenv HT live v (sigma rmap t1) ->
  wf_value fs lo tenv HT live (weaken_val v t2) (sigma rmap t2).
Proof.
  induction t1; simpl; intros. 
  { destruct_c t2. simpl. destruct v; simpl; auto. constructor. }
  { destruct_c t2. simpl. destruct v; simpl; auto. 
    constructor. constructor. consider (ftyp_sub a f); intros. inv H0.
    eapply IHt1 in H8; eauto. econstructor; eauto. eapply wf_val_ftyp_sub2; eauto. }
Qed.
