(* Contains definition of iLLVM, an idealized version of LLVM *)

(* Coq standard library imports *)
Require Import OrderedTypeEx.
Require Import Coq.Classes.EquivDec.
Require Import FMaps.
Require Import FSets.FMapAVL.
Require Import FSets.FMapFacts.

(* Other library imports *)
Add LoadPath "../libs".
Add LoadPath "../libs/CompCert-Toolkit".
Require Import Tactics.
Require Import Bits.
Require Import Coqlib.
Require Import Axioms.

(* Illvm imports *)
Require Import SimpleEnv.
Require Import Utility.


Definition WORDSIZE := 8.
Definition WORDSIZE_BITS := 63%nat. (* WORDSIZE in bits - 1 *)
Definition PTRTYP := int64.

(* ---------------------------------------------------------------------- *)
(* Start of abstract syntax *)

Definition lab := PTRTYP.      (* label *)
Definition id := nat.          (* identifier *)
Definition rgn := nat.         (* region *)

(* ---------------------------------------------------------------------- *)
(* Maximum width of integers in bits, this can be changed. *)
Definition MAX_I_BITS := 128%nat.
Definition MAX_I_BYTES := 16%nat.

(* Conditional operations. *)
Inductive cond : Set := 
| Cond_eq : cond
| Cond_ne : cond
| Cond_ugt : cond
| Cond_uge : cond
| Cond_ult : cond
| Cond_ule : cond
| Cond_sgt : cond
| Cond_sge : cond
| Cond_slt : cond
| Cond_sle : cond.

(* Floating-point conditional operations. *)
Inductive fcond : Set := 
| Fcond_false : fcond
| Fcond_oeq : fcond
| Fcond_ogt : fcond
| Fcond_oge : fcond
| Fcond_olt : fcond
| Fcond_ole : fcond
| Fcond_one : fcond
| Fcond_ord : fcond
| Fcond_ueq : fcond
| Fcond_ugt : fcond
| Fcond_uge : fcond
| Fcond_ult : fcond
| Fcond_ule : fcond
| Fcond_une : fcond
| Fcond_uno : fcond
| Fcond_true : fcond.

(* Binary operations. *)
Inductive binop : Set := 
| Binop_add : binop
| Binop_sub : binop
| Binop_mul : binop
| Binop_udiv : binop
| Binop_sdiv : binop
| Binop_urem : binop
| Binop_srem : binop
| Binop_shl : binop
| Binop_lshr : binop
| Binop_ashr : binop
| Binop_and : binop
| Binop_or : binop
| Binop_xor : binop.

(* Floating-point binary operations. *)
Inductive fbinop : Set :=
| Fbinop_add : fbinop
| Fbinop_sub : fbinop
| Fbinop_mul : fbinop
| Fbinop_div : fbinop 
| Fbinop_rem : fbinop.

(* To integer conversion operations. *)
Inductive iconv : Set :=
| Iconv_trunc : iconv
| Iconv_zext : iconv
| Iconv_sext : iconv
| Iconv_fptoui : iconv
| Iconv_fptosi : iconv.

(* To floating-point conversion operations. *)
Inductive fconv : Set :=
| Fconv_fptrunc : fconv
| Fconv_fpext : fconv
| Fconv_uitofp : fconv
| Fconv_sitofp : fconv.

(* iLLVM types annotated with regions. *)
Unset Elimination Schemes.
Inductive typ := 
| Typ_float : typ
| Typ_double : typ 
| Typ_int : forall sz, (sz < MAX_I_BITS)%nat -> typ
| Typ_ptr : typ -> rgn -> typ
| Typ_name : id -> list rgn -> typ
| Typ_fun : list rgn -> list typ -> option typ -> typ
| Typ_array : typ -> nat -> typ
| Typ_ptrU : nat -> rgn -> typ.
Set Elimination Schemes.

(* ---------------------------------------------------------------------- *)
(* Primitive types *)

(* Primitive types used for structural subtyping in our type system. They are
 * the same as regular types, without named types. The pointer case is not 
 * flattened to make sure our recursive types are well-founded. The function
 * case is not flattened because our induction scheme will become very 
 * complicated. We will make sure that in our type system, we flatten function
 * types. We also refer to primitive types as flat types. *)
Inductive ftyp :=
| Ftyp_float : ftyp
| Ftyp_double : ftyp 
| Ftyp_int : forall sz, (sz < MAX_I_BITS)%nat -> ftyp
| Ftyp_ptr : typ -> rgn -> ftyp
| Ftyp_fun : list rgn -> list typ -> option typ -> ftyp (* signature, return typ *)
| Ftyp_ptrU : nat -> rgn -> ftyp.
Definition ftyps := list ftyp.

Definition float_t := Word.int 31.
Definition double_t := Word.int 63.

(* iLLVM constants. *)
Unset Elimination Schemes.
Inductive const :=
| Const_null : const
| Const_nullU : const
| Const_float : float_t -> const
| Const_double : double_t -> const
| Const_int : forall sz, (sz < MAX_I_BITS)%nat -> Word.int sz -> const
| Const_fun : lab -> const
| Const_undef : ftyps -> const
| Const_baddr : lab -> lab -> const.
(* | Const_struct : list const -> const. *)
Set Elimination Schemes.

(* Operands to iLLVM instructions. *)
Inductive operand :=
| Op_reg : id -> operand
| Op_const : const -> operand.

(* Deterministic instructions. *)
Inductive insn := 
| Insn_binop : id -> binop -> operand -> operand -> insn
| Insn_fbinop : id -> fbinop -> operand -> operand -> insn
| Insn_icmp : id -> cond -> operand -> operand -> insn
| Insn_fcmp : id -> fcond -> operand -> operand -> insn
| Insn_select : id -> typ -> operand -> typ -> operand -> typ -> operand -> insn
| Insn_load : id -> typ -> operand -> insn
| Insn_store : typ -> operand -> typ -> operand -> insn 
| Insn_poolcheck : id -> rgn -> typ -> operand -> insn
| Insn_free : typ -> operand -> insn
| Insn_gep : id -> typ -> operand -> typ -> operand -> insn   (* x = aggregate* ptr, <typ> index *)
| Insn_gep1 : id -> typ -> operand -> operand -> insn
| Insn_extractvalue : id -> typ -> operand -> typ -> const -> insn 
| Insn_insertvalue : id -> typ -> operand -> typ -> operand -> const -> insn  
| Insn_iconv : id -> iconv -> typ -> operand -> typ -> insn
| Insn_fconv : id -> fconv -> typ -> operand -> typ -> insn
| Insn_bitcast : id -> typ -> operand -> typ -> insn 
| Insn_ptrtoint : id -> typ -> operand -> typ -> insn 
| Insn_inttoptr : id -> typ -> operand -> typ -> insn

| Insn_gepU : id -> typ -> operand -> operand -> insn  (* x = ptrU ptr, index *)
| Insn_poolcheckU : id -> rgn -> nat -> operand -> insn
| Insn_exit : insn. 

Inductive unsafe_opcode :=
| Opcode_unknown : id -> unsafe_opcode.

(* Non-deterministic instructions. Contains the label to go to after the instruction. *)
Inductive insn_nd :=
(* Call is basically an LLVM invoke now ... *)
| Insn_call : option id -> option typ -> operand -> list rgn -> list operand -> lab -> insn_nd
| Insn_malloc : id -> option typ -> rgn -> operand -> lab -> insn_nd
| Insn_unsafe_call : option (id * typ) -> unsafe_opcode -> list operand -> lab -> insn_nd.

(* Terminator instructions. *)
Inductive terminator := 
| Insn_return : typ -> operand -> terminator
| Insn_return_void : terminator
| Insn_br_uncond : lab -> terminator
| Insn_br : operand -> lab -> lab -> terminator
| Insn_switch : typ -> operand -> lab -> list (typ * const * lab) -> terminator
| Insn_indirect_br : typ -> operand -> list lab -> terminator
| Insn_unreachable : terminator.

(* Non-determinstic or terminator instructions *)
Inductive insn_nd_term :=
| Insn_nd : insn_nd -> insn_nd_term
| Insn_term : terminator -> insn_nd_term.

(* Phi-node. *)
Inductive phinode :=
| Insn_phi : id -> typ -> (list (operand * lab)) -> phinode.
Definition phiblock := list phinode.

(* Definition of a block. *)
Record block := mk_block {
  b_lab : lab;              (* block label *)
  b_phis : phiblock;        (* phi nodes *)
  b_insns : list insn;      (* list of instructions *)
  b_nd_term : insn_nd_term  (* nondeterministic or terminator instruction *)
}.
Definition blocks := list block.

(* Definition of an Illvm function. *)
Record function := mk_function {
  f_lab : lab;              (* function name *)
  f_params : list id;       (* function parameters *)
  f_sig : list typ;         (* function signature *)
  f_body : blocks;          (* body *)
  f_ret: option typ;        (* optional return typ *)

  (* to support regions *)
  f_prgn : list (rgn*typ);  (* polymorphic regions *)
  f_lrgn : list (rgn*typ)   (* locally allocated regions *)
}.
Definition functions := list function.

(* ---------------------------------------------------------------------- *)
Definition lab_dec := (@Word.eq_dec 63).
Definition id_dec := eq_nat_dec.
Definition rgn_dec := eq_nat_dec.

Lemma lt_0_MAX_I_BITS : (0 < MAX_I_BITS)%nat. unfold MAX_I_BITS. omega. Qed.
Lemma lt_7_MAX_I_BITS : (7 < MAX_I_BITS)%nat. unfold MAX_I_BITS. omega. Qed.
Lemma lt_15_MAX_I_BITS : (15 < MAX_I_BITS)%nat. unfold MAX_I_BITS. omega. Qed.
Lemma lt_31_MAX_I_BITS : (31 < MAX_I_BITS)%nat. unfold MAX_I_BITS. omega. Qed.
Lemma lt_63_MAX_I_BITS : (63 < MAX_I_BITS)%nat. unfold MAX_I_BITS. omega. Qed.

Definition Typ_int1 : typ := Typ_int 0 lt_0_MAX_I_BITS.
Definition Typ_int8 : typ := Typ_int 7 lt_7_MAX_I_BITS.
Definition Typ_int16 : typ := Typ_int 15 lt_15_MAX_I_BITS.
Definition Typ_int32 : typ := Typ_int 31 lt_31_MAX_I_BITS.
Definition Typ_int64 : typ := Typ_int 63 lt_63_MAX_I_BITS.

Definition Ftyp_int1 := Ftyp_int 0 lt_0_MAX_I_BITS.
Definition Ftyp_int8 := Ftyp_int 7 lt_7_MAX_I_BITS.
Definition Ftyp_int16 := Ftyp_int 15 lt_15_MAX_I_BITS.
Definition Ftyp_int32 := Ftyp_int 31 lt_31_MAX_I_BITS.
Definition Ftyp_int64 := Ftyp_int 63 lt_63_MAX_I_BITS.

(* ---------------------------------------------------------------------- *)

(* Given a label and a function table, return the corresponding function *)
Fixpoint lookup_fun (fid:lab) (fs:functions) : option function :=
  match fs with
    | List.nil => None
    | f::fs' => if lab_dec fid (f_lab f) then Some f else lookup_fun fid fs'
  end.

(* Given a label and list of basic-blocks, return the corresponding block *)
Fixpoint lookup_blk (l:lab) (bs:blocks) : option block :=
  match bs with
    | nil => None
    | b::bs' => if lab_dec (b_lab b) l then Some b else lookup_blk l bs'
  end.

(* ---------------------------------------------------------------------- *)
(* Some properties of lookup *) 

Lemma lookup_blk_spec : forall bs l b,
  lookup_blk l bs = Some b ->
  l = b_lab b.
Proof.
  induction bs; crush. destruct (lab_dec (b_lab a) l); crush.
Qed.

Lemma lookup_blk_spec2 : forall bs l b,
  lookup_blk l bs = Some b ->
  lookup_blk (b_lab b) bs = Some b.
Proof.
  intros. assert (H2 := H). apply lookup_blk_spec in H. crush.
Qed.

Lemma lookup_fun_spec : forall fs l f,
  lookup_fun l fs = Some f ->
  l = f_lab f.
Proof.
  induction fs; crush. destruct (lab_dec l (f_lab a)); crush.
Qed.

Lemma lookup_fun_spec2 : forall fs l f,
  lookup_fun l fs = Some f ->
  lookup_fun (f_lab f) fs = Some f.
Proof.
  intros. assert (H2 := H). apply lookup_fun_spec in H. crush.
Qed.

(* ---------------------------------------------------------------------- *)
(* Forall in Type instead of Prop *)
Inductive ForallT {A : Type} (P : A -> Type) : list A -> Type :=
| ForallT_nil : ForallT P nil
| ForallT_cons : forall (x : A) (l : list A),
  P x -> ForallT P l -> ForallT P (x :: l).

(* A stronger induction scheme for const. *)
Section const_rect.
  Variable P : const -> Type.
  Variable Null_case : P (Const_null).
  Variable NullU_case : P (Const_nullU).
  Variable Float_case : forall f, P (Const_float f).
  Variable Double_case : forall d, P (Const_double d).
  Variable Int_case : forall sz pf (i:Word.int sz), P (Const_int sz pf i).
  Variable Fun_case : forall f, P (Const_fun f).
  Variable Undef_case : forall t, P (Const_undef t).
  Variable Baddr_case : forall l1 l2, P (Const_baddr l1 l2).
  (* Variable Global_case : forall x r, P (Const_global x r). *)
  (* Variable Struct_case : forall ls, ForallT P ls -> P (Const_struct ls). *)

  Fixpoint const_rect (c:const) : P c :=
    match c with
      | Const_null => Null_case
      | Const_nullU => NullU_case
      | Const_float f => Float_case f
      | Const_double d => Double_case d
      | Const_int sz pf i => Int_case sz pf i
      | Const_fun f => Fun_case f
      | Const_undef t => Undef_case t
      | Const_baddr l1 l2 => Baddr_case l1 l2
      (* | Const_global x r => Global_case x r *)
      (* | Const_struct ls => Struct_case ls
        ((fix f ls :=
          match ls return (ForallT P ls) with
            | nil => @ForallT_nil const P
            | c'::ls' => @ForallT_cons const P c' ls' (const_rect c') (f ls')
          end) ls) *)
    end.
End const_rect.
Definition const_ind (P:const->Prop) := const_rect P.
Definition const_rec (P:const->Set) := const_rect P.

(* A stronger induction scheme for typ. *)
Section typ_rect.
  Variable P : typ -> Type.
  Hypothesis Float_case : P Typ_float.
  Hypothesis Double_case : P Typ_double.
  Hypothesis Int_case : forall sz pf, P (Typ_int sz pf).
  Hypothesis Ptr_case : forall (t : typ) (r:rgn), P t -> P (Typ_ptr t r).
  Hypothesis Name_case : forall (x:id) (lr:list rgn), P (Typ_name x lr).
  Hypothesis Fun_case : forall (lr : list rgn) (ls : list typ) (t : option typ), 
    ForallT P ls -> 
    match t with
      | Some t' => P t'
      | None => True
    end ->
    P (Typ_fun lr ls t).
  Hypothesis Array_case : forall (t : typ) (sz : nat), P t -> P (Typ_array t sz).
  Hypothesis PtrU_case : forall (sz:nat) (r:rgn), P (Typ_ptrU sz r).

  Fixpoint typ_rect (t:typ) : P t :=
    match t return P t with
      | Typ_float => Float_case
      | Typ_double => Double_case
      | Typ_int sz pf => Int_case sz pf
      | Typ_ptr t' r => Ptr_case t' r (typ_rect t')
      | Typ_name x lr => Name_case x lr
      | Typ_fun lr ls t => Fun_case lr ls t
        ((fix f (ls : list typ) :=
          match ls return (ForallT P ls) with
            | nil => @ForallT_nil typ P
            | t'::ls' => @ForallT_cons typ P t' ls' (typ_rect t') (f ls')
          end) ls) (match t return (match t return Type with
                                      | Some t' => P t'
                                      | None => True
                                    end) with
                      | Some t' => typ_rect t'
                      | None => I
                    end)
      | Typ_array t' n => Array_case t' n (typ_rect t')
      | Typ_ptrU sz r => PtrU_case sz r
    end.  
End typ_rect.
Definition typ_ind (P:typ->Prop) := typ_rect P.
Definition typ_rec (P:typ->Set) := typ_rect P.

Lemma ForallT_ls_dec : forall A ls1 ls2,
  ForallT (fun t1 : A => forall t2 : A, {t1 = t2} + {t1 <> t2}) ls1 ->
  {ls1 = ls2} + {ls1 <> ls2}.
Proof.
  induction ls1; destruct ls2; intros; try_both.
  inv X. apply IHls1 with (ls2 := ls2) in X1. 
  specialize (X0 a0). destruct X0; destruct X1; subst; try_both.
Qed.

Lemma typ_eq_dec : forall (t1 t2:typ), {t1 = t2} + {t1 <> t2}.
  induction t1; destruct t2; try_both.
  { destruct (eq_nat_dec sz sz0); subst. left. f_equal. apply proof_irr. right. crush. }
  { specialize (IHt1 t2). destruct IHt1; destruct (rgn_dec r r0); subst; try_both. }
  { destruct (id_dec x i); destruct (list_eqdec id_dec lr l); subst; try_both. }
  { apply ForallT_ls_dec with (ls2 := l0) in X; auto.
    destruct (list_eqdec rgn_dec lr l); destruct X; try_both.
    destruct t; destruct o; subst; try_both.
    specialize (X0 t0). destruct X0; try_both. }
  { specialize (IHt1 t2). destruct IHt1; destruct (eq_nat_dec n sz); subst; try_both. }
  { destruct (eq_nat_dec sz n); destruct (rgn_dec r r0); subst; try_both. }
Qed.

Lemma ftyp_eq_dec : forall (t1 t2:ftyp), {t1 = t2} + {t1 <> t2}.
Proof.
  induction t1; destruct t2; try_both.
  { destruct (eq_nat_dec sz sz0); subst. left. f_equal. apply proof_irr. right. crush. }
  { destruct (typ_eq_dec t t0); destruct (rgn_dec r r0); subst; try_both. }
  { destruct (list_eqdec rgn_dec l l1); destruct (list_eqdec typ_eq_dec l0 l2); subst; try_both.
    destruct o; destruct o0; subst; try_both.
    destruct (typ_eq_dec t t0); subst; try_both. }
  { destruct (eq_nat_dec n n0); destruct (rgn_dec r r0); subst; try_both. }
Qed.
