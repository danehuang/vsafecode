(* Standard library imports *)
Require Import ZArith.Zbool.

(* Other library imports *)
Add LoadPath "../libs".
Add LoadPath "../libs/CompCert-Toolkit".
Require Import Tactics.
Require Import Bits.
Require Import Coqlib.

(* Illvm imports *)
Require Import Utility.
Require Import IllvmAST.
Require Import IllvmValues.
Require Import TargetData.
Require Import Amem.
Require Import Cmem.


(* ---------------------------------------------------------------------- *)
(** * Abstract Machine Definitions *)
(* ---------------------------------------------------------------------- *)

(* Execution context (i.e. stack frame) , note no allocas! *)
Record exec_ctxt : Type := mk_ec {
  ec_fun : function;         (* current function *)
  ec_blk : block;            (* current block (part of function) *)
  ec_insns : list insn;      (* current instructions (part of block) *)
  ec_term : insn_nd_term;    (* current terminator (part of block) *)
  ec_env : Nenv.t rt_val;    (* current environement *)

  ec_HT : heap_t;            (* heap typing *)
  ec_rmap_e : Nenv.t rgn;    (* return region map: syn_region -> sem_region *)
  ec_rmap_b : Nenv.t rgn;    (* body region map: syn_region -> sem_region *)
  ec_rgns : list rgn;        (* local regions *)
  ec_live : list rgn         (* live regions *)
}.

(* Machine state *)
Record mstate := mk_mstate {
  s_mem : SVAmem.cmem;       (* memory (modeling the heap) *)
  s_cec : exec_ctxt;         (* current execution context *)
  s_stk : list exec_ctxt     (* rest of stack *)
}.

(* Machine configuration (the stuff that doesn't change during computation) *)
Record config := mk_config {
  c_fs : functions;   (* function table *)
  c_lo : layout;      (* architecture's data layout *)
  c_tenv : tenv_t     (* top-level type environment *)
}.

(* The result of evaluating a basic block. *)
Inductive comp :=
| EvalErr : comp             (* bad error *)
| Ret : comp                 (* sweet, sva caught an error *)
| Delay : mstate -> comp.    (* resulting machine state *)
Hint Constructors comp.

Inductive load_comp :=
| Load_SvaErr : load_comp    (* sweet, sva caught an error *)
| Load_MemErr : load_comp    (* bad error *)
| Load_Val : rt_val -> load_comp.
Hint Constructors load_comp.

Inductive store_comp :=
| Store_SvaErr : store_comp  (* sweet, sva caught an error *)
| Store_MemErr : store_comp  (* bad error *)
| Store_Val : SVAmem.cmem -> store_comp.
Hint Constructors store_comp.

(* ---------------------------------------------------------------------- *)
(** * Evaluation helper functions *)
(* ---------------------------------------------------------------------- *)

Definition cast (n m:nat) (pf: n = m) : Word.int n -> Word.int m :=
  match pf with
    | eq_refl => fun x => x
  end.

Section HELPER_FUNCS.

  Variable env : Nenv.t rt_val.
  Variable globs : Nenv.t (PTRTYP*typ*rgn).

  (* Evaluate a binary operation  *)
  Definition eval_binop (b:binop) (o1 o2:operand) : option rt_val :=
    match op2rtv o1 env, op2rtv o2 env with
      | Some (RT_int n1 pf1 i1 :: nil), Some (RT_int n2 pf2 i2 :: nil) => 
        match eq_nat_dec n2 n1 with
          | left pf =>
            match b with
              | Binop_add => Some (RT_int n1 pf1 (Word.add i1 (cast n2 n1 pf i2) ) :: nil)
              | Binop_sub => Some (RT_int n1 pf1 (Word.sub i1 (cast n2 n1 pf i2) ) :: nil)
              | Binop_mul => Some (RT_int n1 pf1 (Word.mul i1 (cast n2 n1 pf i2) ) :: nil)
              | Binop_udiv => Some (RT_int n1 pf1 (Word.divu i1 (cast n2 n1 pf i2) ) :: nil)
              | Binop_sdiv => Some (RT_int n1 pf1 (Word.divs i1 (cast n2 n1 pf i2) ) :: nil)
              | Binop_urem => Some (RT_int n1 pf1 (Word.modu i1 (cast n2 n1 pf i2) ) :: nil)
              | Binop_srem => Some (RT_int n1 pf1 (Word.mods i1 (cast n2 n1 pf i2) ) :: nil)
              | Binop_shl => Some (RT_int n1 pf1 (Word.shl i1 (cast n2 n1 pf i2) ) :: nil)
              | Binop_lshr => Some (RT_int n1 pf1 (Word.shrx i1 (cast n2 n1 pf i2) ) :: nil)
              | Binop_ashr => Some (RT_int n1 pf1 (Word.shr i1 (cast n2 n1 pf i2) ) :: nil)
              | Binop_and => Some (RT_int n1 pf1 (Word.and i1 (cast n2 n1 pf i2) ) :: nil)
              | Binop_or => Some (RT_int n1 pf1 (Word.or i1 (cast n2 n1 pf i2) ) :: nil)
              | Binop_xor => Some (RT_int n1 pf1 (Word.xor i1 (cast n2 n1 pf i2) ) :: nil)
            end
          | right _ => None
        end
      | _, _ => None
    end.

  Definition float_cast {sz:nat} (f:Word.int sz) : float_t := Word.repr (Word.unsigned f).
  Definition double_cast {sz:nat} (f:Word.int sz) : double_t := Word.repr (Word.unsigned f).
  Axiom float_fbinop_magic : forall (fb:fbinop) (f1 f2:float_t), float_t.
  Axiom double_fbinop_magic : forall (fb:fbinop) (d1 d2:double_t), double_t.

  Definition eval_fbinop (f:fbinop) (o1 o2:operand) : option rt_val :=
    match op2rtv o1 env, op2rtv o2 env with
      | Some (RT_int sz1 _ f1 :: nil), Some (RT_int _ _ f2 :: nil) =>
        if eq_nat_dec sz1 31 then
          Some (RT_float (float_fbinop_magic f (float_cast f1) (float_cast f2)) :: nil)
          else
            Some (RT_double (double_fbinop_magic f (double_cast f1) (double_cast f2)) :: nil)
      | _, _ => None
    end.

  Definition b2i (b:bool) : Word.int 0 :=
    if b then Word.one else Word.zero.

  (* Evaluate an integer comparison *)
  Definition eval_icmp (c:cond) (o1 o2:operand) : option rt_val :=
    match op2rtv o1 env, op2rtv o2 env with
      | Some (RT_int n1 pf1 i1 :: nil), Some (RT_int n2 pf2 i2 :: nil) => 
        match eq_nat_dec n2 n1 with
          | left pf => 
            match c with
              | Cond_eq => Some (RT_int 0 lt_0_MAX_I_BITS (b2i (Word.cmp Word.Ceq i1 (cast n2 n1 pf i2))) :: nil)
              | Cond_ne => Some (RT_int 0 lt_0_MAX_I_BITS (b2i (Word.cmp Word.Cne i1 (cast n2 n1 pf i2))) :: nil)
              | Cond_ugt => Some (RT_int 0 lt_0_MAX_I_BITS (b2i (Word.cmpu Word.Cgt i1 (cast n2 n1 pf i2))) :: nil)
              | Cond_uge => Some (RT_int 0 lt_0_MAX_I_BITS (b2i (Word.cmpu Word.Cge i1 (cast n2 n1 pf i2))) :: nil)
              | Cond_ult => Some (RT_int 0 lt_0_MAX_I_BITS (b2i (Word.cmpu Word.Clt i1 (cast n2 n1 pf i2))) :: nil)
              | Cond_ule => Some (RT_int 0 lt_0_MAX_I_BITS (b2i (Word.cmpu Word.Cle i1 (cast n2 n1 pf i2))) :: nil)
              | Cond_sgt => Some (RT_int 0 lt_0_MAX_I_BITS (b2i (Word.cmp Word.Cgt i1 (cast n2 n1 pf i2))) :: nil)
              | Cond_sge => Some (RT_int 0 lt_0_MAX_I_BITS (b2i (Word.cmp Word.Cge i1 (cast n2 n1 pf i2))) :: nil)
              | Cond_slt => Some (RT_int 0 lt_0_MAX_I_BITS (b2i (Word.cmp Word.Clt i1 (cast n2 n1 pf i2))) :: nil)
              | Cond_sle => Some (RT_int 0 lt_0_MAX_I_BITS (b2i (Word.cmp Word.Cle i1 (cast n2 n1 pf i2))) :: nil)
            end
          | right _ => None
        end
      | _, _ => None
    end.

  (* Floating point as Z should respect order *)
  (*
  Definition ordered_fcmp (c:fcond) (f1 f2:binary64) : option rt_val :=
    match f1, f2 with
      | _, B754_nan => Some (RT_int 0 lt_0_MAX_I_BITS (b2i false) :: nil)
      | B754_nan, _ => Some (RT_int 0 lt_0_MAX_I_BITS (b2i false) :: nil)
      | _, _ => match c with 
                  | Fcond_oeq => Some (RT_int 0 lt_0_MAX_I_BITS (b2i (Z.eqb (bits_of_b64 f1) (bits_of_b64 f2))) :: nil)
                  | Fcond_ogt => Some (RT_int 0 lt_0_MAX_I_BITS (b2i (Z.leb (bits_of_b64 f2) (bits_of_b64 f1))) :: nil)
                  | Fcond_oge => Some (RT_int 0 lt_0_MAX_I_BITS (b2i (Z.ltb (bits_of_b64 f2) (bits_of_b64 f1))) :: nil)
                  | Fcond_olt => Some (RT_int 0 lt_0_MAX_I_BITS (b2i (Z.ltb (bits_of_b64 f1) (bits_of_b64 f2))) :: nil)
                  | Fcond_ole => Some (RT_int 0 lt_0_MAX_I_BITS (b2i (Z.leb (bits_of_b64 f1) (bits_of_b64 f2))) :: nil)
                  | Fcond_one => Some (RT_int 0 lt_0_MAX_I_BITS (b2i (negb (Z.eqb (bits_of_b64 f1) (bits_of_b64 f2)))) :: nil)
                  | Fcond_ord => Some (RT_int 0 lt_0_MAX_I_BITS (b2i true) :: nil)
                  | _ => Some (RT_int 0 lt_0_MAX_I_BITS (b2i false) :: nil)
                end
    end.
  *)

  (* Floating point as Z should respect order *)
  (*
  Definition unordered_fcmp (c:fcond) (f1 f2:binary64) : option rt_val :=
    match f1, f2 with
      | _, B754_nan => Some (RT_int 0 lt_0_MAX_I_BITS (b2i true) :: nil)
      | B754_nan, _ => Some (RT_int 0 lt_0_MAX_I_BITS (b2i true) :: nil)
      | _, _ => match c with 
                  | Fcond_ueq => Some (RT_int 0 lt_0_MAX_I_BITS (b2i (Z.eqb (bits_of_b64 f1) (bits_of_b64 f2))) :: nil)
                  | Fcond_ugt => Some (RT_int 0 lt_0_MAX_I_BITS (b2i (Z.leb (bits_of_b64 f2) (bits_of_b64 f1))) :: nil)
                  | Fcond_uge => Some (RT_int 0 lt_0_MAX_I_BITS (b2i (Z.ltb (bits_of_b64 f2) (bits_of_b64 f1))) :: nil)
                  | Fcond_ult => Some (RT_int 0 lt_0_MAX_I_BITS (b2i (Z.ltb (bits_of_b64 f1) (bits_of_b64 f2))) :: nil)
                  | Fcond_ule => Some (RT_int 0 lt_0_MAX_I_BITS (b2i (Z.leb (bits_of_b64 f1) (bits_of_b64 f2))) :: nil)
                  | Fcond_une => Some (RT_int 0 lt_0_MAX_I_BITS (b2i (negb (Z.eqb (bits_of_b64 f1) (bits_of_b64 f2)))) :: nil)
                  | Fcond_uno => Some (RT_int 0 lt_0_MAX_I_BITS (b2i true) :: nil)
                  | _ => Some (RT_int 0 lt_0_MAX_I_BITS (b2i false) :: nil)
                end
    end.
  *)

  Axiom float_fcmp_magic : forall (fc:fcond) (f1 f2:float_t), Word.int 0.
  Axiom double_fcmp_magic : forall (fc:fcond) (d1 d2:double_t), Word.int 0.

  Definition eval_fcmp (c:fcond) (o1 o2:operand) : option rt_val :=
    (* let b2i := (fun (b:bool) => if b then Word.one else Word.zero) in *)
    match op2rtv o1 env, op2rtv o2 env with
      | Some (RT_int sz1 _ f1 :: nil), Some (RT_int sz2 _ f2 :: nil) =>
        if eq_nat_dec sz1 31 then
          Some (RT_int 0 lt_0_MAX_I_BITS (float_fcmp_magic c (float_cast f1) (float_cast f2)) :: nil)
          else
            Some (RT_int 0 lt_0_MAX_I_BITS (double_fcmp_magic c (double_cast f1) (double_cast f2)) :: nil)
      | _, _ => None
    end.

  Definition eval_iconv (c:iconv) (o:operand) (t:typ) : option rt_val :=
    match op2rtv o env, t with
      | Some (RT_int sz1 pf1 i :: nil), Typ_int sz2 pf2 =>
        match c with
          | Iconv_trunc => Some (RT_int sz2 pf2 (Word.repr (Word.unsigned i)) :: nil)
          | Iconv_zext =>
            let n := Z.of_nat (sz2 - sz1) in
              Some (RT_int sz2 pf2 (Word.zero_ext _ n (Word.repr (Word.unsigned i))) :: nil)
          | Iconv_sext =>
            let n := Z.of_nat (sz2 - sz1) in
              Some (RT_int sz2 pf2 (Word.sign_ext _ n (Word.repr (Word.unsigned i))) :: nil)
          | Iconv_fptoui => 
            Some (RT_int sz2 pf2 (Word.repr (Word.unsigned i)) :: nil)
          | Iconv_fptosi => 
            Some (RT_int sz2 pf2 (Word.repr (Word.signed i)) :: nil)
        end
      | _, _ => None
    end.

  Definition eval_fconv (c:fconv) (o:operand) (t:typ) : option rt_val :=
    match op2rtv o env, t with
      | Some (RT_int sz pf i :: nil), Typ_float =>
        match c with
          | Fconv_fptrunc => Some (RT_float (float_cast i) :: nil)
          | Fconv_fpext => Some (RT_float (float_cast i) :: nil)
          | Fconv_uitofp => Some (RT_float (float_cast i) :: nil)
          | Fconv_sitofp => Some (RT_float (float_cast i) :: nil)
        end
      | Some (RT_int sz pf i :: nil), Typ_double =>
        match c with
          | Fconv_fptrunc => Some (RT_double (double_cast i) :: nil)
          | Fconv_fpext => Some (RT_double (double_cast i) :: nil)
          | Fconv_uitofp => Some (RT_double (double_cast i) :: nil)
          | Fconv_sitofp => Some (RT_double (double_cast i) :: nil)
        end
      | _, _ => None
    end.

  Section MEM_HELPER_FUNCS.

    Variable m : SVAmem.cmem.
    Variable fs : functions.
    Variable lo : layout.
    Variable tenv : tenv_t.
    Variable live : list rgn.
    Variable rmap : Nenv.t rgn.

    Definition eval_select (t:typ) (cond o1 o2:operand) :=
    match op2rtv cond env, op2rtv o1 env, op2rtv o2 env with
      | Some (RT_int sz pf i :: nil), Some v1, Some v2 =>
        if Word.eq i Word.zero then 
          Some (weaken_val v1 (flatten_typ lo tenv t)) 
        else 
          Some (weaken_val v2 (flatten_typ lo tenv t))
      | _, _, _ => None
    end. 

    Fixpoint load_helper (n:Z) (t:ftyps) : option rt_val :=
      match t with
        | nil => Some nil
        | t'::ts =>
          match load_helper (n + size_ftyp lo t') ts with
            | Some vs =>
              match SVAmem.load m lo n t' with
                | Some v => Some (v::vs)
                | None => None
              end
            | None => None
          end
      end.

    (* Evaluate a load from either a typed or untyped pointer. *)
    Definition eval_load (t:typ) (o:operand) : load_comp :=
      match t with
        | Typ_ptr t' r' =>
          match op2ptr o env with
            | Some addr =>
              if zeq (Word.unsigned addr) 0 then Load_SvaErr
                else
                  match load_helper (Word.unsigned addr) (flatten_typ lo tenv (sigma'' rmap t')) with
                    | Some rt => Load_Val rt
                    | None => Load_MemErr (* type system should prevent this *)
                  end
            | None => Load_MemErr (* type system should guarantee pointer *)
          end
        | Typ_ptrU 1 r =>
          match op2ptr o env with
            | Some addr =>
              if zeq (Word.unsigned addr) 0 then Load_SvaErr
                else
                  let ts := (Ftyp_int8 :: nil) in
                  match load_helper (Word.unsigned addr) ts with
                    | Some rt => Load_Val rt
                    | None => Load_MemErr
                  end
            | None => Load_SvaErr
          end
        | Typ_ptrU 2 r =>
          match op2ptr o env with
            | Some addr =>
              if zeq (Word.unsigned addr) 0 then Load_SvaErr
                else
                  let ts := (list_repeat (size_ftyp_nat lo Ftyp_int16) Ftyp_int8) in
                  match load_helper (Word.unsigned addr) ts with
                    | Some rt => Load_Val (bytestoint16 lo rt)
                    | None => Load_MemErr
                  end
            | None => Load_SvaErr
          end
        | Typ_ptrU 4 r =>
          match op2ptr o env with
            | Some addr =>
              if zeq (Word.unsigned addr) 0 then Load_SvaErr
                else
                  let ts := (list_repeat (size_ftyp_nat lo Ftyp_int32) Ftyp_int8) in
                  match load_helper (Word.unsigned addr) ts with
                    | Some rt => Load_Val (bytestoint lo rt)
                    | None => Load_MemErr
                  end
            | None => Load_SvaErr
          end
        | Typ_ptrU 8 r =>
          match op2ptr o env with
            | Some addr =>
              if zeq (Word.unsigned addr) 0 then Load_SvaErr
                else
                  let ts := (list_repeat (size_ftyp_nat lo Ftyp_int64) Ftyp_int8) in
                  match load_helper (Word.unsigned addr) ts with
                    | Some rt => Load_Val (bytestoint64 lo rt)
                    | None => Load_MemErr
                  end
            | None => Load_SvaErr
          end
        | _ => Load_MemErr
      end.

    Fixpoint store_helper (n:Z) (t:ftyps) (v:rt_val) : option SVAmem.cmem :=
      match t, v with
        | nil, nil => Some m
        | t'::ts, v'::vs =>
          match store_helper (n + size_ftyp lo t') ts vs with
            | Some m' => SVAmem.store m' lo n t' v'
        | None => None
          end
        | _, _ => None
      end.

    Fixpoint weaken_typ (t1 t2:ftyps) : ftyps :=
      match t1, t2 with
        | t1::ts1, t2::ts2 => t2 :: weaken_typ ts1 ts2
        | nil, _ => nil
        | _, nil => nil
      end.

    (* Evaluate a store to either a typed or untyped pointer. *)
    Definition eval_store (t1 t2:typ) (o1 o2:operand) : store_comp :=
      match t2 with
        | Typ_ptr t' r' =>
          match op2rtv o1 env, op2ptr o2 env with
            | Some rt, Some addr =>
              if zeq (Word.unsigned addr) 0 then Store_SvaErr
                else
                  let ts1 := flatten_typ lo tenv (sigma'' rmap t1) in
                  let ts2 := flatten_typ lo tenv (sigma'' rmap t') in
                    match store_helper (Word.unsigned addr) (weaken_typ ts1 ts2) rt with
                      | Some mem' => Store_Val mem'
                      | None => Store_MemErr (* type system should prevent this *)
                    end
            | _, _ => Store_MemErr (* type system should guarantee pointer *)
          end
        | Typ_ptrU _ r =>
          match op2rtv o1 env, op2ptr o2 env with
            | Some rt, Some addr =>
              if zeq (Word.unsigned addr) 0 then Store_SvaErr
                else
                  let rt' := anytobytes lo rt in
                  let ts := list_repeat (length rt') Ftyp_int8 in
                    match store_helper (Word.unsigned addr) ts rt' with
                      | Some mem' => Store_Val mem'
                      | None => Store_MemErr
                    end
            | _, _ => Store_MemErr (* type system should guarantee pointer *)
          end
        | _ => Store_MemErr
      end.

    (* Evaluate a poolcheck, check that o is in region r at typ t. *)
    Definition eval_poolcheck (HT:heap_t) (r:rgn) (t:typ) (o:operand) : option rt_val :=
      match op2rtv o env with
        (*
        | Some (RT_ptr addr :: nil) =>
          if check_HT lo HT (Word.unsigned addr) (alpha rmap r) (flatten_typ lo tenv (sigma'' rmap t))
            then Some (RT_ptr addr :: nil) 
            else None
        *)
        | Some (RT_int sz pf addr :: nil) =>
          if check_HT lo HT (Word.unsigned addr) (alpha rmap r) (flatten_typ lo tenv (sigma'' rmap t))
            then Some (RT_ptr (Word.repr (Word.unsigned addr)) :: nil)
            else None
        | _ => None
      end.
    
    (* Casts an integer to a pointer into either a typed or untyped region. *)
    Definition eval_inttoptr (HT:heap_t) (o:operand) (t2:typ) : load_comp :=
      match t2 with
        | Typ_ptr t3 r3 =>
          match op2rtv o env with
            | Some (RT_int sz _ i :: nil) => 
              match eq_nat_dec sz WORDSIZE_BITS with
                | left pf =>  
                  if in_dec rgn_dec (alpha rmap r3) live then
                    if check_HT lo HT (Word.unsigned i) (alpha rmap r3) (flatten_typ lo tenv (sigma'' rmap t3))
                      then Load_Val (RT_ptr (cast sz WORDSIZE_BITS pf i) :: nil)
                      else Load_SvaErr
                    else Load_SvaErr
                | right _ => Load_MemErr
              end
            | _ => Load_MemErr
          end
        | Typ_ptrU sz r3 =>
          match op2rtv o env with
            | Some (RT_int sz' _ i :: nil) =>
              match eq_nat_dec sz' WORDSIZE_BITS with
                | left pf =>
                  if in_dec rgn_dec (alpha rmap r3) live then
                    let ts := list_repeat sz Ftyp_int8 in
                    if check_HT lo HT (Word.unsigned i) (alpha rmap r3) (sigma rmap ts)
                      then Load_Val (RT_ptr (cast sz' WORDSIZE_BITS pf i) :: nil)
                      else Load_SvaErr
                    else Load_SvaErr
                | right _ => Load_MemErr
              end
            | _ => Load_MemErr
          end
        | _ => Load_MemErr
      end.

    Definition eval_bitcast (t1 t2:typ) (o:operand) : option rt_val :=
      match t1, t2 with
        | Typ_ptr _ r1, Typ_ptr _ r2 =>
          match op2rtv o env with
            | Some (RT_int _ _ addr :: nil) => Some (RT_ptr (Word.repr (Word.unsigned addr)) :: nil)
            | _ => None
          end
        | Typ_ptrU sz1 r1, Typ_ptrU sz2 r2 =>
          match op2rtv o env with
            | Some (RT_int _ _ addr :: nil) => Some (RT_ptr (Word.repr (Word.unsigned addr)) :: nil)
            | _ => None
          end
        | _, _ => None
      end.

    (* Malloc with finite memory *)
    Definition eval_malloc (HT:heap_t) (r:rgn) (t:option typ) (o:operand) : option (rt_val*SVAmem.cmem) :=
      match op2rtv o env with
        | Some (RT_int sz _ i :: nil) =>
          match t with
            | Some t =>
              match SVAmem.alloc m lo live HT (sigma rmap (flatten_typ lo tenv t)) (nat_of_Z (Word.unsigned i)) (alpha rmap r) with
                | Some (addr, m') => Some (RT_ptr addr :: nil, m')
                | None => None
              end
            | None =>
              match SVAmem.alloc m lo live HT (sigma rmap (list_repeat (nat_of_Z (Word.unsigned i)) Ftyp_int8)) 1 (alpha rmap r) with
                | Some (addr, m') => Some (RT_ptr addr :: nil, m')
                | None => None
              end
          end
        | _ => None
      end.

    (* Calls free *)  
    Definition eval_free (o:operand) : option SVAmem.cmem :=
      match op2rtv o env with
        (* | Some (RT_ptr addr :: nil) => SVAmem.free m lo (Word.unsigned addr) *)
        | Some (RT_int _ _ i :: nil) => SVAmem.free m lo (Word.unsigned i)
        | _ => None
      end.

    (* Evaluate a gep into a named type (i.e. struct) *)        
    Definition eval_gep (o1 o2:operand) (t1 t2:typ) : load_comp :=
      match t1 with 
        | Typ_ptr t r =>
          match t with
            | Typ_name _ _ =>
              match op2ptr o1 env, o2 with
                | Some addr, Op_const (Const_int sz pf i) => 
                  if zle (Word.unsigned addr) 0 then Load_SvaErr else
                  let ts := (flatten_typ lo tenv t) in
                    Load_Val (RT_ptr (Word.repr ((Word.unsigned addr) + walk_offset lo (walk_offset3 lo tenv (nat_of_Z (Word.unsigned i)) t) ts)) :: nil)
                | Some addr, Op_reg x =>
                  match op2rtv (Op_reg x ) env with
                    | Some (RT_int sz pf i :: nil) => 
                      if zle (Word.unsigned addr) 0 then Load_SvaErr else
                      let ts := (flatten_typ lo tenv t) in
                      let n := walk_offset3 lo tenv (nat_of_Z (Word.unsigned i)) t in
                      let ts' := (flatten_typ lo tenv t2) in
                        if lt_dec n (length ts) then
                          if ftyps_subset ts' (skipn n ts) then
                            Load_Val (RT_ptr (Word.repr ((Word.unsigned addr) + walk_offset lo (walk_offset3 lo tenv (nat_of_Z (Word.unsigned i)) t) ts)) :: nil)
                            else Load_SvaErr
                          else Load_SvaErr
                    | _ => Load_MemErr
                  end
                | _, _ => Load_MemErr
              end
            | Typ_array t sz =>
              match op2rtv o1 env, o2 with
                | Some (RT_int _ _ addr :: nil), Op_const (Const_int _ _ i) =>
                  if zeq (Word.unsigned addr) 0 then Load_SvaErr else
                    let ts := flatten_typ lo tenv t in
                    let addr' := (Word.unsigned addr + array_offset lo ts (nat_of_Z (Word.unsigned i))) mod Word.modulus WORDSIZE_BITS in
                    Load_Val (RT_ptr (Word.repr addr') :: nil)
                | Some (RT_int _ _ addr :: nil), Op_reg x2 =>
                  match op2rtv (Op_reg x2) env with
                    | Some (RT_int sz pf i :: nil) =>
                      if zeq (Word.unsigned addr) 0 then Load_SvaErr else
                        let ts := flatten_typ lo tenv t in
                        let addr' := (Word.unsigned addr + array_offset lo ts (nat_of_Z (Word.unsigned i))) mod Word.modulus WORDSIZE_BITS in
                        Load_Val (RT_int WORDSIZE_BITS lt_63_MAX_I_BITS (Word.repr addr') :: nil)
                    | _ => Load_MemErr
                  end
                | _, _ => Load_MemErr
              end
            | _ => Load_MemErr
          end
        | _ => Load_MemErr
      end.

    (* Evaluate a pointer-based gep, i.e. a shallow indexing. *)
    Definition eval_gep1 (o1 o2:operand) (t1:typ) : load_comp :=
      match t1 with
        | Typ_int sz pf =>
          match op2rtv o1 env, op2rtv o2 env with
            | Some (RT_int _ _ addr :: nil), Some (RT_int _ _ i :: nil) =>
              let addr' := (Word.unsigned addr + 8 * Word.unsigned i) mod Word.modulus WORDSIZE_BITS in
              Load_Val (RT_int WORDSIZE_BITS lt_63_MAX_I_BITS (Word.repr addr') :: nil)
            | _, _ => Load_MemErr
          end
        | Typ_ptr t r =>
          match op2rtv o1 env, op2rtv o2 env with
            | Some (RT_int _ _ addr :: nil), Some (RT_int _ _ i :: nil) =>
              let ts := flatten_typ lo tenv t in
              let addr' := (Word.unsigned addr + (size_ftyps lo ts) * Word.unsigned i) mod Word.modulus WORDSIZE_BITS in
              Load_Val (RT_int WORDSIZE_BITS lt_63_MAX_I_BITS (Word.repr addr') :: nil)
            | _, _ => Load_MemErr
          end
        | _ => Load_MemErr
      end.

    (* Evaluate a gep in an unknown region. *)
    Definition eval_gepU (o1 o2:operand) (t:typ) : load_comp :=
      match t with
        | Typ_int sz pf =>
          match op2rtv o1 env, op2rtv o2 env with
            | Some (RT_int _ _ addr :: nil), Some (RT_int _ pf i :: nil) =>
              let addr' := (Word.unsigned addr + Word.unsigned i) mod Word.modulus WORDSIZE_BITS in
                if zle (Word.unsigned addr) 0 then Load_SvaErr else
                  Load_Val (RT_ptr (Word.repr addr') :: nil)
            | _, _ => Load_MemErr
          end
        | Typ_ptrU sz r =>
          match op2rtv o1 env, op2rtv o2 env with
            | Some (RT_int _ _ addr :: nil), Some (RT_int _ pf i :: nil) =>
              let addr' := (Word.unsigned addr + Word.unsigned i) mod Word.modulus WORDSIZE_BITS in
                if zle (Word.unsigned addr) 0 then Load_SvaErr else
                  Load_Val (RT_ptr (Word.repr addr') :: nil)
            | _, _ => Load_MemErr
          end
        | _ => Load_MemErr
      end.

    Definition eval_insertvalue (o1 o2:operand) (c:const) : load_comp :=
      match op2rtv o1 env, op2rtv o2 env, c with
        | Some vs, Some v, Const_int _ _ i =>
          let n := Z.to_nat (Word.unsigned i) in
          Load_Val (firstn n vs ++ v ++ skipn (n + length v) vs)
        | _, _, _ => Load_MemErr
      end.

    Definition eval_extractvalue (o:operand) (t:typ) (c:const) : load_comp :=
      match op2rtv o env, c with
        | Some v, Const_int _ _ i => 
          let ft := flatten_typ lo tenv t in
          let n := Z.to_nat (Word.unsigned i) in
          Load_Val (firstn (length ft) (skipn n v))
        | _, _ => Load_MemErr
      end.

    (* Evaluate a poolcheck in an unknown region, check that o is in region r at typ t. *)
    Definition eval_poolcheckU (HT:heap_t) (r:rgn) (sz:nat) (o:operand) : option rt_val :=
      match op2rtv o env with
        | Some (RT_int _ _ addr :: nil) =>
          let ts := list_repeat sz Ftyp_int8 in
          if check_HT lo HT (Word.unsigned addr) (alpha rmap r) (sigma rmap ts)
            then Some (RT_ptr (Word.repr (Word.unsigned addr)) :: nil)
            else None
        | _ => None
      end.

  End MEM_HELPER_FUNCS.

  (* Casts a pointer to an integer, the type system should deal with the case
     that the pointer doesn't exist. *)
  Definition eval_ptrtoint (x:id) (o:operand) (t1 t2:typ) : option rt_val :=
    match op2rtv o env with
      | Some (RT_int _ _ i :: nil) => Some (RT_int WORDSIZE_BITS lt_63_MAX_I_BITS (Word.repr (Word.unsigned i)) :: nil) 
      | _ => None
    end. 
  
  (* Evaluate a branch statement, return None if condition is messed up or 
     blocks don't exist *)
  Definition eval_br (bs:blocks) (o:operand) (l1 l2:lab) : option block :=
    match op2rtv o env with
      | Some (RT_int 0 lt_0_MAX_I_BITS i :: nil) =>
        if Word.eq_dec i Word.one then lookup_blk l1 bs else lookup_blk l2 bs
      | _ => None
    end.

  (* Evaluate a switch statement *)
  Fixpoint eval_switch (bs:blocks) (o:operand) (ldef:lab) (ls:list (typ * const * lab)) : option block :=
    match ls with
      | nil => lookup_blk ldef bs
      | (_, Const_int sz1 pf1 i1, l)::ls' =>
        match op2rtv o env with
          | Some (RT_int sz2 pf2 i2 :: nil) =>
            match eq_nat_dec sz2 sz1 with
              | left pf => if Word.eq_dec i1 (cast sz2 sz1 pf i2) then lookup_blk l bs else eval_switch bs o ldef ls'
              | right _ => None
            end
          | _ => None
        end
      | _ => None
    end.

  (* Evaluate an indirect branch statement *)
  Fixpoint eval_indirect_br (bs:blocks) (o:operand) (ls:list lab) : option block :=
    match ls with
      | nil => None
      | l::ls' =>
        match op2rtv o env with
          | Some (RT_int _ _ addr :: nil) =>
            if Word.eq_dec addr (Word.repr (Word.unsigned l)) then lookup_blk l bs else eval_indirect_br bs o ls'
          | _ => None
        end
    end.

  (* Binds the arguments to the identifiers in stuff, and returns an optional 
   * fresh environment *)
  Definition init_fun' (x:id) (o:operand) (fenv:Nenv.t rt_val) : option (Nenv.t rt_val) :=
    match op2rtv o env with
      | Some rt => Some (Nenv.add x rt fenv)
      | None => None
    end.

  Variable lo : layout.
  Variable tenv : tenv_t.
  Fixpoint init_fun (params:list id) (sig:list typ) (args:list operand) : option (Nenv.t rt_val) :=
    match params, args, sig with
      | nil, nil, nil => Some (Nenv.empty rt_val)
      | x :: params', o :: args', t :: sig' => 
        match init_fun params' sig' args', op2rtv o env with
          | Some fenv', Some rt => Some (Nenv.add x (weaken_val rt (flatten_typ lo tenv t)) fenv')
          | _, _ => None
        end
      | _, _, _ => None
    end.

End HELPER_FUNCS. 

Section PHIS_SEC.
  Variable lo : layout.
  Variable tenv : tenv_t.

  Fixpoint update_phi' (env:Nenv.t rt_val) (l:lab) (x:id) (t:typ) (ls:list (operand*lab)) : option (Nenv.t rt_val) :=
    match ls with
      | nil => None
      | (o,l') :: ls' => 
        if lab_dec l l' 
          then match op2rtv o env with
                 | Some rt => Some (Nenv.add x (weaken_val rt (flatten_typ lo tenv t)) env)
                 | None => None
               end
          else update_phi' env l x t ls' 
    end.
  Definition update_phi (env:Nenv.t rt_val) (l:lab) (phi:phinode) : option (Nenv.t rt_val) :=
    match phi with
      | Insn_phi x t ls => update_phi' env l x t ls 
    end.
  Fixpoint update_phis (env:Nenv.t rt_val) (l:lab) (phis:phiblock) : option (Nenv.t rt_val) :=
    match phis with
      | nil => Some env
      | p :: phis' => match update_phi env l p with
                        | Some env' => update_phis env' l phis'
                        | None => None
                      end
    end.
End PHIS_SEC.

(* Binds a function polymorphic region to its concrete instatiation *)
Fixpoint bind_prgn (prgn1 prgn2:list rgn) (rmap:Nenv.t rgn) 
  : option (Nenv.t rgn) :=
  match prgn1, prgn2 with
    | p1::prgn1', p2::prgn2' =>
      match Nenv.find p2 rmap with
        | Some p2' =>
          match bind_prgn prgn1' prgn2' rmap with
            | Some rmap' => Some (Nenv.add p1 p2' rmap')
            | None => None
          end
        | None => None
      end
    | nil, nil => Some (Nenv.empty rgn)
    | _, _ => None
  end.

(* Adds extra local region bindings to the current rmap *)
Fixpoint bind_lrgn (lrgn:list (rgn*rgn)) (rmap:Nenv.t rgn) 
  : (Nenv.t rgn) :=
  match lrgn with
    | (l1,l2)::lrgn' =>
      Nenv.add l1 l2 (bind_lrgn lrgn' rmap)
    | nil => rmap
  end.

(* Evaluate a basic block *)

Section EVAL_BLK.

  Variable fs : functions.
  Variable lo : layout.
  Variable tenv : tenv_t.

  Fixpoint eval_blk (insns:list insn) (m:mstate) : comp :=
    let mem := s_mem m in
    let stk := s_stk m in
    let cec := s_cec m in
    let env := ec_env cec in
    let rmap_e := ec_rmap_e cec in
    let rmap_b := ec_rmap_b cec in
    let rgns := ec_rgns cec in
    let live := ec_live cec in
    let HT := ec_HT cec in
    let foo := (fun i e => mk_ec (ec_fun cec) (ec_blk cec) i (ec_term cec) e HT rmap_e rmap_b rgns live) in
    match insns with
      | nil =>
        let nec := foo nil env in
          Delay (mk_mstate mem nec stk)
      | c::insns' =>
        match c with
          | Insn_binop x b o1 o2 =>
            match eval_binop env b o1 o2 with
              | Some rt' => 
                let nec := foo insns' (Nenv.add x rt' env) in
                  eval_blk insns' (mk_mstate mem nec stk)
              | None => EvalErr
            end
          | Insn_fbinop x f o1 o2 =>
            match eval_fbinop env f o1 o2 with
              | Some rt' => 
                let nec := foo insns' (Nenv.add x rt' env) in
                  eval_blk insns' (mk_mstate mem nec stk)
              | None => EvalErr
            end
          | Insn_icmp x c o1 o2 => 
            match eval_icmp env c o1 o2 with
              | Some rt' =>
                let nec := foo insns' (Nenv.add x rt' env) in 
                  eval_blk insns' (mk_mstate mem nec stk)
              | None => EvalErr
            end
          | Insn_fcmp x c o1 o2 =>
            match eval_fcmp env c o1 o2 with
              | Some rt' =>
                let nec := foo insns' (Nenv.add x rt' env) in 
                  eval_blk insns' (mk_mstate mem nec stk)
              | None => EvalErr
            end
          | Insn_select x t c t1 o1 t2 o2 =>
            match eval_select env lo tenv t1 c o1 o2 with
              | Some rt' =>
                let nec := foo insns' (Nenv.add x rt' env) in 
                  eval_blk insns' (mk_mstate mem nec stk)
              | None => EvalErr
            end
          | Insn_load x t1 o1 =>
            match eval_load env mem lo tenv rmap_b t1 o1 with
              | Load_Val rt' => 
                let nec := foo insns' (Nenv.add x rt' env) in 
                  eval_blk insns' (mk_mstate mem nec stk)
              | Load_SvaErr => Ret
              | Load_MemErr => EvalErr
            end
          | Insn_store t1 o1 t2 o2 => 
            match eval_store env mem lo tenv rmap_b t1 t2 o1 o2 with
              | Store_Val mem' =>
                let nec := foo insns' env in
                  eval_blk insns' (mk_mstate mem' nec stk)
              | Store_SvaErr => Ret
              | Store_MemErr => EvalErr
            end
          | Insn_poolcheck x2 r t (Op_reg x) =>
            match eval_poolcheck env lo tenv rmap_b HT r t (Op_reg x) with
              | Some rt' =>
                let nec := foo insns' (Nenv.add x2 rt' env) in
                  eval_blk insns' (mk_mstate mem nec stk)
              | None => Ret
            end
          | Insn_poolcheck x r t o => EvalErr
          | Insn_free t o => 
            match eval_free env mem lo o with
              | Some mem' => 
                let nec := foo insns' env in
                  eval_blk insns' (mk_mstate mem' nec stk)
              | None => EvalErr
            end
          | Insn_bitcast x t1 o1 t2 => 
            match eval_bitcast env t1 t2 o1 with
              | Some rt =>
                let nec := foo insns' (Nenv.add x rt env) in
                  eval_blk insns' (mk_mstate (s_mem m) nec stk)
              | None => EvalErr
            end
          | Insn_gep x t1 o1 t2 o2 =>
            match eval_gep env lo tenv o1 o2 t1 t2 with
              | Load_Val rt =>
                let nec := foo insns' (Nenv.add x rt env) in 
                  eval_blk insns' (mk_mstate mem nec stk)
              | Load_SvaErr => Ret
              | Load_MemErr => EvalErr
            end
          | Insn_gep1 x t1 o1 o2 =>
            match eval_gep1 env lo tenv o1 o2 t1 with
              | Load_Val rt =>
                let nec := foo insns' (Nenv.add x rt env) in 
                  eval_blk insns' (mk_mstate mem nec stk)
              | Load_SvaErr => Ret
              | Load_MemErr => EvalErr
            end
          | Insn_extractvalue x t1 o t2 c =>
            match eval_extractvalue env lo tenv o t2 c with
              | Load_Val rt =>
                let nec := foo insns' (Nenv.add x rt env) in
                  eval_blk insns' (mk_mstate mem nec stk)
              | Load_SvaErr => Ret
              | Load_MemErr => EvalErr
            end
          | Insn_insertvalue x t1 o1 t2 o2 c =>
            match eval_insertvalue env o1 o2 c with
              | Load_Val rt =>
                let nec := foo insns' (Nenv.add x rt env) in
                  eval_blk insns' (mk_mstate mem nec stk)
              | Load_SvaErr => Ret
              | Load_MemErr => EvalErr
            end
          | Insn_iconv x c t1 o t2 =>
            match eval_iconv env c o t2 with
              | Some rt' => 
                let nec := foo insns' (Nenv.add x rt' env) in
                  eval_blk insns' (mk_mstate (s_mem m) nec stk)
              | None => EvalErr
            end
          | Insn_fconv x c t1 o t2 =>
            match eval_fconv env c o t2 with
              | Some rt' => 
                let nec := foo insns' (Nenv.add x rt' env) in
                  eval_blk insns' (mk_mstate (s_mem m) nec stk)
              | None => EvalErr
            end
          | Insn_ptrtoint x t1 o1 t2 => 
            match eval_ptrtoint env x o1 t1 t2 with
              | Some rt' => 
                let nec := foo insns' (Nenv.add x rt' env) in
                  eval_blk insns' (mk_mstate (s_mem m) nec stk)
              | None => EvalErr
            end
          | Insn_inttoptr x t1 o1 t2 =>
            match eval_inttoptr env lo tenv live rmap_b HT o1 t2 with
              | Load_Val rt' => 
                let nec := foo insns' (Nenv.add x rt' env) in
                  eval_blk insns' (mk_mstate (s_mem m) nec stk)
              | Load_SvaErr => Ret (* in this case, its like an Sva error *)
              | Load_MemErr => EvalErr
            end
          | Insn_gepU x t o1 o2 =>
            match eval_gepU env o1 o2 t with
              | Load_Val rt =>
                let nec := foo insns' (Nenv.add x rt env) in 
                  eval_blk insns' (mk_mstate mem nec stk)
              | Load_SvaErr => Ret
              | Load_MemErr => EvalErr
            end
          | Insn_poolcheckU x2 r sz (Op_reg x) =>
            match eval_poolcheckU env lo rmap_b HT r sz (Op_reg x) with
              | Some rt =>
                let nec := foo insns' (Nenv.add x2 rt env) in
                  eval_blk insns' (mk_mstate mem nec stk)
              | None => Ret
            end
          | Insn_poolcheckU x2 r sz o => EvalErr
          | Insn_exit => Ret
        end
    end.
End EVAL_BLK.

(* ---------------------------------------------------------------------- *)
(** * Mixed Small-step operational semantics. *)
(* ---------------------------------------------------------------------- *)

Variable fresh_ctr : nat.

(* The bool says if the system is halted or not. Note that we have transitions
 * to halted states if any run-time support function fails. This occurs on
 * delete regions (return, return void), new regions (call), and alloc (malloc). *)
Inductive mstep : config -> mstate -> mstate -> bool ->Prop :=
| Mstep_return : forall fs lo tenv mem f b env stk t rt o f' b' env' t' x' l' o' prgns' args' rmap_e rmap_b rgns live rmap_e' rmap_b' rgns' live' live'' mem' HT HT' HT'',
  SVAmem.del_regions mem lo live HT' HT rgns = Some (mem', HT'', live'') ->
  op2rtv o env = Some rt ->
  mstep
    (mk_config fs lo tenv)
    (mk_mstate mem (mk_ec f b nil (Insn_term (Insn_return t o)) env HT rmap_e rmap_b rgns live)
      ((mk_ec f' b' nil (Insn_nd (Insn_call (Some x') (Some t') o' prgns' args' l')) env' HT' rmap_e' rmap_b' rgns' live')::stk))
    (mk_mstate mem' (mk_ec f' b' nil (Insn_term (Insn_br_uncond l')) 
      (Nenv.add x' (weaken_val rt (flatten_typ lo tenv t')) env') HT'' rmap_e' rmap_b' rgns' live'') stk)
    false
| Mstep_return_void : forall fs lo tenv mem f b env stk f' b' l' o' prgns' args' env' rmap_e rmap_b rgns live rmap_e' rmap_b' rgns' live' live'' mem' HT HT' HT'',
  SVAmem.del_regions mem lo live HT' HT rgns = Some (mem', HT'', live'') ->
  mstep 
    (mk_config fs lo tenv)
    (mk_mstate mem (mk_ec f b nil (Insn_term (Insn_return_void)) env HT rmap_e rmap_b rgns live) 
      ((mk_ec f' b' nil (Insn_nd (Insn_call None None o' prgns' args' l')) env' HT' rmap_e' rmap_b' rgns' live')::stk))
    (mk_mstate mem' (mk_ec f' b' nil (Insn_term (Insn_br_uncond l')) env' HT'' rmap_e' rmap_b' rgns' live'') stk)
    false
| Mstep_br_uncond : forall fs lo tenv mem f b l env env' stk b' HT rmap_e rmap_b rgns live,
  lookup_blk l (f_body f) = Some b' ->
  l = (b_lab b') ->
  update_phis lo tenv env (b_lab b) (b_phis b') = Some env' ->
  mstep 
    (mk_config fs lo tenv)
    (mk_mstate mem (mk_ec f b nil (Insn_term (Insn_br_uncond l)) env HT rmap_e rmap_b rgns live) stk) 
    (mk_mstate mem (mk_ec f b' (b_insns b') (b_nd_term b') env' HT rmap_e rmap_b rgns live) stk)
    false
| Mstep_br : forall fs lo tenv mem f b l1 l2 env stk b' o env' HT rmap_e rmap_b rgns live,
  eval_br env (f_body f) o l1 l2 = Some b' ->
  update_phis lo tenv env (b_lab b) (b_phis b') = Some env' ->
  mstep 
    (mk_config fs lo tenv)
    (mk_mstate mem (mk_ec f b nil (Insn_term (Insn_br o l1 l2)) env HT rmap_e rmap_b rgns live) stk)
    (mk_mstate mem (mk_ec f b' (b_insns b') (b_nd_term b') env' HT rmap_e rmap_b rgns live) stk)
    false
| Mstep_switch : forall fs lo tenv mem f b t ldef ls env stk b' o env' HT rmap_e rmap_b rgns live,
  eval_switch env (f_body f) o ldef ls = Some b' ->
  update_phis lo tenv env (b_lab b) (b_phis b') = Some env' ->
  mstep 
    (mk_config fs lo tenv)
    (mk_mstate mem (mk_ec f b nil (Insn_term (Insn_switch t o ldef ls)) env HT rmap_e rmap_b rgns live) stk)
    (mk_mstate mem (mk_ec f b' (b_insns b') (b_nd_term b') env' HT rmap_e rmap_b rgns live) stk)
    false
| Mstep_indirect_br : forall fs lo tenv mem f b t ls env stk b' o env' HT rmap_e rmap_b rgns live,
  eval_indirect_br env (f_body f) o ls = Some b' ->
  update_phis lo tenv env (b_lab b) (b_phis b') = Some env' ->
  mstep 
    (mk_config fs lo tenv)
    (mk_mstate mem (mk_ec f b nil (Insn_term (Insn_indirect_br t o ls)) env HT rmap_e rmap_b rgns live) stk)
    (mk_mstate mem (mk_ec f b' (b_insns b') (b_nd_term b') env' HT rmap_e rmap_b rgns live) stk)
    false
| Mstep_indirect_br_fail : forall fs lo tenv mem f b t ls env stk o HT rmap_e rmap_b rgns live,
  eval_indirect_br env (f_body f) o ls = None ->
  mstep 
    (mk_config fs lo tenv)
    (mk_mstate mem (mk_ec f b nil (Insn_term (Insn_indirect_br t o ls)) env HT rmap_e rmap_b rgns live) stk)
    (mk_mstate mem (mk_ec f b nil (Insn_term (Insn_indirect_br t o ls)) env HT rmap_e rmap_b rgns live) stk)
    true
| Mstep_unreachable : forall fs lo tenv mem f b env stk HT rmap_e rmap_b rgns live,
  mstep
  (mk_config fs lo tenv)
    (mk_mstate mem (mk_ec f b nil (Insn_term (Insn_unreachable)) env HT rmap_e rmap_b rgns live) stk)
    (mk_mstate mem (mk_ec f b nil (Insn_term (Insn_unreachable)) env HT rmap_e rmap_b rgns live) stk)
    true
| Mstep_malloc : forall fs lo tenv mem f b l env stk r t x o rt mem' HT rmap_e rmap_b rgns live,
  eval_malloc env mem lo tenv live rmap_b HT r t o = Some (rt, mem') ->
  mstep 
    (mk_config fs lo tenv)
    (mk_mstate mem (mk_ec f b nil (Insn_nd (Insn_malloc x t r o l)) env HT rmap_e rmap_b rgns live) stk)
    (mk_mstate mem' (mk_ec f b nil (Insn_term (Insn_br_uncond l))
      (Nenv.add x rt env) HT rmap_e rmap_b rgns live) stk)
    false
| Mstep_malloc_fail : forall fs lo tenv mem f b l env stk r t x o HT rmap_e rmap_b rgns live,
  eval_malloc env mem lo tenv live rmap_b HT r t o = None ->
  mstep 
    (mk_config fs lo tenv)
    (mk_mstate mem (mk_ec f b nil (Insn_nd (Insn_malloc x t r o l)) env HT rmap_e rmap_b rgns live) stk) 
    (mk_mstate mem (mk_ec f b nil (Insn_nd (Insn_malloc x t r o l)) env HT rmap_e rmap_b rgns live) stk)
    true
| Mstep_call : forall fs lo tenv mem f b l env stk b' t x o prgns args fid' f' env' rmap_e rmap_b rgns live rmap_e' rmap_b' live' lrgns HT HT' mem' rgns',
  op2fun o env = Some fid' ->
  lookup_fun fid' fs = Some f' ->
  lookup_blk fid' (f_body f') = Some b' ->
  init_fun env lo tenv (f_params f') (f_sig f') args = Some env' ->
  bind_prgn (domain (f_prgn f')) prgns rmap_b = Some rmap_e' ->
  bind_lrgn lrgns rmap_e' = rmap_b' ->
  SVAmem.freshn fresh_ctr live (f_lrgn f') = Some (lrgns, live', rgns') ->
  SVAmem.new_regions mem lo tenv rmap_b' live rgns' HT (f_lrgn f') = Some (mem', HT') ->
  fid' <> Word.repr 0 ->
  mstep 
    (mk_config fs lo tenv)
    (mk_mstate mem (mk_ec f b nil (Insn_nd (Insn_call x t o prgns args l)) env HT rmap_e rmap_b rgns live) stk)
    (mk_mstate mem' (mk_ec f' b' (b_insns b') (b_nd_term b') env' HT' rmap_e' rmap_b' rgns' live') 
      ((mk_ec f b nil (Insn_nd (Insn_call x t o prgns args l)) env HT rmap_e rmap_b rgns live)::stk))
    false
| Mstep_call_fail : forall fs lo tenv mem f b env stk t x o prgns args l HT rmap_e rmap_b rgns live fid',
  op2fun o env = Some fid' ->
  fid' = Word.repr 0 ->
  mstep
    (mk_config fs lo tenv)
    (mk_mstate mem (mk_ec f b nil (Insn_nd (Insn_call x t o prgns args l)) env HT rmap_e rmap_b rgns live) stk)
    (mk_mstate mem (mk_ec f b nil (Insn_nd (Insn_call x t o prgns args l)) env HT rmap_e rmap_b rgns live) stk)
    true
| Mstep_call_fail2 : forall fs lo tenv mem f b env stk t x o prgns args l f' HT rmap_e rmap_b rgns live fid' lrgns live' rgns' rmap_e' rmap_b',
  op2fun o env = Some fid' ->
  lookup_fun fid' fs = Some f' ->
  SVAmem.freshn fresh_ctr live (f_lrgn f') = None \/
  (SVAmem.freshn fresh_ctr live (f_lrgn f') = Some (lrgns, live', rgns') /\
  bind_prgn (domain (f_prgn f')) prgns rmap_b = Some rmap_e' /\
  bind_lrgn lrgns rmap_e' = rmap_b' /\
  SVAmem.new_regions mem lo tenv rmap_b' live rgns' HT (f_lrgn f') = None) ->
  mstep
    (mk_config fs lo tenv)
    (mk_mstate mem (mk_ec f b nil (Insn_nd (Insn_call x t o prgns args l)) env HT rmap_e rmap_b rgns live) stk)
    (mk_mstate mem (mk_ec f b nil (Insn_nd (Insn_call x t o prgns args l)) env HT rmap_e rmap_b rgns live) stk)
    true
| Mstep_eval : forall fs lo tenv mem f b env stk insns t m' HT rmap_e rmap_b rgns live,
  eval_blk lo tenv insns (mk_mstate mem (mk_ec f b insns t env HT rmap_e rmap_b rgns live) stk) = 
  Delay m' ->
  mstep (mk_config fs lo tenv) 
    (mk_mstate mem (mk_ec f b insns t env HT rmap_e rmap_b rgns live) stk) 
    m'
    false
| Mstep_eval_fail : forall fs lo tenv mem f b env stk insns t HT rmap_e rmap_b rgns live,
  eval_blk lo tenv insns (mk_mstate mem (mk_ec f b insns t env HT rmap_e rmap_b rgns live) stk) = 
  Ret ->
  mstep 
    (mk_config fs lo tenv)
    (mk_mstate mem (mk_ec f b insns t env HT rmap_e rmap_b rgns live) stk)
    (mk_mstate mem (mk_ec f b insns t env HT rmap_e rmap_b rgns live) stk)
    true
| Mstep_unsafe_call : forall fs lo tenv mem f b env stk xt op os l HT rmap_e rmap_b rgns live mem' f' b' insns' t' env' HT' rmap_e' rmap_b' rgns' live' stk' halt,
  mstep
    (mk_config fs lo tenv)
    (mk_mstate mem (mk_ec f b nil (Insn_nd (Insn_unsafe_call xt op os l)) env HT rmap_e rmap_b rgns live) stk)
    (mk_mstate mem' (mk_ec f' b' insns' t' env' HT' rmap_e' rmap_b' rgns' live') stk')
    halt
  .
Hint Constructors mstep.

(* Final state is basically on a return and empty execution stack *)
Definition final_state (m:mstate) : Prop :=
  match m with
    | mk_mstate _ (mk_ec _ _ nil (Insn_term (Insn_return _ _)) _ _ _ _ _ _) nil => True
    | mk_mstate _ (mk_ec _ _ nil (Insn_term Insn_return_void) _ _ _ _ _ _) nil => True
    | _ => False
  end.
