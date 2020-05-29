(* Other library imports *)
Add LoadPath "../libs/".
Add LoadPath "../libs/CompCert-Toolkit".
Require Import Tactics.
Require Import Bits.

Require Import Coqlib.


(* Illvm imports *)
Require Import Utility.
Require Import IllvmAST.
Require Import IllvmValues.
Require Import TargetData.


(* ---------------------------------------------------------------------- *)
(* Contains an abstract memory signature for a memory *)

Module Type MemSig.
  Parameter cmem : Type.

  Parameter empty : cmem.
  Definition nullptr : Z := 0.

  (* ---------------------------------------------------------------------- *)
  (* Memory Operations *)

  (* Read out an optional run-time value given an address, typ, and memory. *)
  Parameter load : forall (m:cmem) (lo:layout) (addr:Z) (t:ftyp), option rt_tag.

  (* Write in a run-time value given an address, typ, and memory. Return None 
   * on failure. *)
  Parameter store : forall (m:cmem) (lo:layout) (addr:Z) (t:ftyp) (rt:rt_tag), option cmem.

  (* Optionally return the base address and memory state, given an allocation
   * request for n cells of typ t. Fails if out of memory. *)
  Parameter alloc : forall (m:cmem) (lo:layout) (live:list rgn) (HT:heap_t) (t:ftyps) (s:nat) (r:rgn), option (PTRTYP*cmem).

  (* Optionally return the memory state with block pointed to be addr freed. *)
  Parameter free : forall (m:cmem) (lo:layout) (addr:Z), option cmem. 

  (* Generate new run-time regions fresh from live, optionally returning the updated
   * memory, the updated heap type, syn-region -> rt-region map, and the update live
   * region list *)
  Parameter freshn : forall (n:rgn) (live:list rgn) (lrgns:list (rgn*typ)),
    option (list (rgn*rgn)*list rgn*list rgn).

  Parameter new_regions : forall (m:cmem) (lo:layout) (tenv:tenv_t) (rmap:Nenv.t rgn) (live rgns:list rgn) (HT:heap_t) (lrgn:list (rgn*typ)), option (cmem * heap_t).

  (* Delete the rgns specified in live, returning the new memory, heap-typing, and live
   * list. HT1 is the input typing, HT2 is the expected heap-typing. Thus, it doesn't
   * really need to produce a heap typing. *)
  Parameter del_regions : forall (m:cmem) (lo:layout) (live:list rgn) (HT1 HT2:heap_t) (rgns:list rgn), option (cmem * heap_t * list rgn).

  (* ---------------------------------------------------------------------- *)
  (* Properties *)

  (* ---------------------------------------------------------------------- *)
  (* Load Properties *)
  Axiom load_typ : forall m n t v lo,
    load m lo n t = Some v ->
    match t with
      | Ftyp_float => exists f, v = RT_float f
      | Ftyp_double => exists d, v = RT_double d
      | Ftyp_int sz pf => exists i, v = RT_int sz pf i
      | Ftyp_ptr t' r => exists i, v = RT_ptr i
      | Ftyp_fun p s r => exists l, v = RT_fun l
      | Ftyp_ptrU sz r => exists i, v = RT_ptr i
    end.

  Axiom load_null_fail : forall m t lo,
    load m lo 0 t = None.

  (* ---------------------------------------------------------------------- *)
  (* Store Properties *)
  Axiom load_store_valid : forall m1 n t v v' lo tenv fs HT live,
    wf_value' fs lo tenv HT live v' t ->
    load m1 lo n t = Some v ->
    exists m2, store m1 lo n t v' = Some m2.

  Axiom load_store_other : forall m1 m2 n t v n' t' fs lo tenv HT live,
    wf_value' fs lo tenv HT live v t ->
    store m1 lo n t v = Some m2 ->
    n' + size_ftyp lo t' <= n
    \/ n + size_ftyp lo t <= n' ->
    load m2 lo n' t' = load m1 lo n' t'.

  Axiom load_store_same : forall m1 m2 n t v fs lo tenv HT live,
    wf_value' fs lo tenv HT live v t ->
    store m1 lo n t v = Some m2 ->
    load m2 lo n t = Some v.

  Axiom load_store_valid_sub : forall m1 n t1 t2 v v' lo tenv fs HT live rmap,
    ftyp_sub t1 t2 = true ->
    wf_value' fs lo tenv HT live v' (sigma' rmap t1) ->
    load m1 lo n (sigma' rmap t2) = Some v ->
      exists m2, store m1 lo n (sigma' rmap t2) v' = Some m2.
  
  Axiom load_store_same_sub : forall m1 m2 n t1 t2 v fs lo tenv HT live rmap,
    ftyp_sub t1 t2 = true ->
    wf_value' fs lo tenv HT live v (sigma' rmap t1) ->
    store m1 lo n (sigma' rmap t2) v = Some m2 ->
    load m2 lo n (sigma' rmap t2) = Some v.

  Axiom store_null_fail : forall m tenv t v,
    store m tenv 0 t v = None.

  (* ---------------------------------------------------------------------- *)
  (* Alloc Properties *)
  Axiom alloc_typ : forall m t m' n r fs lo tenv HT live rmap s,
    wf_tenv tenv ->
    TS tenv t ->
    alloc m lo live HT (sigma rmap (flatten_typ lo tenv t)) s (alpha rmap r) = Some (n,m') ->
    wf_value' fs lo tenv live HT 
      (RT_ptr n) 
      (Ftyp_ptr (sigma'' rmap t) (alpha rmap r)).

  Axiom load_alloc_same : forall m lo live HT t m' n n' t' v r s,
    alloc m lo live HT t s r = Some (n, m') ->
    load m lo n' t' = Some v ->
    load m' lo n' t' = Some v.

  Axiom alloc_typU : forall m m' n r fs lo tenv HT live rmap s sz,
    alloc m lo live HT (list_repeat sz Ftyp_int8) s (alpha rmap r) = Some (n,m') ->
    wf_value' fs lo tenv live HT
      (RT_ptr n)
      (Ftyp_ptrU sz (alpha rmap r)).

  (* ---------------------------------------------------------------------- *)
  (* Free Properties *)
  Axiom load_free_valid : forall m lo n t v,
    load m lo n t = Some v ->
    exists m', free m lo n = Some m'.

  Axiom load_free_same : forall m lo n m' t v,
    free m lo n = Some m' ->
    load m lo n t = Some v ->
    load m' lo n t = Some v.

  (* ---------------------------------------------------------------------- *)
  (* New Region Properties *)

  Definition wf_mem (fs:functions) (lo:layout) (tenv:tenv_t) (live:list rgn) (HT:heap_t) (m:cmem) : Prop :=
    forall n t r,
      Zenv.find n HT = Some (t,r) ->
      exists v, load m lo n t = Some v /\ wf_value' fs lo tenv live HT v t.

  Axiom freshn_prop : forall lrgns n live rmap rgns live',
    freshn n live lrgns = Some (rmap, live', rgns) ->
    domain lrgns = domain rmap /\
    rgns = range rmap /\
    live' = rgns ++ live /\
    list_disjoint (range rmap) live /\
    list_norepet (range rmap).
  
  Axiom new_regions_prop : forall m lo live rgns HT lrgn m' HT' rmap tenv,
    list_norepet rgns ->
    list_disjoint rgns live ->
    new_regions m lo tenv rmap live rgns HT lrgn = Some (m', HT') ->
    heapt_ext HT HT' /\
    heapt_ext2 live HT HT'.

  Axiom new_regions_wf_HT_live : forall lrgn m lo HT rmap m' HT' live rgns tenv,
    Forall (fun t => wf_tenv_ftyps (rgns++live) (sigma rmap (flatten_typ lo tenv t))) (range lrgn) ->
    wf_HT_live live HT ->
    new_regions m lo tenv rmap live rgns HT lrgn = Some (m', HT') ->
    wf_HT_live (rgns++live) HT'.

  Axiom new_regions_wf_HT_bounds : forall lrgn m lo HT rmap m' HT' live rgns tenv,
    wf_HT_bounds HT ->
    new_regions m lo tenv rmap live rgns HT lrgn = Some (m', HT') ->
    wf_HT_bounds HT' /\
    max_HT HT <= max_HT HT'.

  Axiom new_regions_wf_mem : forall m lo live rgns HT lrgn m' HT' rmap fs tenv,
    wf_HT lo HT ->
    wf_tenv tenv ->
    new_regions m lo tenv rmap live rgns HT lrgn = Some (m', HT') ->
    wf_mem fs lo tenv live HT m ->
    wf_mem fs lo tenv (rgns++live) HT' m' /\ wf_HT lo HT'.

  Axiom freshn_prog : forall n live lrgn,
    freshn n live lrgn = None \/
    exists lrgns, exists live', exists rgns',
      freshn n live lrgn = Some (lrgns, live', rgns').
  
  Axiom new_regions_prog : forall m lo tenv rmap live rgns HT lrgn,
    new_regions m lo tenv rmap live rgns HT lrgn = None \/
    exists m', exists HT',
      new_regions m lo tenv rmap live rgns HT lrgn = Some (m', HT').
  
  (* ---------------------------------------------------------------------- *)
  (* Delete Region Properties *)

  Axiom del_regions_prop : forall m lo live HT HT' rgns m' HT'' live',
    del_regions m lo live HT HT' rgns = Some (m', HT'', live') ->
    live = rgns ++ live' /\
    HT = HT''.

  Axiom del_regions_wf_mem : forall m lo HT HT' rgns live fs tenv m',
    wf_HT_live live HT ->
    list_disjoint rgns live ->
    heapt_ext HT HT' ->
    heapt_ext2 live HT HT' ->
    del_regions m lo (rgns ++ live) HT HT' rgns = Some (m', HT, live) ->
    wf_mem fs lo tenv (rgns ++ live) HT' m ->
    wf_mem fs lo tenv live HT m'.

  (* ---------------------------------------------------------------------- *)
  (* Functions and properties that expose meta-data, essentially stating that
   * del_regions and new_regions are inverses of each other. *)

  (* Returns the high-address in use *)
  Parameter high_addr : forall (m:cmem), nat.

  Axiom store_high_addr_same : forall m lo n t v m',
    store m lo n t v = Some m' ->
    high_addr m = high_addr m'.

  Axiom alloc_high_addr_same : forall m lo live HT t r r' n m',
    alloc m lo live HT t r r' = Some (n,m') ->
    high_addr m = high_addr m'.

  Axiom free_high_addr_same : forall m lo n m',
    free m lo n = Some m' ->
    high_addr m = high_addr m'.
    
  Axiom new_regions_high_addr_prop : forall rgns m lo HT rmap m' HT' live tenv lrgn,
    new_regions m lo tenv rmap live rgns HT lrgn = Some (m', HT') ->
    max_HT HT + ftyp_max <= Z.of_nat (high_addr m') /\
    max_HT HT + ftyp_max < Word.max_unsigned WORDSIZE_BITS /\
    max_HT HT + ftyp_max > 0.

  Axiom del_regions_prog : forall m lo live HT HT' rgns,
    max_HT HT + ftyp_max <= Z.of_nat (high_addr m) ->
    max_HT HT + ftyp_max > 0 ->
    exists m', exists HT'', exists live', 
      del_regions m lo (rgns ++ live) HT HT' rgns = Some (m', HT'', live').

  Definition wf_mem_metadata (HT:heap_t) (m:cmem) : Prop :=
    max_HT HT + ftyp_max <= Z.of_nat (high_addr m).

  Axiom new_regions_wf_meta : forall rgns m lo HT rmap m' HT' live tenv lrgn,
    new_regions m lo tenv rmap live rgns HT lrgn = Some (m', HT') ->
    wf_mem_metadata HT' m'.

  Axiom del_regions_wf_meta : forall m lo live HT HT' rgns m' HT'' live',
    del_regions m lo live HT HT' rgns = Some (m', HT'', live') ->
    wf_mem_metadata HT'' m'.

End MemSig.
