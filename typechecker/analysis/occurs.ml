open Utility
open SCast

(* We assumes SSA, so used multiple times, defined once. *)

(*----------------------------------------------------------------------------*)
(* Variable use computation *)

let uses_op (o:operand) : S.t = 
  match o with
    | Op_reg x -> S.singleton x 
    | Op_const _ -> S.empty 

let uses_ops (os:operand list) : S.t =
  List.fold_left (fun acc o -> S.union (uses_op o) acc) S.empty os

let uses_insn (i:insn) : S.t =
  match i with
    | Insn_binop(x, bop, o1, o2) -> S.union (uses_op o1) (uses_op o2)
    | Insn_fbinop(x, fop, o1, o2) -> S.union (uses_op o1) (uses_op o2)
    | Insn_icmp(x, c, o1, o2) -> S.union (uses_op o1) (uses_op o2)
    | Insn_fcmp(x, fc, o1, o2) -> S.union (uses_op o1) (uses_op o2)
    | Insn_select(x, t1, o1, t2, o2, t3, o3) -> S.union (S.union (uses_op o1) (uses_op o2)) (uses_op o3)
    | Insn_load(x, t, o) -> uses_op o
    | Insn_store(t1, o1, t2, o2) -> S.union (uses_op o1) (uses_op o2)
    | Insn_poolcheck(x, r, t, o) -> uses_op o
    | Insn_free(t, o) -> uses_op o
    | Insn_gep(x, t1, o1, t2, o2) -> S.union (uses_op o1) (uses_op o2)
    | Insn_gep1(x, t1, o1, o2) -> S.union (uses_op o1) (uses_op o2)
    | Insn_extractvalue(x, t1, o, t2, c) -> uses_op o 
    | Insn_insertvalue(x, t1, o1, t2, o2, c) -> S.union (uses_op o1) (uses_op o2)
    | Insn_iconv(x, ic, t1, o, t2) -> uses_op o
    | Insn_fconv(x, fc, t1, o, t2) -> uses_op o
    | Insn_bitcast(x, t1, o, t2) -> uses_op o
    | Insn_ptrtoint(x, t1, o, t2) -> uses_op o
    | Insn_inttoptr(x, t1, o, t2) -> uses_op o
    | Insn_gepU(x, t1, o1, o2) -> S.union (uses_op o1) (uses_op o2)
    | Insn_poolcheckU(x, r, sz, o) -> uses_op o
    | Insn_exit -> S.empty

let uses_insns (is:insn list) : S.t =
  List.fold_left (fun acc i -> S.union (uses_insn i) acc) S.empty is

let uses_phi (p:phinode) : S.t =
  match p with
    | Insn_phi(x, t, arms) -> S.empty
	(* List.fold_left (fun acc (o, l) -> S.union (uses_op o) acc) S.empty arms *)

let uses_phis (ps:phinode list) : S.t =
  List.fold_left (fun acc p -> S.union (uses_phi p) acc) S.empty ps

let uses_nd (nd:insn_nd) : S.t =
  match nd with
    | Insn_call(x, t, o, rgns, os, l) -> S.union (uses_op o) (uses_ops os)
    | Insn_malloc(x, t, r, o, l) -> uses_op o
    | Insn_unsafe_call(xt, op, os, l) -> uses_ops os

let uses_tm (tm:terminator) : S.t =
  match tm with
    | Insn_return(t, o) -> uses_op o
    | Insn_return_void -> S.empty
    | Insn_br_uncond(l) -> S.empty
    | Insn_br(o, l1, l2) -> uses_op o
    | Insn_switch(t, o, l, arms) -> uses_op o 
    | Insn_indirect_br(t, o, ls) -> uses_op o
    | Insn_unreachable -> S.empty

let uses_ndtm (ndtm:insn_nd_term) : S.t =
  match ndtm with
    | Insn_nd(nd) -> uses_nd nd
    | Insn_term(tm) -> uses_tm tm

let uses_blk (b:block) : S.t = 
  let usesPhis = uses_phis b.b_phis in
  let usesInsns = uses_insns b.b_insns in
  let usesNdtm = uses_ndtm b.b_nd_term in
  S.union (S.union usesPhis usesInsns) usesNdtm

(*----------------------------------------------------------------------------*)
(* Variable definition computation *)

let defn_insn_opt (i:insn) : string option =
  match i with
    | Insn_binop(x, _, _, _) -> Some x
    | Insn_fbinop(x, _, _, _) -> Some x
    | Insn_icmp(x, _, _, _) -> Some x
    | Insn_fcmp(x, _, _, _) -> Some x
    | Insn_select(x, _, _, _, _, _, _) -> Some x
    | Insn_load(x, _, _) -> Some x
    | Insn_store(_, _, _, _) -> None
    | Insn_poolcheck(_, _, _, _) -> None
    | Insn_free(_, _) -> None
    | Insn_gep(x, _, _, _, _) -> Some x
    | Insn_gep1(x, _, _, _) -> Some x
    | Insn_extractvalue(x, _, _, _, _) -> Some x
    | Insn_insertvalue(x, _, _, _, _, _) -> Some x
    | Insn_iconv(x, _, _, _, _) -> Some x
    | Insn_fconv(x, _, _, _, _) -> Some x
    | Insn_bitcast(x, _, _, _) -> Some x
    | Insn_ptrtoint(x, _, _, _) -> Some x
    | Insn_inttoptr(x, _, _, _) -> Some x
    | Insn_gepU(x, _, _, _) -> Some x
    | Insn_poolcheckU(_, _, _, _) -> None
    | Insn_exit -> None

let defn_insn (i:insn) : S.t =
  match i with
    | Insn_binop(x, _, _, _) -> S.singleton x
    | Insn_fbinop(x, _, _, _) -> S.singleton x
    | Insn_icmp(x, _, _, _) -> S.singleton x
    | Insn_fcmp(x, _, _, _) -> S.singleton x
    | Insn_select(x, _, _, _, _, _, _) -> S.singleton x
    | Insn_load(x, _, _) -> S.singleton x
    | Insn_store(_, _, _, _) -> S.empty
    | Insn_poolcheck(x, _, _, _) -> S.singleton x
    | Insn_free(_, _) -> S.empty
    | Insn_gep(x, _, _, _, _) -> S.singleton x
    | Insn_gep1(x, _, _, _) -> S.singleton x
    | Insn_extractvalue(x, _, _, _, _) -> S.singleton x
    | Insn_insertvalue(x, _, _, _, _, _) -> S.singleton x
    | Insn_iconv(x, _, _, _, _) -> S.singleton x
    | Insn_fconv(x, _, _, _, _) -> S.singleton x
    | Insn_bitcast(x, _, _, _) -> S.singleton x
    | Insn_ptrtoint(x, _, _, _) -> S.singleton x
    | Insn_inttoptr(x, _, _, _) -> S.singleton x
    | Insn_gepU(x, _, _, _) -> S.singleton x
    | Insn_poolcheckU(x, _, _, _) -> S.singleton x
    | Insn_exit -> S.empty

let defn_insns (is:insn list) : S.t =
  List.fold_left (fun acc i -> S.union (defn_insn i) acc) S.empty is

let defn_nd (nd:insn_nd) : S.t =
  match nd with
    | Insn_call(x, _, _, _, _, _) -> 
	(match x with
	  | Some x -> S.singleton x
	  | None -> S.empty)
    | Insn_malloc(x, _, _, _, _) -> S.singleton x
    | Insn_unsafe_call (xt, _, _, _) -> 
	(match xt with
	   | Some (x, t) -> S.singleton x
	   | None -> S.empty)

let defn_ndtm (ndtm:insn_nd_term) : S.t =
  match ndtm with
    | Insn_nd(nd) -> defn_nd nd
    | Insn_term(tm) -> S.empty

let defn_phi (p:phinode) : S.t =
  match p with
    | Insn_phi(x, t, arms) -> S.singleton x

let defn_phis (ps:phinode list) : S.t =
  List.fold_left (fun acc p -> S.union (defn_phi p) acc) S.empty ps

let defn_blk (b:block) : S.t =
  let defnPhis = defn_phis b.b_phis in
  let defnInsns = defn_insns b.b_insns in
  let defnNdtm = defn_ndtm b.b_nd_term in
  S.union (S.union defnPhis defnInsns) defnNdtm

let defn_blks (bs:block list) : S.t SMap.t =
  List.fold_left (fun acc b -> SMap.add b.b_lab (defn_blk b) acc) SMap.empty bs

(*----------------------------------------------------------------------------*)
(* Free-variable computation *)

let fv_blk (b:block) : S.t =
  S.diff (uses_blk b) (defn_blk b)

let fv_blks (bs:block list) : S.t SMap.t =
  List.fold_left (fun acc b -> SMap.add b.b_lab (fv_blk b) acc) SMap.empty bs
