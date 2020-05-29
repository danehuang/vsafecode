open Utility
open SCast

(* debugging functions *)
let debug = ref false
let log str =
  if (!debug) then print_endline str else ()

let string_of_gamma (gamma:typ SMap.t) : string = 
  "{"^
  SMap.fold
    ( fun k v acc ->
	"(" ^ k ^ ", " ^ Pprint.string_of_typ v ^ ") " ^ acc
    ) gamma "" ^ "}"

(*----------------------------------------------------------------------------*)
(* Calculates basic block preconditions *)

let lookup_const (c:const) : typ option =
  match c with
    | Const_null -> Some (Typ_int(63)) (* Some(Typ_ptr(Typ_float, "")) *)
    | Const_nullU -> Some (Typ_int(63)) (* Some(Typ_ptrU(0, "")) *)
    | Const_float(f) -> Some(Typ_float)
    | Const_double(d) -> Some(Typ_double)
    | Const_int(sz, _) -> Some(Typ_int sz)
    | Const_fun(l) -> None
    | Const_undef(t) -> None
    | Const_baddr(l1, l2) -> None

let lookup (gamma:typ SMap.t) (o:operand) : typ option =
  match o with
    | Op_reg x -> (try Some(SMap.find x gamma) with Not_found -> None)
    | Op_const c -> lookup_const c

let get_int_typ (gamma:typ SMap.t) (o:operand) : typ =
  match lookup gamma o with
    | Some t ->
	(match t with
	  | Typ_int(sz) -> Typ_int(sz)
	  | _ -> 
	      log ("Typ was not int for: " ^ Pprint.string_of_op o) ; 
	      log (string_of_gamma gamma) ; 
	      failwith "Precond: did not find int where expected"
	)
    | None -> 
	log ("Did not find operand: " ^ Pprint.string_of_op o) ;
	log (string_of_gamma gamma) ; 
	failwith "Precond: did not find int where expected"

let get_float_typ (gamma:typ SMap.t) structM (o:operand) : typ =
  match lookup gamma o with
    | Some t -> 
	(match t with
	  | Typ_float -> Typ_float
	  | Typ_double -> Typ_double
	  | Typ_int(sz) -> 
	      if sz = 31 then Typ_float else Typ_double
	  | Typ_name(x, rs) ->
	      let (ts, rs) = SMap.find x structM in
	      List.hd ts
	  | _ -> failwith "Precond: did not find float where expected")
    | None -> failwith "Precond: did not find float where expected"

let unfold_ptr (t:typ) : typ =
  match t with
    | Typ_ptr(t, r) -> t
    | Typ_ptrU(sz, r) -> 
	if sz = 1 then
	  Typ_int(7)
	else if sz = 2 then
	  Typ_int(15)
	else if sz = 4 then
	  Typ_int(31)
	else if sz = 8 then
	  Typ_int(63) 
	else Typ_int(63)
    | _ -> failwith "Precond: found non-ptr where expected"

let op2id o =
  match o with
    | Op_reg x -> x
    | _ -> failwith "expected register in precond"

let precond_insn (gamma:typ SMap.t) structM (i:insn) : typ SMap.t = 
  match i with
    | Insn_binop(x, bop, o1, o2) -> SMap.add x (get_int_typ gamma o1) gamma
    | Insn_fbinop(x, fop, o1, o2) -> SMap.add x (get_float_typ gamma structM o1) gamma
    | Insn_icmp(x, c, o1, o2) -> SMap.add x (Typ_int(0)) gamma
    | Insn_fcmp(x, fc, o1, o2) -> SMap.add x (Typ_int(0)) gamma
    | Insn_select(x, t1, o1, t2, o2, t3, o3) -> SMap.add x t2 gamma
    | Insn_load(x, t, o) -> SMap.add x (unfold_ptr t) gamma
    | Insn_store(t1, o1, t2, o2) -> gamma
    | Insn_poolcheck(x, r, t, o) -> SMap.add x (Typ_ptr(t, r)) gamma
    | Insn_free(t, o) -> gamma
    | Insn_gep(x, t1, o1, t2, o2) -> 
	(match t1, o2 with
	   | Typ_ptr(_, r), Op_const(_) -> SMap.add x (Typ_ptr(t2, r)) gamma
	   | Typ_ptr(_, r), Op_reg _ -> SMap.add x (Typ_int(63)) gamma
	   | _, _ -> failwith ("Precond: ill-formed gep\n" ^ (Pprint.string_of_insn i))
	)
    | Insn_gep1(x, t1, o1, o2) -> SMap.add x (Typ_int(63)) gamma
    | Insn_extractvalue(x, t1, o, t2, c) -> SMap.add x t2 gamma
    | Insn_insertvalue(x, t1, o1, t2, o2, c) -> SMap.add x t1 gamma
    | Insn_iconv(x, ic, t1, o, t2) -> SMap.add x t2 gamma
    | Insn_fconv(x, fc, t1, o, t2) -> SMap.add x t2 gamma
    | Insn_bitcast(x, t1, o, t2) -> SMap.add x t2 gamma  (* should this be failing? *)
    | Insn_ptrtoint(x, t1, o, t2) -> SMap.add x t2 gamma
    | Insn_inttoptr(x, t1, o, t2) -> SMap.add x t2 gamma
    | Insn_gepU(x, t, o1, o2) ->
	(match o2, t with
	  | Op_const(Const_int(_, i)), Typ_ptrU(sz, r) -> 
	      let t' = SMap.find (op2id o1) gamma in
	      (match t' with
		 | Typ_int _ -> SMap.add x (Typ_ptrU(0, r)) gamma
		 | _ ->
		     if sz = 0 
		     then SMap.add x (Typ_ptrU(0, r)) gamma
		     else SMap.add x (Typ_ptrU(max (sz - i) 0, r)) gamma
	      )
	  | Op_reg _, Typ_ptrU(_, r) -> SMap.add x (Typ_ptrU(0, r)) gamma
	  | _, Typ_int _ -> SMap.add x (Typ_int(63)) gamma 
	  | _, _ ->
	      failwith ("Precond: ill-formed gepU\n" ^ Pprint.string_of_insn i)
	)
    | Insn_poolcheckU(x, r, sz, o) -> SMap.add x (Typ_ptrU(sz, r)) gamma
    | Insn_exit -> gamma

let precond_nd (gamma:typ SMap.t) (nd:insn_nd) : typ SMap.t =
  match nd with
    | Insn_call(x, t, o, rgs, os, l) -> 
	(match x, t with
	  | None, None -> gamma
	  | Some x, Some t -> SMap.add x t gamma
	  | _, _ -> failwith "Precond: ill-formed call (assignment and return type mismatch)")
    | Insn_malloc(x, t, r, o, l) -> 
	(match t with
	   | Some t -> SMap.add x (Typ_ptr(t, r)) gamma
	   | None -> 
	       (match o with
		 | Op_const(Const_int(_, i)) -> SMap.add x (Typ_ptrU(i, r)) gamma
		 | _ -> gamma)
	)
    | Insn_unsafe_call(xt, _, _, _) -> 
	(match xt with
	   | Some (x, t) -> SMap.add x t gamma
	   | None -> gamma
	)

let precond_tm (gamma:typ SMap.t) (tm:terminator) : typ SMap.t =
  gamma

let precond_ndtm (gamma:typ SMap.t) structM (ndtm:insn_nd_term) : typ SMap.t =
  match ndtm with
    | Insn_nd(nd) -> precond_nd gamma nd
    | Insn_term(tm) -> precond_tm gamma tm

let precond_insns (gamma:typ SMap.t) structM (is:insn list) : typ SMap.t =
  List.fold_left (fun acc i -> precond_insn acc structM i) gamma is

let precond_phi (gamma:typ SMap.t) structM (p:phinode) : typ SMap.t =
  match p with
    | Insn_phi(x, t, arms) -> SMap.add x t gamma
	
let precond_phis (gamma:typ SMap.t) structM (ps:phiblock) : typ SMap.t =
  List.fold_left (fun acc i -> precond_phi acc structM i) gamma ps

let precond_blk (gamma:typ SMap.t) structM (b:block) : typ SMap.t =
  let gamma' = precond_phis gamma structM b.b_phis in
  let gamma'' = precond_insns gamma' structM b.b_insns in
  precond_ndtm gamma'' structM b.b_nd_term

(* Builds the entire precondition map. *)
let precond_blks (gamma:typ SMap.t) structM (bs:block list) : typ SMap.t = 
  List.fold_left (fun acc b -> precond_blk acc structM b) gamma bs

let preconds_fargs (gamma:typ SMap.t) structM (f:function0) : typ SMap.t =
  if List.length f.f_params <> List.length f.f_sig then
    failwith "Precond: ill-formed function (parameter/signature mismatch)"
  else
    let args = List.combine f.f_params f.f_sig in
    List.fold_left (fun acc (x, t) -> SMap.add x t acc) gamma args

let string_of_precond (m:typ SMap.t) =
  SMap.fold (fun k v acc -> "(" ^ k ^ ", " ^ Pprint.string_of_typ v ^ "), " ^ acc) m ""

let string_of_defn (m: S.t SMap.t) =
  SMap.fold (fun k v acc -> "(" ^ k ^ ": " ^ Pprint.string_of_set v ^ ")\n" ^ acc) m ""

let precond_func (globsM: typ SMap.t) structM (f:function0) : (lab * typ SMap.t) list =
  (* Build map of all preconditions and function arguments. *)
  let preconds = preconds_fargs SMap.empty structM f in
  let preconds = precond_blks preconds structM f.f_body in
  let precondArgs = preconds_fargs SMap.empty structM f in  (* slightly inefficient ... *)
  (*
  let greach = Cfa.reachable f in
  log "reachability: " ;4
  log (G.string_of_g greach (fun x -> x)) ; 
  *)
  log ("Calculating precondition for: " ^ f.f_lab) ; 
  let greach = Cfa.dominator f in
  log "dominator: " ;
  log (G.string_of_g greach (fun x -> x)) ; 
  let defn = Occurs.defn_blks f.f_body in
  (* log ("defn: " ^ string_of_defn defn) ; *)
  List.fold_right 
    ( fun b acc -> 
	let bs = G.edges greach b.b_lab in
	let vars = G.S.fold (fun e acc -> S.union (SMap.find e defn) acc) bs S.empty in
	(* We also need to include the current block's phi-node definitions for this
         * basic block's preconditions *)
	let vars = S.union vars (Occurs.defn_phis b.b_phis) in 
	log (b.b_lab ^ " vars: " ^ Pprint.string_of_set vars) ; 
	let gamma = S.fold (fun e acc -> SMap.add e (SMap.find e preconds) acc) vars precondArgs in
	let gamma = SMap.fold (fun k v acc -> SMap.add k v acc) globsM gamma in
	(b.b_lab, gamma)::acc 
    ) f.f_body []

(*
let precond_funcs (fs:functions) : (lab * (lab * typ SMap.t) list) list =
  List.map (fun f -> (f.f_lab, precond_func f)) fs
*)
