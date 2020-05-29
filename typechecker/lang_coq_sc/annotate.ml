open Utility
open SCast
open Iast
open Pprint

(* debugging functions *)
let debug = ref true
let log str =
  if (!debug) then print_endline str else ()

let op2id o : SCast.id =
  match o with
    | SCast.Op_reg x -> x
    | SCast.Op_const c -> 
	match c with
	  | SCast.Const_fun x -> x
	  | _ -> failwith "Expected a name but none found in op2id."

let lower_rvar rv = 
  let (fname, r) = rv in
  r

let lower_size sizeM sz = 
  match sz with
    | Size_const i -> i
    | Size_var sv -> try VMap.find sv sizeM with Not_found -> 0

let rec flatten_tipe t = 
  match t with
    | Tipe_float -> [Tipe_float]
    | Tipe_double -> [Tipe_double]
    | Tipe_int sz -> [Tipe_int sz]
    | Tipe_ptr(t, r) -> [Tipe_ptr(t, r)]
    | Tipe_ptrU(sz, r) -> [Tipe_ptrU(sz, r)]
    | Tipe_struct ts -> List.fold_left (fun acc t -> acc @ flatten_tipe t) [] ts
    | Tipe_fun(rs, ts, rt) -> [Tipe_fun(rs, ts, rt)]
    | Tipe_array(t, sz) -> [Tipe_array(t, sz)]
    | Tipe_tvar _ 
    | Tipe_join _
    | Tipe_scheme _ -> failwith("should not have join var at this stage: " ^ string_of_tipe t)

let rec lift_typ fname t =
  match t with
    | Typ_float -> Tipe_float
    | Typ_double -> Tipe_double
    | Typ_int(sz) -> Tipe_int sz
    | Typ_ptr(t, r) -> Tipe_ptr(lift_typ fname t, (fname, r))
    | Typ_ptrU(sz, r) -> Tipe_ptrU(Size_const sz, (fname, r))
    | Typ_name _ -> failwith "only use on primitives"
    | Typ_fun(rs, ts, rt) -> failwith "only use on primitives"
    | Typ_array(t, sz) -> Tipe_array(lift_typ fname t, sz)

let rec lift_ftyp fname t = 
  match t with
    | Ftyp_float -> Tipe_float
    | Ftyp_double -> Tipe_double
    | Ftyp_int sz -> Tipe_int sz
    | Ftyp_ptr(t, r) -> Tipe_ptr(lift_typ fname t, (fname, r))
    | Ftyp_ptrU(sz, r) -> Tipe_ptrU(Size_const sz, (fname, r))
    | Ftyp_fun(rs, ts, rt) -> Tipe_fun(List.map (fun r -> (fname, r)) rs, List.map (lift_typ fname) ts, lift_opt (lift_typ fname) rt)

let lift_ftyps fname ts = 
  List.map (lift_ftyp fname) ts

let fresh_rvar rvarc =
  let tmp = fresh rvarc in
  "RV" ^ string_of_int tmp
	       
(* also need to substitute in region vars for the types *)
let rec generalize_ptr rvarc t = 
  match t with
    | Tipe_ptr(t, r) -> 
	let rv = fresh_rvar rvarc in
	let (t', prgns, rs) = generalize_ptr rvarc t in
	(Tipe_ptr(t', ("G", rv)), rv :: prgns, r :: rs)
    | Tipe_ptrU(sz, r) ->
	let rv = fresh_rvar rvarc in
	(Tipe_ptrU(sz, ("G", rv)), [rv], [r])
    | _ -> (t, [], [])

module TMap2 = Map.Make(struct type t = tipe let compare = compare end)
let nameM : string TMap2.t ref = ref TMap2.empty
let namec = counter()
let fresh_name() = 
  let tmp = fresh namec in
  "mystruct." ^ string_of_int tmp

let structM : (SCast.typ list * string list) SMap.t ref = ref SMap.empty

let globsM : SCast.typ SMap.t ref = ref SMap.empty

let rec generalize_struct ts = 
  let rvarc = counter() in
  List.fold_left (fun (ts, prgns, rs) t -> 
		    let (t', prgns', rs') = generalize_ptr rvarc t in
		    (ts @ [t'], prgns @ prgns', rs @ rs')
		 ) ([], [], []) ts

let string_of_generalized (ts, prgns, rs) = 
  "<" ^ sep_by ", " (fun x -> x) prgns ^ ">" ^ 
    string_of_tipe (Tipe_struct ts) ^
    "<" ^ sep_by ", " string_of_rvar rs ^ ">"

let rec lower_tipe sizeM t =
  match t with
    | Tipe_float -> Typ_float
    | Tipe_double -> Typ_double
    | Tipe_int(sz) -> Typ_int(sz)
    | Tipe_ptr(t, r) -> Typ_ptr(lower_tipe sizeM t, lower_rvar r)
    | Tipe_ptrU(sz, r) -> Typ_ptrU(lower_size sizeM sz, lower_rvar r)
    | Tipe_struct(ts) -> 
	let ts' = flatten_tipe (Tipe_struct ts) in
	let (ts'', prgns, rs) = generalize_struct ts' in
	let name = 
	  try TMap2.find (Tipe_struct(ts'')) !nameM 
	  with Not_found ->
	    let name = fresh_name() in
	    nameM := TMap2.add (Tipe_struct(ts'')) name !nameM ; 
	    name
	in
	  structM := SMap.add name ((List.map (lower_tipe sizeM) ts''), prgns) !structM ; 
	  Typ_name(name, List.map lower_rvar rs)
    | Tipe_fun(rs, ts, rt) -> Typ_fun(List.map lower_rvar rs, List.map (lower_tipe sizeM) ts, lift_opt (lower_tipe sizeM) rt)
    | Tipe_array(t, sz) -> Typ_array(lower_tipe sizeM t, sz)
    | Tipe_tvar _
    | Tipe_join _
    | Tipe_scheme _ -> failwith("should not have join var at this state: " ^ string_of_tipe t)

let get_ptr_typ t =
  match t with
    | Typ_ptr(t, r) -> t
    | Typ_ptrU(sz, r) -> Typ_int(sz * 8 - 1)
    | _ -> failwith ("Annotate: expected ptr but none found: " ^ Pprint.string_of_typ t)

let get_ptrU_size t =
  match t with
    | Typ_ptrU(sz, r) -> sz
    | _ -> 0

let op2idopt o =
  try Some (op2id o) with _ -> None

let modify_globsM sizeM gamma x =
  if VMap.mem ("G", x) gamma then
    globsM := SMap.add x (lower_tipe sizeM (VMap.find ("G", x) gamma)) !globsM

let splat t = t

let annotate_tipe fname sizeM gamma t o =
  match op2idopt o with
    | Some x ->
	modify_globsM sizeM gamma x ;
	let t = 
	(try splat (lower_tipe sizeM (VMap.find (fname, x) gamma)) with Not_found -> 
	   (try splat (lower_tipe sizeM (VMap.find ("G", x) gamma)) with Not_found -> t)
	)
	in
	  log (x ^ ": " ^ Pprint.string_of_typ t) ; 
	  t
    | None -> 
	match o with
	  | Op_const (Const_null) -> Typ_int(63)
	  | Op_const (Const_nullU) -> Typ_int(63)
	  | _ -> t

let size_typ_int t = 
  match t with
    | Typ_int(sz) -> sz
    | _ -> failwith "expected int but none found in size_typ_int"

let annotate_insn fname sizeM gamma i = 
  match i with
    | Insn_binop(x, bop, o1, o2) -> i
    | Insn_fbinop(x, fop, o1, o2) -> i
    | Insn_icmp(x, c, o1, o2) -> i
    | Insn_fcmp(x, fc, o1, o2) -> i
    | Insn_select(x, t1, o1, t2, o2, t3, o3) -> 
	Insn_select(x, t1, o1, annotate_tipe fname sizeM gamma t2 (Op_reg x), o2, annotate_tipe fname sizeM gamma t3 (Op_reg x), o3)
    | Insn_load(x, t, o) -> 
	let t' = annotate_tipe fname sizeM gamma t o in
	  (* Insn_load(x, t', o) *)
	(match t' with
	   | Typ_ptrU(sz, r) -> Insn_load(x, Typ_ptrU(size_typ_int t, r), o)
	   | _ -> Insn_load(x, t', o)
	)
    | Insn_store(t1, o1, t2, o2) -> 
	let t2' = annotate_tipe fname sizeM gamma t2 o2 in
	let t1' = try annotate_tipe fname sizeM gamma t1 o1 with _ -> get_ptr_typ t2' in
	Insn_store(t1', o1, t2', o2)
    | Insn_poolcheck(x, r, t, o) -> 
	annotate_tipe fname sizeM gamma t o ; 
	Insn_poolcheck(x, r, get_ptr_typ (annotate_tipe fname sizeM gamma t (Op_reg x)), o)
    | Insn_free(t, o) -> Insn_free(annotate_tipe fname sizeM gamma t o, o)
    | Insn_gep(x, t1, o1, t2, o2) -> Insn_gep(x, (annotate_tipe fname sizeM gamma t1 o1), o1, get_ptr_typ (annotate_tipe fname sizeM gamma t2 (Op_reg x)), o2)
    | Insn_gep1(x, t1, o1, o2) -> Insn_gep1(x, (annotate_tipe fname sizeM gamma t1 o1), o1, o2)
    | Insn_extractvalue(x, t1, o, t2, c) -> Insn_extractvalue(x, annotate_tipe fname sizeM gamma t1 o, o, annotate_tipe fname sizeM gamma t2 (Op_reg x), c)
    | Insn_insertvalue(x, t1, o1, t2, o2, c) -> 
	(match o1 with
	   | Op_const(Const_undef ts) -> 
	       let t1' = lower_tipe sizeM (Tipe_struct (lift_ftyps fname ts)) in
	       Insn_insertvalue(x, t1', o1, annotate_tipe fname sizeM gamma t2 o2, o2, c)
	   | _ -> Insn_insertvalue(x, annotate_tipe fname sizeM gamma t1 o1, o1, annotate_tipe fname sizeM gamma t2 o2, o2, c)
	)
    | Insn_iconv(x, ic, t1, o, t2) -> i
    | Insn_fconv(x, fc, t1, o, t2) -> Insn_fconv(x, fc, annotate_tipe fname sizeM gamma t1 o, o, annotate_tipe fname sizeM gamma t2 (Op_reg x))
    | Insn_bitcast(x, t1, o, t2) -> i
    | Insn_ptrtoint(x, t1, o, t2) -> Insn_ptrtoint(x, annotate_tipe fname sizeM gamma t1 o, o, t2)
    | Insn_inttoptr(x, t1, o, t2) -> Insn_inttoptr(x, t1, o, annotate_tipe fname sizeM gamma t1 o)
    | Insn_gepU(x, t, o1, o2) -> Insn_gepU(x, annotate_tipe fname sizeM gamma t o1, o1, o2)
    | Insn_poolcheckU(x, r, sz, o) -> 
	annotate_tipe fname sizeM gamma (Typ_int 63) o ; 
	Insn_poolcheckU(x, r, get_ptrU_size (annotate_tipe fname sizeM gamma (SCast.Typ_ptrU(0, r)) (SCast.Op_reg x)), o)
    | Insn_exit -> i 

let annotate_insns fname sizeM gamma is =
  List.map (annotate_insn fname sizeM gamma) is

let annotate_nd fname sizeM gamma nd =
  match nd with
    | Insn_call(x, t, o, rgns, os, l) ->
	(match x, t with
	   | Some x, Some t -> 
	       List.iter (fun o -> let _ = annotate_tipe fname sizeM gamma (Typ_int 63) o in ()) os ; 
	       Insn_call(Some x, Some (annotate_tipe fname sizeM gamma t (Op_reg x)), o, rgns, os, l)
	   | _, _ -> nd
	)
    | Insn_malloc(x, t, r, o, l) ->
	(match t with
	   | Some t ->
	       let t' = lower_tipe sizeM (VMap.find (fname, x) gamma) in
	       Insn_malloc(x, Some (get_ptr_typ t'), r, o, l)
	   | None -> nd
	)
    | Insn_unsafe_call (xt, oc, ops, l) -> 
	(match xt with
	   | Some (x, t) -> Insn_unsafe_call(Some(x, lower_tipe sizeM (VMap.find (fname, x) gamma)), oc, ops, l)
	   | None -> nd
	)

let annotate_tm fname sizeM gamma tm =
  match tm with
    | Insn_return(t, o) -> 
	(match o with
	   | Op_const (Const_undef (Ftyp_int sz :: [])) -> Insn_return(Typ_int sz, o)
	   | _ -> Insn_return(annotate_tipe fname sizeM gamma t o, o)
	)
    | Insn_return_void -> tm
    | Insn_br_uncond _ -> tm
    | Insn_br _ -> tm
    | Insn_switch _ -> tm
    | Insn_indirect_br _ -> tm
    | Insn_unreachable -> tm

let annotate_ndtm fname sizeM gamma ndtm =
  match ndtm with
    | Insn_nd(nd) -> Insn_nd(annotate_nd fname sizeM gamma nd)
    | Insn_term(tm) -> Insn_term(annotate_tm fname sizeM gamma tm)

let annotate_phi fname sizeM gamma p =
  match p with
    | Insn_phi(x, t, arms) -> 
	let t' = annotate_tipe fname sizeM gamma t (Op_reg x) in
	match t' with
	  | Typ_ptr _
	  | Typ_ptrU _ ->
	      let isint = 
		List.fold_left 
		  (fun acc (o, l) ->
		     match annotate_tipe fname sizeM gamma (Typ_float) o with
		       | Typ_int _ -> true
		       | _ -> acc
		  ) false arms
	      in
		if isint then
		  (Insn_phi(x, Typ_int 63, arms), VMap.add (fname, x) (Tipe_int 63) gamma)
		else
		  (Insn_phi(x, t', arms), gamma)
	  | _ -> (Insn_phi(x, t', arms), gamma)
	
let annotate_phis fname sizeM gamma ps =
  let (phis, gamma') = 
    List.fold_left (fun (ps, gamma) p -> 
		      let (p', gamma') = annotate_phi fname sizeM gamma p in
			(p' :: ps, gamma')
		   ) ([], gamma) ps
  in
    (List.rev phis, gamma')

let annotate_blk fname sizeM gamma b =
  let insns' = annotate_insns fname sizeM gamma b.b_insns in
  let (phis', gamma') = annotate_phis fname sizeM gamma b.b_phis in
  let ndtm' = annotate_ndtm fname sizeM gamma' b.b_nd_term in
  ({ b_lab = b.b_lab ;
     b_insns = insns' ;
     b_phis = phis' ;
     b_nd_term = ndtm'
   }, gamma')

let annotate_blks fname sizeM gamma bs = 
  let (bs, gamma') = 
    List.fold_left (fun (bs, gamma) b ->
		      let (b', gamma') = annotate_blk fname sizeM gamma b in
			(b' :: bs, gamma')
		   ) ([], gamma) bs
  in
    List.rev bs

let annotate_rgns fname sizeM delta rs =
  List.map (fun (r, t) ->
	      let t' = try lower_tipe sizeM ((VMap.find (fname, r) delta)) with Not_found -> t in
	      (r, t')
	   ) rs

let get_structM() = 
  !structM

let get_globsM() = 
  !globsM

let annotate_fun sizeM gamma f =
  let body' = annotate_blks f.f_lab sizeM gamma f.f_body in
  { f_lab = f.f_lab ;
    f_params = f.f_params ;    (* id list *)
    f_sig = f.f_sig ;          (* typ list *)
    f_body = body' ;           (* block list *)
    f_ret = f.f_ret ;          (* typ option *)
    f_prgn = f.f_prgn ;        (* (rgn * typ) list *)
    f_lrgn = f.f_lrgn          (* (rgn * typ) list *)
  }
