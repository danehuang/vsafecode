open Utility
open SCast

(* Pretty Printing Module *)

(*----------------------------------------------------------------------------*)
(* Utility *)
let rec sep_by sep f ls =
  match ls with
    | [] -> ""
    | hd::[] -> f hd
    | hd::ls -> f hd ^ sep ^ sep_by sep f ls

(*----------------------------------------------------------------------------*)
let string_of_set vars = 
  sep_by ", " (fun x -> x) (S.elements vars) 

(*----------------------------------------------------------------------------*)
(* SCast printing *)

let string_of_cond c =
  match c with
    | Cond_eq -> "cond_eq"
    | Cond_ne -> "cond_ne"
    | Cond_ugt -> "cond_ugt"
    | Cond_uge -> "cond_uge"
    | Cond_ult -> "cond_ult"
    | Cond_ule -> "cond_ule"
    | Cond_sgt -> "cond_sgt"
    | Cond_sge -> "cond_sge"
    | Cond_slt -> "cond_slt"
    | Cond_sle -> "cond_sle"

let string_of_fcond fc =
  match fc with
    | Fcond_false -> "fcond_false"
    | Fcond_oeq -> "fcond_oeq"
    | Fcond_ogt -> "fcond_ogt"
    | Fcond_oge -> "fcond_oge"
    | Fcond_olt -> "fcond_olt"
    | Fcond_ole -> "fcond_ole"
    | Fcond_one -> "fcond_one"
    | Fcond_ord -> "fcond_ord"
    | Fcond_ueq -> "fcond_ueq"
    | Fcond_ugt -> "fcond_ugt"
    | Fcond_uge -> "fcond_uge"
    | Fcond_ult -> "fcond_ult"
    | Fcond_ule -> "fcond_ule"
    | Fcond_une -> "fcond_une"
    | Fcond_uno -> "fcond_uno"
    | Fcond_true -> "fcond_true"

let string_of_binop bop =
  match bop with
    | Binop_add -> "binop_add"
    | Binop_sub -> "binop_sub"
    | Binop_mul -> "binop_mul"
    | Binop_udiv -> "binop_udiv"
    | Binop_sdiv -> "binop_sdiv"
    | Binop_urem -> "binop_urem"
    | Binop_srem -> "binop_srem"
    | Binop_shl -> "binop_shl"
    | Binop_lshr -> "binop_lshr"
    | Binop_ashr -> "binop_ashr"
    | Binop_and -> "binop_and"
    | Binop_or -> "binop_or"
    | Binop_xor -> "binop_xor"
	
let string_of_fbinop fop =
  match fop with
    | Fbinop_add -> "fbinop_add"
    | Fbinop_sub -> "fbinop_sub"
    | Fbinop_mul -> "fbinop_mul"
    | Fbinop_div -> "fbinop_div"
    | Fbinop_rem -> "fbinop_rem"

let string_of_iconv ic =
  match ic with
    | Iconv_trunc -> "iconv_trunc"
    | Iconv_zext -> "iconv_zext"
    | Iconv_sext -> "iconv_sext"
    | Iconv_fptoui -> "iconv_fptoui"
    | Iconv_fptosi -> "iconv_fptosi"

let string_of_fconv fc =
  match fc with
    | Fconv_fptrunc -> "fconv_fptrunc"
    | Fconv_fpext -> "fconv_fpext"
    | Fconv_uitofp -> "fconv_uitofp"
    | Fconv_sitofp -> "fconv_sitofp"

let string_of_rgns rgns =
  sep_by ", " (fun x -> x) rgns

let rec string_of_typ t =
  match t with
    | Typ_float -> "float"
    | Typ_double -> "double"
    | Typ_int(sz) -> "i" ^ string_of_int (sz + 1)
    | Typ_ptr(t,r) -> string_of_typ t ^ "*" ^ r
    | Typ_name(name,rgns) -> name ^"<" ^ string_of_rgns rgns ^ ">"
    | Typ_fun(rgns, ts, ret) ->
	let rgns' = string_of_rgns rgns in
	let ts' = sep_by ", " string_of_typ ts in
	(match ret with
	  | None -> "<" ^ rgns' ^ ">(" ^ ts' ^ ")"
	  | Some t -> string_of_typ t ^ " <" ^ rgns' ^ ">(" ^ ts' ^ ")")
    | Typ_array(t, sz) -> "[ " ^ string_of_typ t ^ " x " ^ string_of_int sz ^ " ]"
    | Typ_ptrU (sz, r) -> "U(" ^ string_of_int sz ^ ")*" ^ r
	  

let string_of_typs ts =
  sep_by ", " string_of_typ ts

let rec string_of_ftyp t =
  match t with
    | Ftyp_float -> "ffloat"
    | Ftyp_double -> "fdouble"
    | Ftyp_int(sz) -> "fi" ^ string_of_int (sz + 1)
    | Ftyp_ptr(t, r) -> string_of_typ t ^ "*" ^ r
    | Ftyp_fun(rgns, ts, ret) ->
	let rgns' = string_of_rgns rgns in
	let ts' = sep_by ", " string_of_typ ts in
	(match ret with
	  | None -> "<" ^ rgns' ^ ">(" ^ ts' ^ ")"
	  | Some t -> string_of_typ t ^ " <" ^ rgns' ^ ">(" ^ ts' ^ ")" 
	)
    | Ftyp_ptrU (sz, r) -> "FU(" ^ string_of_int sz ^ ")*" ^ r

let string_of_ftyps ts =
  sep_by ", " string_of_ftyp ts

let string_of_const c =
  match c with
    | Const_null -> "null"
    | Const_nullU -> "nullU"
    | Const_float(f) -> string_of_float f
    | Const_double(d) -> string_of_float d
    | Const_int(sz, i) -> string_of_int i ^ ":@" ^ (string_of_int (sz + 1))
    | Const_fun(l) -> l
    | Const_undef(t) -> "UNDEF(" ^ string_of_ftyps t ^ ")"
    | Const_baddr(l1, l2) -> "BADDR(" ^ l1 ^ ", " ^ l2 ^ ")"

let string_of_op o =
  match o with
    | Op_reg x -> "%" ^ x
    | Op_const c -> string_of_const c

let string_of_ops os =
  sep_by ", " string_of_op os

let string_of_insn i =
  let f = fun x -> "%"^x in
  match i with
    | Insn_binop(x, bop, o1, o2) -> f x ^ " = " ^ string_of_binop bop ^ " " ^ string_of_op o1 ^ " " ^ string_of_op o2
    | Insn_fbinop(x, fop, o1, o2) -> f x ^ " = " ^ string_of_fbinop fop ^ " " ^ string_of_op o1 ^ " " ^ string_of_op o2
    | Insn_icmp(x, c, o1, o2) -> f x ^ " = " ^ string_of_cond c ^ " " ^ string_of_op o1 ^ " " ^ string_of_op o2
    | Insn_fcmp(x, fc, o1, o2) -> f x ^ " = " ^ string_of_fcond fc ^ " " ^ string_of_op o1 ^ " " ^ string_of_op o2
    | Insn_select(x, t1, o1, t2, o2, t3, o3) -> f x ^ " = select " ^ string_of_typ t1 ^ " " ^ string_of_op o1 ^ " " ^ string_of_typ t2 ^ " " ^ string_of_op o2 ^ " " ^ string_of_typ t3 ^ " " ^ string_of_op o3 
    | Insn_load(x, t, o) -> f x ^ " = load " ^ string_of_typ t ^ " " ^ string_of_op o
    | Insn_store(t1, o1, t2, o2) -> "store " ^ string_of_typ t1 ^ " " ^ string_of_op o1 ^ " " ^ string_of_typ t2 ^ " " ^ string_of_op o2
    | Insn_poolcheck(x, r, t, o) -> f x ^ " = poolcheck " ^ r ^ " " ^ string_of_typ t ^ " " ^ string_of_op o
    | Insn_free(t, o) -> "free " ^ string_of_typ t ^ " " ^ string_of_op o
    | Insn_gep(x, t1, o1, t2, o2) -> f x ^ " = gep " ^ string_of_typ t1 ^ " " ^ string_of_op o1 ^ " " ^ string_of_typ t2 ^ " " ^ string_of_op o2
    | Insn_gep1(x, t1, o1, o2) -> f x ^ " = gep1 " ^ string_of_typ t1 ^ " " ^ string_of_op o1 ^ " " ^ string_of_op o2
    | Insn_extractvalue(x, t1, o, t2, c) -> f x ^ " = extractvalue " ^ string_of_typ t1 ^ " " ^ string_of_op o ^ " " ^ string_of_typ t2 ^ " " ^ string_of_const c
    | Insn_insertvalue(x, t1, o1, t2, o2, c) -> f x ^ " = insertvalue " ^ string_of_typ t1 ^ " " ^ string_of_op o1 ^ " " ^ string_of_typ t2 ^ " " ^ string_of_op o2 ^ " " ^ string_of_const c
    | Insn_iconv(x, ic, t1, o, t2) -> f x ^ " = " ^ string_of_iconv ic ^ " " ^ string_of_typ t1 ^ " " ^ string_of_op o ^ " " ^ string_of_typ t2
    | Insn_fconv(x, fc, t1, o, t2) -> f x ^ " = " ^ string_of_fconv fc ^ " " ^ string_of_typ t1 ^ " " ^ string_of_op o ^ " " ^ string_of_typ t2
    | Insn_bitcast(x, t1, o, t2) -> f x ^ " = bitcast " ^ string_of_typ t1 ^ " " ^ string_of_op o ^ " " ^ string_of_typ t2
    | Insn_ptrtoint(x, t1, o, t2) -> f x ^ " = ptrtoint " ^ string_of_typ t1 ^ " " ^ string_of_op o ^ " " ^ string_of_typ t2
    | Insn_inttoptr(x, t1, o, t2) -> f x ^ " = inttoptr " ^ string_of_typ t1 ^ " " ^ string_of_op o ^ " " ^ string_of_typ t2
    | Insn_gepU(x, t, o1, o2) -> f x ^ " = gepU " ^ string_of_typ t ^ " " ^ string_of_op o1 ^ " " ^ string_of_op o2
    | Insn_poolcheckU(x, r, sz, o) -> f x ^ " = poolcheckU " ^ r ^ " " ^ string_of_int sz ^ " " ^ string_of_op o
    | Insn_exit -> "exit" 

let string_of_opcode op =
  match op with
    | Opcode_unknown str -> str

let string_of_nd nd =
  let f = fun x -> "%"^x in
  match nd with
    | Insn_call(x, t, o, rgns, os, l) ->
	begin
	  match (x, t) with
	    | (Some x, Some t) -> f x ^ " = call " ^ string_of_typ t ^ " " ^string_of_op o ^ " <" ^ string_of_rgns rgns ^ ">(" ^ string_of_ops os ^ ") " ^ l
	    | (None, None) -> "call " ^ string_of_op o ^ " <" ^ string_of_rgns rgns ^ ">(" ^ string_of_ops os ^ ") " ^ l
	    | (_, _) -> failwith "ill-formed call"
	end
    | Insn_malloc(x, t, r, o, l) -> 
	begin
	  match t with
	    | Some t -> f x  ^ " = poolalloc " ^ string_of_typ t ^ " " ^ r ^ " " ^ string_of_op o ^ " " ^ l
	    | None -> f x ^ " = poolallocU " ^ r ^ " " ^ string_of_op o ^ " " ^ l
	end
    | Insn_unsafe_call(xt, op, os, l) ->
	begin
	  match xt with
	    | Some (x, t) -> f x ^ " = unsafe_call " ^ string_of_typ t ^ " " ^ string_of_opcode op ^ " " ^ string_of_ops os ^ " " ^ l
	    | None -> "unsafe_call " ^ string_of_opcode op ^ " " ^ string_of_ops os ^ " " ^ l
	end
	  

let string_of_term tm =
  match tm with
    | Insn_return(t, o) -> "ret " ^ string_of_typ t ^ " " ^ string_of_op o
    | Insn_return_void -> "ret"
    | Insn_br_uncond(l) -> "br " ^ l
    | Insn_br (o, l1, l2) -> "br " ^ string_of_op o ^ " " ^ l1 ^ " " ^ l2
    | Insn_switch(t, o, l, arms) -> "switch " ^ string_of_typ t ^ " " ^ string_of_op o ^ " " ^ l ^ " " ^ sep_by ", " (fun ((t, c), l) -> string_of_typ t ^ " " ^ string_of_const c ^ " " ^ l) arms
	(* ((typ * const) * lab) list *)
    | Insn_indirect_br(t, o, ls) -> "indirectbr " ^ string_of_typ t ^ " " ^ string_of_op o ^ " " ^ sep_by ", " (fun x -> x) ls
    | Insn_unreachable -> "unreachable"

let string_of_nd_term nt =
  match nt with
    | Insn_nd nd -> string_of_nd nd
    | Insn_term tm -> string_of_term tm

let string_of_phi p =
  let f = fun x -> "%"^x in
  match p with
    | Insn_phi(x, t, arms) -> f x ^ " = phi " ^ string_of_typ t ^ " " ^ "[" ^ sep_by ", " (fun (o, l) -> string_of_op o ^ " " ^ l) arms ^ "]"
	(* (operand * lab) list *)

let string_of_phis ps =
  sep_by "\n" string_of_phi ps

let string_of_insns is =
  sep_by "\n" string_of_insn is

let string_of_phis2 indent ps =
  sep_by "\n" (fun p -> indent ^ string_of_phi p) ps

let string_of_insns2 indent is =
  sep_by "\n" (fun i -> indent ^ string_of_insn i) is

let string_of_blk b =
  let phi_sep = if List.length b.b_phis = 0 then "" else "\n" in
  let insn_sep = if List.length b.b_insns = 0 then "" else "\n" in
  b.b_lab ^ ":\n" ^
    string_of_phis2 "  " b.b_phis ^ phi_sep ^
    string_of_insns2 "  " b.b_insns ^ insn_sep ^
    "  " ^ string_of_nd_term b.b_nd_term

let string_of_blks bs =
  sep_by "\n" string_of_blk bs

let string_of_rgntyps rts =
  "<" ^ sep_by ", " (fun (x, t) -> x ^ " " ^ string_of_typ t) rts ^ ">"

let string_of_sig params ts =
  if List.length params <> List.length ts
  then failwith "parameter and signature do not match"
  else "(" ^ sep_by ", " (fun (x, t) -> string_of_typ t ^ " %" ^ x) (List.combine params ts) ^ ")"

let string_of_fun f =
  let ret = 
    match f.f_ret with
      | Some t -> string_of_typ t
      | None -> "void" in
  let body_sep = if List.length f.f_body = 0 then "" else "\n" in
  ret ^ " " ^ f.f_lab ^ string_of_rgntyps f.f_prgn ^ 
    string_of_sig f.f_params f.f_sig ^ " {\n" ^
    string_of_rgntyps f.f_lrgn ^ body_sep ^
    string_of_blks f.f_body ^ "\n}\n"

let string_of_funs fs =
  sep_by "\n" string_of_fun fs

let string_of_gprgns gprgns = 
  sep_by ", " (fun (r, t) -> r ^ ": " ^ string_of_typ t) gprgns 

let string_of_globsM globsM = 
  SMap.fold (fun k v acc -> k ^ ": " ^ string_of_typ v ^ "\n" ^ acc) globsM ""

let string_of_tenv tenv = 
  SMap.fold (fun k (ts, rs) acc -> k ^ "<" ^ string_of_rgns rs ^ ">{" ^ string_of_typs ts ^ "}\n" ^ acc) tenv ""
