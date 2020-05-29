open Llvm
open Utility
open Iast

(* debugging functions *)
let debug = ref true
let log str =
  if (!debug) then print_endline str else ()

let st = SlotTracker.slotTracker()
let getGlobalSlot = SlotTracker.getGlobalSlot st
let getLocalSlot = SlotTracker.getLocalSlot st
let clearSlotTracker() = SlotTracker.reset st

let name v : string = getLocalSlot v
let gname v : string = 
  let name = getGlobalSlot v in
  if contains name "Pool" then
    name
  else
    "G" ^ name

(* Need to rewrite phi nodes with new vars in varsM since they catch all back-edges. *)

(*----------------------------------------------------------------------------*)
(* State *)

let poolTypM : SCast.typ SMap.t ref = ref SMap.empty
let poolArg : (string list) ref = ref []    (* pools for function's arguments *)
let frtyp : SCast.typ option ref = ref None (* function's return type *)
let localpool = ref []                      (* function's local pools *)

(* Unsafe calls that have been validated. *)
let unsafeValidate : S.t ref = ref S.empty

(* Keeps track of the last label when we split up a block for phi rewrites. *)
let labM : string SMap.t ref = ref SMap.empty

let currFunc : string ref = ref ""
let currLab : string ref = ref ""
let predLabs : string list ref = ref []

let preds = G.graph()
let modify_preds l1 l2 = 
  G.add_edge preds l1 l2

(* Keeps track of potentially constant values in a function. *)
let cvalM : int SMap.t ref = ref SMap.empty

(* Keeps track of checked vars. *)
let valid : S.t ref = ref S.empty
let reset_valid() = valid := S.empty

let modify_valid x = 
  valid := S.add x !valid

let is_valid x = 
  S.mem x !valid

(* Copy-propogation metadata, mapping bitcast assignment variables to original. *)
let varsM : string SMap.t ref = ref SMap.empty

(* Keeps track of aliases var -> (region, alias) *)
let checkaliasM : (string * SCast.operand) SMap.t ref = ref SMap.empty
let reset_checkaliasM() = checkaliasM := SMap.empty

let modify_checkaliasM x r o = 
  checkaliasM := SMap.add x (r, o) !checkaliasM

let checkvarsM : (string * string) VMap.t ref = ref VMap.empty
let reset_checkvarsM() = checkvarsM := VMap.empty

let checkphis : (string * ((SCast.operand * SCast.lab) list)) list ref = ref []
let reset_checkphis() = checkphis := [] 

let varc = counter()
let fresh_var() =
  let tmp = fresh varc in
  "check-" ^ string_of_int tmp

(*----------------------------------------------------------------------------*)
let clearUnsafeValidate() = unsafeValidate := S.empty
let clearCval() = cvalM := SMap.empty
let clearLocalPool() = localpool := []
let clearVars() = varsM := SMap.empty
let clearLab() = labM := SMap.empty
let clearFrtyp() = frtyp := None

let update_cval x o = 
  match o with
    | SCast.Op_const (SCast.Const_int(_, i')) -> 
	cvalM := SMap.add x i' !cvalM 
    | _ -> () 

(*----------------------------------------------------------------------------*)
(* Inference State *)

let tvarc = counter() (* type variable counter *)
let fresh_tvar fname =
  let tmp = fresh tvarc in
  (fname, "TV" ^ string_of_int tmp)

let svarc = counter() (* size variable counter *)
let fresh_svar fname =
  let tmp = fresh svarc in
  (fname, "SV" ^ string_of_int tmp)

(* Hash cons for program var x *)
let tvarM : tvar VMap.t ref = ref VMap.empty
let get_update_tvar fname x = 
  try VMap.find (fname, x) !tvarM 
  with _ -> 
    let tv = fresh_tvar fname in
    tvarM := VMap.add (fname, x) tv !tvarM ;
    tv

let gamma : tipe VMap.t ref = ref VMap.empty     (* (func, program var) -> tipe *)
let delta : tipe VMap.t ref = ref VMap.empty     (* (func, region var) -> (size * tipe) *)
let kappa : sc_constraint2 list ref = ref []     (* set of constraints *)
let gkappa : sc_constraint2 list ref = ref []    (* global constraints *)
let callsites : ((tipe * (tipe list)) list) SMap.t ref = ref SMap.empty (* function call sites *)

let _DEFAULT_TYP = SCast.Typ_int(31)
let _GLOBAL = "G"
let _RET = "ret"

let modify_gamma x t =
  modify_vmap gamma x t

let read_gamma fname x = 
  try VMap.find (fname, x) !gamma
  with Not_found ->
    VMap.find (_GLOBAL, x) !gamma

let modify_delta x t =
  modify_vmap delta x t

let modify_kappa l c =
  kappa := (l, c) :: !kappa

let modify_gkappa l c =
  gkappa := (l, c) :: !gkappa

let put_callsites fname ts = 
  callsites := SMap.add fname ts !callsites

let modify_callsites fname rs ts = 
  let ts' = SMap.find fname !callsites in
  let ts'' = List.map (fun ((t', ts'), t) -> (t', (Tipe_scheme(rs, t)) :: ts')) (List.combine ts' ts) in
  callsites := SMap.add fname ts'' !callsites

let callsites_constraints() =
  SMap.fold 
    (fun k ts acc -> 
       (List.fold_left 
	  (fun acc (t, ts) -> 
	     if List.length ts = 0 then
	       acc
	     else
	       ("call", Tipe_eq(t, Tipe_join ts)) :: acc
	  ) [] ts
       ) @ acc
    ) !callsites []

let string_of_callsites callsites = 
  SMap.fold
    (fun k ts acc ->
       (List.fold_left
	  (fun acc (t, ts) ->
	     string_of_tipe t ^ " = " ^ string_of_tipe (Tipe_join ts) ^ ", " ^ acc
	  ) "" ts
       ) ^ "\n" ^ acc
    ) callsites "" 

let gpools = ref []                         (* global pools *)
let modify_gpools x t = 
  if contains x "GlobalPool" then
    ( gpools := x :: !gpools ; 
      modify_delta (_GLOBAL, x) t
    )

let gvars = ref []
let modify_gvars g x =
  match classify_type (type_of g) with
    | TypeKind.Function -> ()
    | _ -> 
	if not (contains x "GlobalPool") then
	  gvars := x :: !gvars 

let fresh_list fname n =
  let rec fresh_list n acc =
    if n = 0 then 
      acc
    else 
      ( let tv = fresh_tvar fname in
	fresh_list (n - 1) (tv :: acc)
      )
  in
    fresh_list n []

let rec aggregate_constraints fname t tv =
  (* log ("aggregate: " ^ string_of_lltype t) ; *)
  match classify_type t with
    | TypeKind.Struct ->
	let ts = Array.to_list (struct_element_types t) in
	let tvs = fresh_list fname (List.length ts) in
	let tvs' = List.map (fun x -> Tipe_tvar x) tvs in
	let tvs'' = List.map (fun (t, tv) -> aggregate_constraints fname t tv) (List.combine ts tvs) in
	modify_kappa "struct" (Tipe_eq(Tipe_tvar tv, Tipe_struct tvs')) ;
	(* Tipe_struct(tvs') *)
	Tipe_struct(tvs'')
    | TypeKind.Vector -> 
	let tv' = fresh_tvar fname in
	let t' = aggregate_constraints fname (element_type t) tv' in
	modify_kappa "array" (Tipe_eq(Tipe_tvar tv, Tipe_array(Tipe_tvar tv', vector_size t))) ;
	Tipe_array(t', vector_size t) 
    | TypeKind.Array ->
	let tv' = fresh_tvar fname in
	let t' = aggregate_constraints fname (element_type t) tv' in
	modify_kappa "array" (Tipe_eq(Tipe_tvar tv, Tipe_array(Tipe_tvar tv', array_length t))) ;
	(* Tipe_array(Tipe_tvar tv', array_length t) *)
	Tipe_array(t', array_length t) 
    | _ -> Tipe_tvar(tv)

(*----------------------------------------------------------------------------*)
(* LLVM Utility Functions *)

(* TODO: read this in from the data layout *)
let rec align_typ t : int =
  match classify_type t with
    | TypeKind.Float -> 4
    | TypeKind.Integer -> integer_bitwidth t / 8 
    | TypeKind.Array -> 1
    | TypeKind.Pointer -> 8
    | TypeKind.Struct -> 1
    | TypeKind.Double -> 8
    | TypeKind.Vector -> 1
    | _ -> failwith (string_of_lltype t ^ " not supported in align_typ.")

(* TODO: read this in from the data layout *)
let rec size_typ t : int =
  match classify_type t with
    | TypeKind.Float -> 4
    | TypeKind.Integer -> integer_bitwidth t / 8
    | TypeKind.Array -> (size_typ (element_type t)) * array_length t
    | TypeKind.Pointer -> 8
    | TypeKind.Struct -> 
	Array.fold_left 
	  ( fun acc b -> 
	      let align = align_typ b in
	      size_typ b + (acc mod align) + acc
	  ) 0 (struct_element_types t)
    | TypeKind.Function -> 8
    | TypeKind.Double -> 8
    | TypeKind.Vector -> (size_typ (element_type t)) * vector_size t
    | _ -> failwith (string_of_lltype t ^ " not supported in size_typ.")

let is_phi i : bool =
  match instr_opcode i with 
    | Opcode.PHI -> true 
    | _ -> false

let is_nd i : bool =
  match instr_opcode i with
    | Opcode.Call
    | Opcode.Invoke -> true
    | _ -> false

let is_term i : bool =
  match instr_opcode i with
    | Opcode.Ret
    | Opcode.Br
    | Opcode.Switch
    | Opcode.IndirectBr
    | Opcode.Invalid2
    | Opcode.Unreachable -> true
    | _ -> false

let filter_phis b : llvalue list =
  fold_right_instrs (fun i acc -> if is_phi i then i::acc else acc) b []

let filter_insns b : llvalue list =
  fold_right_instrs (fun i acc -> if not (is_phi i) then i::acc else acc) b []

let get_llptr_typ t =
  match classify_type t with
    | TypeKind.Pointer -> element_type t
    | _ -> failwith "Expected pointer type but none found in get_llptr_typ."

let get_base_typ t =
  match classify_type t with
    | TypeKind.Integer -> Some (Tipe_int (integer_bitwidth t - 1))
    | TypeKind.Float -> Some (Tipe_float)
    | _ -> None

let rec index_typ t os = 
  match os with
    | [] -> t
    | (SCast.Op_const (SCast.Const_int(_, i)))::os -> 
	(match classify_type t with
	   | TypeKind.Struct ->
	       let ts = struct_element_types t in
	       index_typ (ts.(i)) os
	   | TypeKind.Array -> index_typ (element_type t) os
	   | _ -> failwith (string_of_lltype t ^ " not struct or array in index_typ.")
	)
    | SCast.Op_reg x::os ->
	(match classify_type t with
	   | TypeKind.Array -> index_typ (element_type t) os
	   | _ -> failwith "Expected array but none found in index_typ."
	)
    | _ -> failwith "Expected constant int or reg but none found in index_typ."

let size_typs_upto ts idx = 
  snd (List.fold_left (fun (i, acc) t -> 
			 if i < idx then
			   (i + 1, size_typ t + acc)
			 else
		      (i + 1, acc)
		      ) (0, 0) ts)

(* works with arbitrary numbers iff its not a gep of 0, 0, which aliases ... *)
let offset_typ scale t os = 
  let rec go t os (c, rs) = 
    match os with
    | [] -> (c, List.rev rs)
    | (SCast.Op_const (SCast.Const_int(_, i)))::os -> 
	(match classify_type t with
	   | TypeKind.Struct -> 
	       let ts = struct_element_types t in
	       let off = if scale then size_typs_upto (Array.to_list ts) i else i in
	       go (ts.(i)) os (c + off, rs)
	   | TypeKind.Vector
	   | TypeKind.Array -> go (element_type t) os (c + i, rs)
	   | _ -> failwith (string_of_lltype t ^ " not struct or array in offset_typ.")
	)
    | SCast.Op_reg x::os ->
	(match classify_type t with
	   | TypeKind.Vector
	   | TypeKind.Array -> go (element_type t) os (c, (SCast.Op_reg x :: rs))
	   | _ -> failwith "Expected array but none found in offset_typ."
	)
    | _ -> failwith "Expected constant int or reg but none found in offset_typ."
  in
    go t os (0, [])

(* Ok, so we need to recurse on the lltyp, and not index if lltyp has a name *)
let rec index_tipe skip llt t os =
  (* log ("indexing: " ^ string_of_tipe t) ; *)
  match os with
    | [] -> t
    | (SCast.Op_const (SCast.Const_int(_, i)))::os -> 
	(match classify_type llt with
	   | TypeKind.Struct -> 
	       let ts = struct_element_types llt in
	       (match struct_name llt with
		  | None -> 
		      (match t with
			 | Tipe_struct ts' -> index_tipe true (ts.(i)) (List.nth ts' i) os
			 | _ -> failwith "Expected struct in index_tipe."
		      )
		  | Some s -> 
		      (match t with
			 | Tipe_struct ts' -> 
			     if skip then index_tipe true (ts.(i)) t os else index_tipe true (ts.(i)) (List.nth ts' i) os
			 | _ -> failwith "Expected struct in index_tipe."
		      )
	       )
	   | TypeKind.Vector
	   | TypeKind.Array -> 
	       (match t with
		  | Tipe_array(t, _) -> index_tipe true (element_type llt) t os
		  | _ -> failwith "Expected array in index_tipe."
	       )
	   | _ -> failwith (string_of_tipe t ^ " not struct or array in index_tipe.")
	)
    | SCast.Op_reg x::os ->
	(match classify_type llt with
	   | TypeKind.Vector
	   | TypeKind.Array -> 
	       (match t with 
		  | Tipe_array(t, _) -> index_tipe true (element_type llt) t os
		  | _ -> failwith "Expected array in index_tipe."
	       )
	   | _ -> failwith "Expected array but none found in index_tipe."
	)
    | _ -> failwith "Expected constant int or reg but none found in index_tipe."

let rec lltyp2tipe fname lt =
  match classify_type lt with
    | TypeKind.Float -> Tipe_float
    | TypeKind.Double -> Tipe_double
    | TypeKind.Integer -> Tipe_int(integer_bitwidth lt - 1)
    | TypeKind.Function -> Tipe_tvar (fresh_tvar fname)
    | TypeKind.Struct -> Tipe_struct(List.map (lltyp2tipe fname) (Array.to_list (struct_element_types lt)))
    | TypeKind.Array -> Tipe_array(lltyp2tipe fname (element_type lt), array_length lt)
    | TypeKind.Pointer -> Tipe_tvar (fresh_tvar fname)
    | TypeKind.Label -> Tipe_int 63
    | TypeKind.Vector -> Tipe_array(lltyp2tipe fname (element_type lt), vector_size lt)
    | _ -> failwith ("lltyp2tipe unsupported: " ^ string_of_lltype lt)

let index_struct_tipe t i = 
  match t with
    | Tipe_struct ts -> List.nth ts i
    | _ -> failwith ("index_struct_tipe expected struct tipe but: " ^ string_of_tipe t ^ " found instead") 

(*----------------------------------------------------------------------------*)
(* Other utility functions *)

let op_contains o str : bool =
  match o with
    | SCast.Op_reg x -> contains x str
    | SCast.Op_const c ->
	match c with
	  | SCast.Const_fun f -> contains f str
	  | _ -> false

let op2id o : SCast.id =
  match o with
    | SCast.Op_reg x -> x
    | SCast.Op_const c -> 
	match c with
	  | SCast.Const_fun f -> f
	  | _ -> failwith ("Expected a name but none found in op2id: " ^ (Pprint.string_of_op o))

let op2pool o : SCast.id = 
  match o with
    | SCast.Op_reg x -> op2id o
    | SCast.Op_const c -> "NA"

let is_pool_cast t : bool =
  match t with
    | SCast.Typ_ptr(SCast.Typ_array(_, 92), _) -> true
    | _ -> false

let is_pool_descriptor t : bool = 
  match t with
    | SCast.Typ_array(_, 92) -> true
    | _ -> false

let is_pool o t : bool =
  match o with
    | SCast.Op_reg x -> contains x "Pool" || contains x "PD" || is_pool_cast t
    | SCast.Op_const _ -> is_pool_cast t

let is_unknown_pool pool : bool =
  let t = 
    try SMap.find pool !poolTypM 
    with Not_found -> SCast.Typ_int(63)
  in
    match t with
      | SCast.Typ_int(7) -> true
      | _ -> false

let is_array t : bool = 
  match t with
    | SCast.Typ_array(_, _) -> true
    | _ -> false

let is_base_tipe t = 
  match t with
    | SCast.Typ_int _ -> true
    | SCast.Typ_float -> true
    | SCast.Typ_double -> true
    | _ -> false

let to_base_tipe t =
  match t with
    | SCast.Typ_int(sz) -> Tipe_int(sz)
    | SCast.Typ_float -> Tipe_float
    | SCast.Typ_double -> Tipe_double
    | _ -> failwith ("not a base type: " ^ Pprint.string_of_typ t)

let is_undef o = 
  match o with
    | SCast.Op_const (SCast.Const_undef _) -> true
    | _ -> false

let const_tipe c =
  match c with
    | SCast.Const_null -> Some (Tipe_int 63)
    | SCast.Const_nullU -> Some (Tipe_int 63)
    | SCast.Const_int(sz, _) -> Some (Tipe_int sz)
    | SCast.Const_float _ -> Some (Tipe_float)
    | SCast.Const_double _ -> Some (Tipe_double)
    | SCast.Const_undef(SCast.Ftyp_int(sz) :: []) -> Some (Tipe_int sz)
    | SCast.Const_undef(SCast.Ftyp_float :: []) -> Some (Tipe_float)
    | SCast.Const_undef(SCast.Ftyp_double :: []) ->  Some (Tipe_double)
    | _ -> None
      

(*----------------------------------------------------------------------------*)
let update_vars' (x:string) (x':string) : unit =
  (* map x and everything that used to map to x to x' *)
  varsM := SMap.add x x' !varsM ; 
  varsM := SMap.fold (fun k v acc -> if v = x then SMap.add k x' acc else acc) !varsM !varsM 

let update_vars (x:string) (o:SCast.operand) : unit =
  match o with
    | SCast.Op_reg x' -> update_vars' x x'
    | SCast.Op_const c ->
	match c with
	  | SCast.Const_fun x' -> update_vars' x x'
	  | _ -> ()

let string_of_checkvars cM = 
  VMap.fold (fun (l, x) (l', x') acc -> l ^ "." ^ x ^ ": " ^ l' ^ "." ^ x' ^ "    " ^ acc) cM ""

let string_of_vars cM = 
  SMap.fold (fun k v acc -> k ^ ": " ^ v ^ "    " ^ acc) cM ""

let update_checkvars (x:string) (x':string) : unit =
  (* map x and everything that used to map to x to x' *)
  checkvarsM := VMap.add (!currLab, x) (!currLab, x') !checkvarsM ; 
  checkvarsM := VMap.fold (fun k v acc -> 
			     if v = (!currLab, x) then 
			       VMap.add k (!currLab, x') acc 
			     else acc
			  ) !checkvarsM !checkvarsM

let constraints_phi fname x arms =
  log "constraints phi" ; 
  let tv = get_update_tvar fname x in
  let ts = List.fold_left
    (fun acc (o, b) ->
       match o with
	 | SCast.Op_reg x ->
	     (try 
		let t = read_gamma fname x in
		  t :: acc
	      with _ ->
		let tv' = get_update_tvar fname x in
		  Tipe_tvar tv' :: acc
	     )
	 | SCast.Op_const c -> 
	     match const_tipe c with
	       | Some t -> t :: acc
	       | None -> acc
    ) [] arms
  in
    modify_gkappa "phi" (Tipe_eq(Tipe_tvar tv, Tipe_join ts))

let idgen' clab (x:string) : string = 
  try snd (VMap.find (clab, x) !checkvarsM)
  with Not_found ->
    ( if List.length !predLabs = 1 then
	( if VMap.mem ((List.hd !predLabs), x) !checkvarsM then
	    snd (VMap.find ((List.hd !predLabs), x) !checkvarsM)
	  else
	    x
	)
      else if List.length !predLabs >= 2 then
	( if List.fold_left (fun acc l -> VMap.mem (l, x) !checkvarsM && acc) true !predLabs then
	    ( let arms = List.fold_left 
		(fun acc l -> (SCast.Op_reg (snd (VMap.find (l, x) !checkvarsM)), l) :: acc
		) [] !predLabs
	      in
	      let phiv = fresh_var() in
		checkphis := (phiv, arms) :: !checkphis ; 
		update_vars x (SCast.Op_reg phiv) ; 
		let tv = get_update_tvar !currFunc phiv in
		modify_gamma (!currFunc, phiv) (Tipe_tvar tv) ; 
		constraints_phi !currFunc phiv arms ; 
		phiv
	    )
	  else
	    x
	)
      else x
    )

let idgen (x:string) : string = 
  try idgen' !currLab (SMap.find x !varsM)
  with Not_found -> idgen' !currLab x

let idgen2 clab (x:string) : string = 
  try idgen' clab (SMap.find x !varsM)
  with Not_found -> idgen' clab x

(*----------------------------------------------------------------------------*)
(* Meta-data string parsing *)

let rec parse_pstr (pstr:string) : string list =
  let i = try String.index pstr ',' with Not_found -> -1 in
  if i = -1 then 
    [pstr]
  else
    let s = String.sub pstr 0 i in
    s :: parse_pstr (String.sub pstr (i + 2) (String.length pstr - (i + 2)))

let get_pstr i : string =
  match metadata i (mdkind_id (global_context()) "safecode") with
    | Some md -> 
	let v = operand md 0 in
	(match get_mdstring v with
	   | Some s -> s
	   | None -> failwith "Expected metadata string but none found in get_pstr."
	)
    | None -> 
	"NA, NA, NA, NA, NA, NA, NA, NA, NA, NA, NA, NA, NA, NA, NA"

(*----------------------------------------------------------------------------*)
(* Dummy type translation *)
let rec translate_typ pool t : SCast.typ =
  match classify_type t with
    | TypeKind.Float -> SCast.Typ_float
    | TypeKind.Double -> SCast.Typ_double
    | TypeKind.Integer -> SCast.Typ_int(integer_bitwidth t - 1)
    | TypeKind.Function -> SCast.Typ_fun([], [], None)
    | TypeKind.Struct -> SCast.Typ_name("struct", [])
    | TypeKind.Array -> SCast.Typ_array(translate_typ pool (element_type t), array_length t)
    | TypeKind.Pointer -> SCast.Typ_ptr(translate_typ "" (element_type t), pool)
    | TypeKind.Label -> SCast.Typ_int(63)
    | TypeKind.Vector -> SCast.Typ_array(translate_typ pool (element_type t), vector_size t)
    | _ -> failwith ("translate_typ unsupported: " ^ string_of_lltype t)

let translate_cexpr ce : SCast.operand = 
  match constexpr_opcode ce with
    | Opcode.BitCast -> 
	(match classify_value (operand ce 0) with
	   | ValueKind.GlobalVariable -> SCast.Op_reg(gname (operand ce 0))
	   | _ -> SCast.Op_reg(name (operand ce 0))
	)
    | Opcode.GetElementPtr -> 
	(match classify_value (operand ce 0) with
	   | ValueKind.GlobalVariable -> SCast.Op_reg(gname (operand ce 0))
	   | _ -> SCast.Op_reg(name (operand ce 0)) (* only works for 0, 0 *)
	)
    | _ -> SCast.Op_reg ("cexpr")

let rec translate_undef_ftyps t = 
  log ("UNDEF " ^ string_of_lltype t) ; 
  match classify_type t with
    | TypeKind.Float -> SCast.Ftyp_float :: []
    | TypeKind.Integer -> SCast.Ftyp_int(integer_bitwidth t - 1) :: [] 
    | TypeKind.Double -> SCast.Ftyp_double :: []
    | TypeKind.Struct -> 
	let ts = struct_element_types t in 
	let ts' = Array.to_list ts in
	List.fold_left (fun acc t -> acc @ translate_undef_ftyps t) [] ts'
    | TypeKind.Array ->
	let t' = translate_undef_ftyps (element_type t) in
	let rec go n =
	  if n = 0 then [] else t' @ go (n - 1)
	in
	go (array_length t)
    | TypeKind.Vector ->
	let t' = translate_undef_ftyps (element_type t) in
	let rec go n =
	  if n = 0 then [] else t' @ go (n - 1)
	in
	go (vector_size t)
    | _ -> SCast.Ftyp_int(63) :: []

let translate_op pool o : SCast.operand =
  match classify_value o with
    | ValueKind.NullValue -> failwith "translate_op unsupported: nullvalue"
    | ValueKind.Argument -> SCast.Op_reg (idgen (name o))
    | ValueKind.BasicBlock -> SCast.Op_reg (idgen (name o))
	(* failwith "translate_op unsupported: basicblock" *)
    | ValueKind.InlineAsm -> failwith "translate_op unsupported: inlineasm"
    | ValueKind.MDNode -> failwith "translate_op unsupported: mdnode"
    | ValueKind.MDString -> 
	(match get_mdstring o with
	  | Some s -> SCast.Op_reg s 
	  | None -> failwith "Expected metadata string but none found in translate_op."
	) 
    | ValueKind.BlockAddress -> failwith "translate_op unsupported: blockaddress"
    | ValueKind.ConstantAggregateZero -> failwith "translate_op unsupported: constant aggregate zero"
    | ValueKind.ConstantArray -> 
	log (string_of_int (num_operands o)) ; 
	log (string_of_int (num_operands (operand o 0))) ; 
	failwith "translate_op unsupported: constant array"
    | ValueKind.ConstantExpr -> translate_cexpr o
    | ValueKind.ConstantFP -> 
	(match classify_type (type_of o) with
	   | TypeKind.Float -> SCast.Op_const (SCast.Const_float(1.0))
	   | TypeKind.Double -> SCast.Op_const (SCast.Const_double(1.0))
	   | _ -> SCast.Op_const (SCast.Const_double(1.0))
	)
    | ValueKind.ConstantInt -> 
	(match int64_of_const o with
	  | Some i -> SCast.Op_const (SCast.Const_int((integer_bitwidth (type_of o)) - 1, Int64.to_int i )) 
	  | None -> SCast.Op_const (SCast.Const_int((integer_bitwidth (type_of o)) - 1, 42))
	)
    | ValueKind.ConstantPointerNull -> 
	if is_unknown_pool pool then
	  SCast.Op_const (SCast.Const_nullU)
	else
	  SCast.Op_const (SCast.Const_null)
    | ValueKind.ConstantStruct -> failwith "translate_op unsupported: constant struct"
    | ValueKind.ConstantVector -> failwith "translate_op unsupported: constant vector"
    | ValueKind.Function -> 
	SCast.Op_const (SCast.Const_fun (getGlobalSlot o))
    | ValueKind.GlobalAlias -> failwith "translate_op unsupported: globalalias"
    | ValueKind.GlobalVariable -> SCast.Op_reg (gname o)
    | ValueKind.UndefValue -> SCast.Op_const (SCast.Const_undef(translate_undef_ftyps (type_of o)))
    | ValueKind.Instruction _ -> SCast.Op_reg (idgen (name o)) 

(*----------------------------------------------------------------------------*)
(* Pool offset is 1 greater than operand offset because the pool list always 
 * contain a slot for the assignment variable. *)

let translate_op_typ pool o : (SCast.operand * SCast.typ) = 
  let o' = translate_op pool o in
  (o', translate_typ pool (type_of o))

let opgen1 pools i =
  if num_operands i != 1
  then failwith ("open1 expected 1 operand.")
  else translate_op_typ (List.nth pools 1) (operand i 0)
  
let opgen2 pools i =
  if num_operands i != 2 
  then failwith ("expected 2 operands")
  else 
    let (o1, t1) = translate_op_typ (List.nth pools 1) (operand i 0) in
    let (o2, t2) = translate_op_typ (List.nth pools 2) (operand i 1) in
    (o1, t1, o2, t2)

let opgenn pools i = 
  let rec opgenn' i n =
    if num_operands i = n then []
    else translate_op_typ (List.nth pools (n + 1)) (operand i n) :: opgenn' i (n + 1)
  in
    opgenn' i 0

(*----------------------------------------------------------------------------*)
let translate_icmp ic =
  match ic with
    | Icmp.Eq -> SCast.Cond_eq
    | Icmp.Ne -> SCast.Cond_ne
    | Icmp.Ugt -> SCast.Cond_ugt
    | Icmp.Uge -> SCast.Cond_uge
    | Icmp.Ult -> SCast.Cond_ult
    | Icmp.Ule -> SCast.Cond_ule
    | Icmp.Sgt -> SCast.Cond_sgt
    | Icmp.Sge -> SCast.Cond_sge
    | Icmp.Slt -> SCast.Cond_slt
    | Icmp.Sle -> SCast.Cond_sle

let translate_fcmp fc =
  match fc with
    | Fcmp.False -> SCast.Fcond_false
    | Fcmp.Oeq -> SCast.Fcond_oeq
    | Fcmp.Ogt -> SCast.Fcond_ogt
    | Fcmp.Oge -> SCast.Fcond_oge
    | Fcmp.Olt -> SCast.Fcond_olt
    | Fcmp.Ole -> SCast.Fcond_ole
    | Fcmp.One -> SCast.Fcond_one
    | Fcmp.Ord -> SCast.Fcond_ord
    | Fcmp.Uno -> SCast.Fcond_uno
    | Fcmp.Ueq -> SCast.Fcond_ueq
    | Fcmp.Ugt -> SCast.Fcond_ugt
    | Fcmp.Uge -> SCast.Fcond_uge
    | Fcmp.Ult -> SCast.Fcond_ult
    | Fcmp.Ule -> SCast.Fcond_ule
    | Fcmp.Une -> SCast.Fcond_une
    | Fcmp.True -> SCast.Fcond_true

(*
let translate_carray o = 
  match classify_value o with
    | ValueKind.ConstantArray -> 
	log "HERE" ; 
	log (string_of_int (num_operands o)) ; 
	dump_value o ; 
	let o' = translate_op "" (operand o 0) in
	log (Pprint.string_of_op o') ; 
	let rec go i n = 
	  if num_operands i = n then []
	  else translate_op_typ "" (operand i n) :: go i (n + 1)
	in
	  go o 0
    | _ -> failwith "translate_carray not given constant array"
*)

(*----------------------------------------------------------------------------*)
(* Special call emissions *)

let emit_poolalloc fname x t r o l : (SCast.insn list, SCast.insn_nd) sum = 
  let x = 
    match x with
      | Some x -> x
      | None -> failwith "Poolalloc should have assignment variable."
  in
  let sz = 
    match o with
      | SCast.Op_const(SCast.Const_int(_, sz')) -> sz'
      | _ ->
	  try SMap.find (op2id o) !cvalM 
	  with _ -> 0
  in
  (* 
   * D(r) = Some n    TV = {TV1; ...; TVn}
   * ---------------------------------------------------------
   * G |- x = poolalloc(r, o) : G[x:TV'][r:TV] @ C[TV' = TV*r]
   *)
  let tv = get_update_tvar fname r in
  (* let tv = fresh_tvar fname in *)
  let tv' = get_update_tvar fname x in
  let n = 1 (* should read this from parsepool *)
    (*
    match SMap.find pool !rmap with
      | Some n -> n
      | None -> 1 
    *)
  in
  ( (if not (VMap.mem (fname, r) !delta) then
       modify_delta (fname, r) (Tipe_tvar tv)
     else
       let t = VMap.find (fname, r) !delta in
	 modify_kappa "poolalloc" (Tipe_eq(Tipe_tvar tv, t)) 
    ) ; 
    modify_gamma (fname, x) (Tipe_tvar tv') ;
    modify_delta (fname, r) (Tipe_tvar tv) ;
    ( if is_unknown_pool r then
	( let szv = fresh_svar fname in
	  modify_kappa "poolallocU" (Tipe_eq(Tipe_tvar tv', Tipe_ptrU(Size_var szv, (fname, r)))) ;
	  modify_kappa "poolallocU" (Size_geq(szv, sz))
	)
      else
	modify_kappa "poolalloc" (Tipe_eq(Tipe_tvar tv', Tipe_ptr(Tipe_tvar tv, (fname, r))))
    ) ; 
    modify_kappa "poolalloc/U" (Tipe_size(Tipe_tvar tv, sz)) ; 
    if n <> 1 then
      ( let tvs = List.map (fun x -> Tipe_tvar x) (fresh_list fname n) in
	  modify_kappa "poolalloc" (Tipe_eq(Tipe_tvar tv, Tipe_struct(tvs))) ;
      )
  ) ; 
  if is_unknown_pool r then
    Inr (SCast.Insn_malloc(x, None, r, SCast.Op_const(SCast.Const_int(63, sz)), l))
  else
    Inr (SCast.Insn_malloc(x, Some _DEFAULT_TYP, r, SCast.Op_const(SCast.Const_int(63, 1)), l)) 

let emit_free o t : (SCast.insn list, SCast.insn_nd) sum =
  (* 
   * ---------------------------------------------------------
   * G |- free x : G @ C
   *)
  Inl ([SCast.Insn_free(t, o)])

let rec emit_poolcheck' fname x r o : SCast.insn list =
  (* 
   * ---------------------------------------------------------
   * G |- poolcheck r x : G[x:TV] @ C[TV = TV'*r]
   *)
  if is_undef o then
    [SCast.Insn_exit]
  else
  let tv = fresh_tvar fname in
  let tv' = fresh_tvar fname in
  if is_unknown_pool r then
    ( let szv = fresh_svar fname in
      modify_kappa "poolcheckU" (Tipe_eq(Tipe_tvar tv, Tipe_ptrU(Size_var szv, (fname, r)))) ;
      modify_kappa "poolcheckU" (Size_geq(szv, 0)) 
    )
  else
    ( modify_kappa "poolcheck" (Tipe_eq(Tipe_tvar tv, Tipe_ptr(Tipe_tvar tv', (fname, r)))) 
    ) ;
  (if not (VMap.mem (fname, r) !delta) then
     modify_delta (fname, r) (Tipe_tvar tv')
  ) ; 
  let x2 = 
    match x with
      | Some x -> x
      | None -> fresh_var() 
  in
  update_checkvars (op2id o) x2 ;
  modify_gamma (fname, x2) (Tipe_tvar tv) ;
  modify_valid x2 ; 
  if is_unknown_pool r then
    ( if SMap.mem (op2id o) !checkaliasM then
	( let (r, o') = SMap.find (op2id o) !checkaliasM in
	  SCast.Insn_poolcheckU(x2, r, 0, o) :: emit_poolcheck' fname None r o'
	)
      else
	[SCast.Insn_poolcheckU(x2, r, 0, o)]
    )
  else
    ( if SMap.mem (op2id o) !checkaliasM then
	( let (r, o') = SMap.find (op2id o) !checkaliasM in
	  SCast.Insn_poolcheck(x2, r, _DEFAULT_TYP, o) :: emit_poolcheck' fname None r o'
	)
      else
	[SCast.Insn_poolcheck(x2, r, _DEFAULT_TYP, o)]
    )
let emit_poolcheck fname x r o =
  Inl (emit_poolcheck' fname x r o)

(* Copy propogation for pchk_getActualValue because it just gets the rewrite pointer? *)
let emit_pchk_actual fname x r o =
  match x with
    | Some x -> 
	emit_poolcheck fname (Some x) r o 
	(* Inl (SCast.Insn_bitcast(x, _DEFAULT_TYP, o, _DEFAULT_TYP)) *)
    | None -> failwith "pchk_getActualValue expects an assignment variable"

(* Copy propogation for boundscheckui since it is always followed by a poolcheck (if used). *)
let emit_boundscheck x o =
  match x with
    | Some x ->
	update_vars x o ;
	Inl ([SCast.Insn_bitcast(x, _DEFAULT_TYP, o, _DEFAULT_TYP)])
    | None -> failwith "Boundscheck expects assignment variable."

let constraints_call fname safe x o rgns os ts =
  if VMap.mem (_GLOBAL, (op2id o)) !gamma then
    match VMap.find (_GLOBAL, (op2id o)) !gamma with
      | Tipe_fun(prgns', ts', t') ->
	  let ts'' = List.map 
	    (fun (o, t) -> 
	       match o with
		 | SCast.Op_reg x ->
		     (try read_gamma fname x
		      with Not_found -> Tipe_tvar (get_update_tvar fname x)
		     )
		 | SCast.Op_const c ->
		     match c with
		       | SCast.Const_null -> Tipe_int(63) (* Tipe_tvar (fresh_tvar fname) *)
		       | SCast.Const_nullU -> Tipe_int(63)
		       | SCast.Const_undef _ -> Tipe_tvar (fresh_tvar fname)
		       | SCast.Const_fun x ->
			   (try read_gamma fname x
			    with Not_found -> Tipe_tvar (get_update_tvar fname x)
			   )
		       | _ -> to_base_tipe t
	    ) (List.combine os ts)
	  in
	  let rs' = List.map (fun r -> (fname, r)) rgns in
	  (match x with
	     | Some x ->
		 let tv' = get_update_tvar fname x in
		 modify_gamma (fname, x) (Tipe_tvar tv') ;
		 if safe then
		   modify_callsites (op2id o) rs' ((Tipe_tvar tv') :: ts'')
		   (* modify_gkappa "call" (Tipe_eq(Tipe_fun(rs', ts'', Some (Tipe_tvar tv')), Tipe_fun(prgns', ts', t'))) *)
		 else
		   modify_callsites (op2id o) rs' [ Tipe_tvar tv' ]
		   (* modify_gkappa "call" (Tipe_eq(Tipe_fun(rs', [], Some (Tipe_tvar tv')), Tipe_fun(prgns', [], t'))) *)
	     | None ->
		 modify_callsites (op2id o) rs' ts''
		 (* modify_gkappa "call" (Tipe_eq(Tipe_fun(rs', ts'', None), Tipe_fun(prgns', ts', t'))) *)
	  )
      | _ -> failwith "call fail"

let special_call fname pools ts c : (SCast.insn list, SCast.insn_nd) sum =
  match c with
    | SCast.Insn_call(x, _, o, rgns, os, l) ->
	log ("id: " ^ match x with Some x -> x | None -> "none") ; 
	log ("name: " ^ Pprint.string_of_op o) ;
	log ("regions: " ^ Pprint.string_of_rgns rgns) ;
	log ("ops: " ^ Pprint.string_of_ops os) ; 
	log ("typs: " ^ Pprint.string_of_typs ts) ; 
	(try
	log (string_of_bool (is_pool (List.nth os 0) (List.nth ts 0)))
	with _ -> () ); 
	if op_contains o "__sc_dbg_poolinit" then
	  ( let pool = List.nth rgns 0 in
	    let t = try SMap.find pool !poolTypM with Not_found -> SCast.Typ_float in
	    ( if not (List.mem (pool, t) !localpool) then
		localpool := (pool, t) :: !localpool 
	    ) ; 
	    Inr c  
	  )
	else if op_contains o "poolcheckui_debug" then
	  ( if List.length os = 5 then 
	      ( let pool = List.nth pools 2 in (* refers to meta-data string offset *)
		let o = List.nth os 0 in
		emit_poolcheck fname x pool o
	      )
	    else if List.length os = 6 then
	      ( let pool = List.nth pools 2 in (* refers to meta-data string offset *)
	        let o = List.nth os 1 in
	        emit_poolcheck fname x pool o 
	      )
	    else
	      failwith "poolcheckui_debug expects at least 5 operands"
	  )
	else if op_contains o "poolcheck_debug" then
	  ( if List.length os = 5 then
	      ( let pool = List.nth pools 2 in
		let o = List.nth os 0 in
		emit_poolcheck fname x pool o
	      )
	    else if List.length os = 6 then 
	      ( let pool = List.nth pools 2 in 
		let o = List.nth os 1 in
		emit_poolcheck fname x pool o 
	      )
	    else
	      failwith "poolcheck expects 6 operands"
	  )
	else if op_contains o "boundscheckui_debug" || op_contains o "boundscheck_debug" then
	  ( if List.length os = 5 then 
	      ( let o = List.nth os 1 in
	        emit_boundscheck x o
	      )
	    else if List.length os = 6 then
	      ( let o = List.nth os 2 in
		emit_boundscheck x o
	      )
	    else
	      failwith "boundscheck(ui)_debug expects at least 5 operands"
	  )
	else if op_contains o "fastlscheck_debug" then
	  ( if List.length os != 7 then failwith "fastlscheck_debug expects 7 operands"
	    else
	      let pool = List.nth pools 1 in
	      let o = List.nth os 0 in
	      emit_poolcheck fname x pool o
	  )
	else if op_contains o "poolcheck_freeui_debug" then
	  ( if List.length os = 5 then 
	      let pool = List.nth pools 2 in 
	      let o = List.nth os 1 in   
	      emit_poolcheck fname x pool o
	    else if List.length os = 4 then
	      let pool = List.nth pools 2 in
	      let o = List.nth os 0 in
	      emit_poolcheck fname x pool o
	    else 
	      failwith "poolcheck_freeui_debug expects either 4 or 5 operands"
	  )
	else if op_contains o "poolfree" then 
	  ( if List.length os != 1 then failwith "poolfree expects 1 operand "
	    else
	      let o = List.nth os 0 in
	      let t = List.nth ts 0 in 
	      emit_free o t
	  )
	else if op_contains o "poolalloc" || op_contains o "poolcalloc" || op_contains o "poolrealloc" then
	  ( let o = List.hd (List.rev os) in
	    let t = List.nth ts 0 in
	    let pool = List.nth rgns 0 in
	    emit_poolalloc fname x t pool o l
	  )
	else if op_contains o "pchk_getActualValue" then
	  ( if List.length os = 1 then
	      let pool = List.nth pools 2 in
	      let o1 = List.nth os 0 in
	      emit_pchk_actual fname x pool o1
	    else if List.length os = 2 then
	      let pool = List.nth pools 2 in
	      let o1 = List.nth os 1 in
	      emit_pchk_actual fname x pool o1
	    else
	      failwith "pchk_getActualValue expects either 1 or 2 operands."
	  )
	else if op_contains o "__assert_rtn" then
	  ( Inl ([SCast.Insn_exit])
	  )
	else if op_contains o "llvm.memset" then
	  ( let pool = List.nth pools 1 in
	    let rgns' = [pool] in
	    Inr (SCast.Insn_call(x, None, o, rgns', os, l))
	  )
	else if op_contains o "llvm.memcpy" then
	  ( Inr (SCast.Insn_unsafe_call(None, SCast.Opcode_unknown(op2id o), os, l))
	  )
	else if op_contains o "llvm.lifetime.start" then
	  ( Inr (SCast.Insn_unsafe_call(None, SCast.Opcode_unknown(op2id o), os, l))
	  )
	else if op_contains o "llvm.lifetime.end" then
	  ( Inr (SCast.Insn_unsafe_call(None, SCast.Opcode_unknown(op2id o), os, l))
	  )
	else if op_contains o "pool_printf" then
	  Inr (SCast.Insn_unsafe_call(None, SCast.Opcode_unknown(op2id o), os, l))
	else if op_contains o "pool_vfprintf_debug" then
	  Inr (SCast.Insn_unsafe_call(None, SCast.Opcode_unknown(op2id o), os, l))
	else if op_contains o "pool_fprintf" then
	  Inr (SCast.Insn_unsafe_call(None, SCast.Opcode_unknown(op2id o), os, l))
	else if op_contains o "__sc_fsparameter" then
	  ( match x with
	      | Some x ->
		  Inr (SCast.Insn_unsafe_call(None, SCast.Opcode_unknown(op2id o), [SCast.Op_reg x] @ os, l))
	      | None -> failwith "__sc_fsparameter expects assignment." 
	  )
	else if op_contains o "__sc_fscallinfo_debug" then
	  ( match x with
	      | Some x ->
		  Inr (SCast.Insn_unsafe_call(None, SCast.Opcode_unknown(op2id o), [SCast.Op_reg x] @ os, l))
	      | None -> failwith "__sc_fscallinfo_debug expects assignment."
	  )
	else if op_contains o "pool___snprintf_chk" then
	  ( match x with
	      | Some x ->
		  Inr (SCast.Insn_unsafe_call(None, SCast.Opcode_unknown(op2id o), [SCast.Op_reg x], l))
	      | None -> failwith "pool___snprintf_chk expects assignment."
	  )
	else if op_contains o "__sc_targetcheck" then
	  ( match x with
	      | Some x ->
		  Inr (SCast.Insn_unsafe_call(Some (x, _DEFAULT_TYP), SCast.Opcode_unknown(op2id o), [SCast.Op_reg x] @ os, l))
	      | None -> failwith "__sc_targetcheck expects assignment."
	  )
	else if op_contains o "__sc_vacallregister" or op_contains o "__sc_varegister" then
	  ( let o' = List.nth os 0 in
	    (try unsafeValidate := S.add (op2id o') !unsafeValidate ; with _ -> ()) ; 
	    Inr (SCast.Insn_unsafe_call(None, SCast.Opcode_unknown(op2id o), [List.nth os 0], l))
	  )
	else if op_contains o "funccheckui_debug" then
	  ( let o' = List.nth os 0 in
	    (try unsafeValidate := S.add (op2id o') !unsafeValidate ; with _ -> ()) ; 
	    Inr (SCast.Insn_unsafe_call(None, SCast.Opcode_unknown(op2id o), [o'], l))
	  )
	else if op_contains o "pool_strcpy_debug" then
	  ( Inr (SCast.Insn_unsafe_call(None, SCast.Opcode_unknown(op2id o), os, l))
	  )
	else if op_contains o "pool_strcmp_debug" then
	  ( match x with
	      | Some x ->
		  let tv = get_update_tvar fname x in
		  modify_gamma (fname, x) (Tipe_tvar tv) ; 
		  Inr (SCast.Insn_unsafe_call(Some (x, _DEFAULT_TYP), SCast.Opcode_unknown(op2id o), os, l))
	      | None -> failwith "pool_strcmp_debug expects assignment"
	  )
	else if op_contains o "pool_memcpy_debug" then
	  ( Inr (SCast.Insn_unsafe_call(None, SCast.Opcode_unknown(op2id o), os, l))
	  )
	else if op_contains o "pool_memset_debug" then
	  ( Inr (SCast.Insn_unsafe_call(None, SCast.Opcode_unknown(op2id o), os, l))
	  )
	else if op_contains o "pool_strstr_debug" then
	  ( match x with
	      | Some x -> 
		  let tv = get_update_tvar fname x in
		  modify_gamma (fname, x) (Tipe_tvar tv) ; 
		  Inr (SCast.Insn_unsafe_call(Some (x, _DEFAULT_TYP), SCast.Opcode_unknown(op2id o), os, l))
	      | None -> Inr (SCast.Insn_unsafe_call(None, SCast.Opcode_unknown(op2id o), os, l))
	  )
	else if op_contains o "pool_sscanf" then
	  ( Inr (SCast.Insn_unsafe_call(None, SCast.Opcode_unknown(op2id o), os, l))
	  )
	else if op_contains o "poolcheckstrui_debug" then
	  ( Inr (SCast.Insn_unsafe_call(None, SCast.Opcode_unknown(op2id o), os, l))
	  )
	else if op_contains o "setjmp" then
	  ( match x with
	      | Some x ->
		  let tv = get_update_tvar fname x in
		  modify_gamma (fname, x) (Tipe_tvar tv) ; 
		  Inr (SCast.Insn_unsafe_call(Some (x, _DEFAULT_TYP), SCast.Opcode_unknown(op2id o), os, l))
	      | None -> failwith "setjmp expects assignment"
	  )
	else if op_contains o "longjmp" then
	  ( Inr (SCast.Insn_unsafe_call(None, SCast.Opcode_unknown(op2id o), os, l))
	  )
	else if op_contains o "_close" then
	  ( match x with
	      | Some x -> Inr (SCast.Insn_unsafe_call(Some (x, _DEFAULT_TYP), SCast.Opcode_unknown(op2id o), os, l))
	      | None -> failwith "_close expects assignment"
	  )
	else if op_contains o "_read" then
	  ( match x with
	      | Some x -> Inr (SCast.Insn_unsafe_call(Some (x, _DEFAULT_TYP), SCast.Opcode_unknown(op2id o), os, l))
	      | None -> failwith "_read expects assignment"
	  )
	else if op_contains o "perror" then
	  ( Inr (SCast.Insn_unsafe_call(None, SCast.Opcode_unknown(op2id o), os, l))
	  )
	    (* this one here just for oldens *)
	else if op_contains o "dealwithargs_clone" then
	  ( match x with
	      | Some x -> Inr (SCast.Insn_unsafe_call(Some (x, _DEFAULT_TYP), SCast.Opcode_unknown(op2id o), os, l))
	      | None -> Inr (SCast.Insn_unsafe_call(None, SCast.Opcode_unknown(op2id o), os, l))
	  ) 
	else 
	  ( if (S.mem (op2id o) !unsafeValidate) then
	      ( let ros = List.map (fun r -> SCast.Op_reg ("rgn." ^ r)) rgns in
		match x with
		  | Some x -> Inr (SCast.Insn_unsafe_call(Some (x, _DEFAULT_TYP), SCast.Opcode_unknown(op2id o), ros @ os, l))
		  | None -> Inr (SCast.Insn_unsafe_call(None, SCast.Opcode_unknown(op2id o), ros @ os, l))
	      )
	    else
	      ( (*
		( if not (fname = op2id o) then
		    constraints_call fname true x o rgns os ts 
		) ;
		*)
		constraints_call fname true x o rgns os ts ; 
		Inr c
	      )
	  )
    | _ -> failwith "Found non-call in special_call."

let useless_calls o : bool =
  if op_contains o "pool_register_debug" then true
  else if op_contains o "pool_unregister_debug" then true
  else if op_contains o "pool_reregister_debug" then true
  else if op_contains o "pool_register_stack_debug" then true
  else if op_contains o "pool_unregister_stack_debug" then true
  else if op_contains o "pool_register_global" then true
  else if op_contains o "pool_init_runtime" then true
  else if op_contains o "__sc_vacallregister" then true
  else if op_contains o "__sc_vacallunregister" then true
  else if op_contains o "__sc_dbg_poolinit" then true
  else if op_contains o "__sc_dbg_pooldestroy" then true
  else if op_contains o "poolargvregister" then true
  else if op_contains o "llvm.memset" then true
  else false

let base_constraints fname tag o t = 
  match o with
    | SCast.Op_reg x -> 
	let tv = get_update_tvar fname x in
	modify_kappa tag (Tipe_eq(Tipe_tvar tv, to_base_tipe t))
    | _ -> ()

let base_constraints2 fname tag o1 t1 o2 t2 = 
  base_constraints fname tag o1 t1 ; 
  base_constraints fname tag o2 t2 

let constraints_select fname x arms =
  log "constraints select" ; 
  let tv = get_update_tvar fname x in
  let ts = List.fold_left
    (fun acc o ->
       match o with
	 | SCast.Op_reg x ->
	     (try 
		let t = read_gamma fname x in
		  t :: acc
	      with _ ->
		let tv' = get_update_tvar fname x in
		  Tipe_tvar tv' :: acc
	     )
	 | SCast.Op_const c -> 
	     match const_tipe c with
	       | Some t -> t :: acc
	       | None -> acc
    ) [] arms
  in
    modify_gkappa "select" (Tipe_eq(Tipe_tvar tv, Tipe_join ts))

let translate_insn fname i : (SCast.insn list, SCast.insn_nd_term) sum =
  let pools = parse_pstr (get_pstr i) in
  match instr_opcode i with
	(* Terminator Instructions *)
    | Opcode.Ret ->
	log "ret" ; 
	if (num_operands i) = 0 then
	  Inr (SCast.Insn_term SCast.Insn_return_void)
	else if (num_operands i) = 1 then
	  ( ( let (o, t) = opgen1 pools i in
	      (match o with
		 | SCast.Op_reg x -> 
		     let t' = VMap.find (fname, x) !gamma in
		     modify_kappa "return" (Tipe_eq(Tipe_tvar(fname, _RET), t'))
		 | SCast.Op_const c -> 
		     (match const_tipe c with
			| Some t -> modify_kappa "return" (Tipe_eq(Tipe_tvar(fname, _RET), t))
			| None ->
			    let tv = fresh_tvar fname in
			    modify_kappa "return" (Tipe_eq(Tipe_tvar(fname, _RET), Tipe_tvar tv))
		     )
		       (*
		 | SCast.Op_const _ ->
		     modify_kappa "return" (Tipe_eq(Tipe_tvar(fname, _RET), to_base_tipe t))
		       *)
	      ) ;
		frtyp := Some t ; 
		Inr (SCast.Insn_term(SCast.Insn_return(t, o)))
	    )
	  )
	else
	  failwith "Expected 0 or 1 operands in ret."
    | Opcode.Br ->
	log "br" ;
	if num_operands i = 1 then
	  ( let l = value_name (operand i 0) in
	    modify_preds l !currLab ; 
	    Inr (SCast.Insn_term(SCast.Insn_br_uncond(l)))
	  )
	else if num_operands i = 3 then
	  ( let l1 = value_name (operand i 1) in
	    let l2 = value_name (operand i 2) in
	    modify_preds l1 !currLab ; 
	    modify_preds l2 !currLab ; 
	    Inr (SCast.Insn_term(SCast.Insn_br(translate_op "" (operand i 0), l2, l1)))
	  )
	else
	  failwith "Incorrect arguments to br."
    | Opcode.Unreachable -> Inr (SCast.Insn_term (SCast.Insn_unreachable))

	(* Standard Binary Operators *)
    | Opcode.Add -> 
	log "add" ;
	let (o1, t1, o2, t2) = opgen2 pools i in
	modify_gamma (fname, (name i)) (to_base_tipe t1) ; 
	base_constraints2 fname "add" o1 t1 o2 t2 ; 
	Inl ([SCast.Insn_binop (name i, SCast.Binop_add, o1, o2)])
    | Opcode.FAdd ->
	log "fadd" ;
	let (o1, t1, o2, t2) = opgen2 pools i in
	modify_gamma (fname, (name i)) (to_base_tipe t1) ; 
	base_constraints2 fname "fadd" o1 t1 o2 t2 ;
	Inl ([SCast.Insn_fbinop (name i, SCast.Fbinop_add, o1, o2)])
    | Opcode.Sub ->
	log "sub" ; 
	let (o1, t1, o2, t2) = opgen2 pools i in
	modify_gamma (fname, (name i)) (to_base_tipe t1) ; 
	base_constraints2 fname "sub" o1 t1 o2 t2 ;
	Inl ([SCast.Insn_binop (name i, SCast.Binop_sub, o1, o2)])
    | Opcode.FSub ->
	log "fsub" ; 
	let (o1, t1, o2, t2) = opgen2 pools i in
	modify_gamma (fname, (name i)) (to_base_tipe t1) ; 
	base_constraints2 fname "fsub" o1 t1 o2 t2 ;
	Inl ([SCast.Insn_fbinop (name i, SCast.Fbinop_sub, o1, o2)])
    | Opcode.Mul -> 
	log "mul" ; 
	let (o1, t1, o2, t2) = opgen2 pools i in
	modify_gamma (fname, (name i)) (to_base_tipe t1) ; 
	base_constraints2 fname "mul" o1 t1 o2 t2 ;
	Inl ([SCast.Insn_binop (name i, SCast.Binop_mul, o1, o2)])
    | Opcode.FMul ->
	log "fmul" ; 
	let (o1, t1, o2, t2) = opgen2 pools i in
	modify_gamma (fname, (name i)) (to_base_tipe t1) ; 
	base_constraints2 fname "fmul" o1 t1 o2 t2 ;
	Inl ([SCast.Insn_fbinop (name i, SCast.Fbinop_mul, o1, o2)])
    | Opcode.UDiv -> 
	log "udiv" ; 
	let (o1, t1, o2, t2) = opgen2 pools i in
	modify_gamma (fname, (name i)) (to_base_tipe t1) ; 
	base_constraints2 fname "udiv" o1 t1 o2 t2 ;
	Inl ([SCast.Insn_binop (name i, SCast.Binop_udiv, o1, o2)])
    | Opcode.SDiv ->
	log "sdiv" ; 
	let (o1, t1, o2, t2) = opgen2 pools i in
	modify_gamma (fname, (name i)) (to_base_tipe t1) ; 
	base_constraints2 fname "sdiv" o1 t1 o2 t2 ;
	Inl ([SCast.Insn_binop (name i, SCast.Binop_sdiv, o1, o2)])
    | Opcode.FDiv ->
	log "fdiv" ;
	let (o1, t1, o2, t2) = opgen2 pools i in
	modify_gamma (fname, (name i)) (to_base_tipe t1) ; 
	base_constraints2 fname "fdiv" o1 t1 o2 t2 ;
	Inl ([SCast.Insn_fbinop (name i, SCast.Fbinop_div, o1, o2)])
    | Opcode.URem ->
	log "urem" ;
	let (o1, t1, o2, t2) = opgen2 pools i in
	modify_gamma (fname, (name i)) (to_base_tipe t1) ; 
	base_constraints2 fname "urem" o1 t1 o2 t2 ;
	Inl ([SCast.Insn_binop (name i, SCast.Binop_urem, o1, o2)])
    | Opcode.SRem ->
	log "srem" ;
	let (o1, t1, o2, t2) = opgen2 pools i in
	modify_gamma (fname, (name i)) (to_base_tipe t1) ; 
	base_constraints2 fname "srem" o1 t1 o2 t2 ;
	Inl ([SCast.Insn_binop (name i, SCast.Binop_srem, o1, o2)])
    | Opcode.FRem ->
	log "frem" ; 
	let (o1, t1, o2, t2) = opgen2 pools i in
	modify_gamma (fname, (name i)) (to_base_tipe t1) ; 
	base_constraints2 fname "frem" o1 t1 o2 t2 ;
	Inl ([SCast.Insn_fbinop (name i, SCast.Fbinop_rem, o1, o2)])

	(* Logical Operators *)
    | Opcode.Shl ->
	log "shl" ;
	let (o1, t1, o2, t2) = opgen2 pools i in
	modify_gamma (fname, (name i)) (to_base_tipe t1) ; 
	base_constraints2 fname "shl" o1 t1 o2 t2 ;
	Inl ([SCast.Insn_binop (name i, SCast.Binop_shl, o1, o2)])
    | Opcode.LShr ->
	log "lshr" ;
	let (o1, t1, o2, t2) = opgen2 pools i in
	modify_gamma (fname, (name i)) (to_base_tipe t1) ; 
	base_constraints2 fname "lshr" o1 t1 o2 t2 ;
	Inl ([SCast.Insn_binop (name i, SCast.Binop_lshr, o1, o2)])
    | Opcode.AShr ->
	log "ashr" ;
	let (o1, t1, o2, t2) = opgen2 pools i in
	modify_gamma (fname, (name i)) (to_base_tipe t1) ; 
	base_constraints2 fname "ashr" o1 t1 o2 t2 ;
	Inl ([SCast.Insn_binop (name i, SCast.Binop_ashr, o1, o2)])
    | Opcode.And ->
	log "and" ; 
	let (o1, t1, o2, t2) = opgen2 pools i in
	modify_gamma (fname, (name i)) (to_base_tipe t1) ; 
	base_constraints2 fname "and" o1 t1 o2 t2 ;
	Inl ([SCast.Insn_binop (name i, SCast.Binop_and, o1, o2)])
    | Opcode.Or -> 
	log "or" ;
	let (o1, t1, o2, t2) = opgen2 pools i in
	modify_gamma (fname, (name i)) (to_base_tipe t1) ; 
	base_constraints2 fname "or" o1 t1 o2 t2 ;
	Inl ([SCast.Insn_binop (name i, SCast.Binop_or, o1, o2)])
    | Opcode.Xor -> 
	log "xor" ;
	let (o1, t1, o2, t2) = opgen2 pools i in
	modify_gamma (fname, (name i)) (to_base_tipe t1) ; 
	base_constraints2 fname "xor" o1 t1 o2 t2 ;
	Inl ([SCast.Insn_binop (name i, SCast.Binop_xor, o1, o2)])

	(* Memory Operators *)
    | Opcode.Alloca -> 
	log "alloca" ; 
	let pool = List.nth pools 0 in
	let t = get_llptr_typ (type_of i) in
	let sz = size_typ t (* if is_unknown_pool pool then (size_typ t) else 1 *) in
	let t = translate_typ pool t in
	if is_pool_descriptor t
	then Inr (SCast.Insn_nd (SCast.Insn_call(None, None, SCast.Op_reg("__sc_dbg_poolinit"), [pool], [], "")))
	else 
	  (match emit_poolalloc fname (Some (name i)) t pool (SCast.Op_const (SCast.Const_int(63, sz))) "" with
	     | Inl i -> Inl i
	     | Inr nd -> Inr (SCast.Insn_nd nd)
	  )
    | Opcode.Load ->
	log "load" ;
	(* 
	 * G |- o:TV
	 * ---------------------------------------------------------
	 * G |- x = load lt* o !r : G[x:TV'] @ C[TV = TV'*r]
	 *)
	let (o, t) = opgen1 pools i in 
	let r = List.nth pools 1 in
	let x = name i in
	let lt = type_of (operand i 0) in
	let sz = size_typ (get_llptr_typ lt) in
	(match read_gamma fname (op2id o) with
	   | Tipe_tvar(tv) ->
	       let tv' = get_update_tvar fname x in
	       modify_gamma (fname, x) (Tipe_tvar tv') ;
	       if is_unknown_pool r then
		 ( let szv = fresh_svar fname in
		   modify_kappa "loadU" (Tipe_eq(Tipe_tvar tv', Tipe_int (sz * 8 - 1))) ; 
		   modify_kappa "loadU" (Tipe_eq(Tipe_tvar tv, Tipe_ptrU(Size_var szv, (fname, r)))) ; 
		   modify_kappa "loadU" (Size_geq(szv, sz)) 
		 )
	       else
	        ( modify_kappa "load" (Tipe_eq(Tipe_tvar tv, Tipe_ptr(Tipe_tvar tv', (fname, r)))) ; 
		  modify_kappa "load" (Tipe_size(Tipe_tvar tv', sz))
		)
	     | _ -> failwith "did not find tvar in load"
	  ) ; 
	  Inl ([SCast.Insn_load (x, SCast.Typ_int(sz), o)])
	(* Inl ([SCast.Insn_load (x, t, o)]) *)
    | Opcode.Store ->
	log "store" ;
	(* G |- o2:TV2    G |- o1:TV1
	 * ---------------------------------------------------------
	 * G |- store lt1 o1 !r1 lt2 o2 !r2 : G @ C[TV2 = TV1*r2]
	 *)
	let (o1, t1, o2, t2) = opgen2 pools i in
	let lt1 = type_of (operand i 0) in
	let sz = size_typ lt1 in
	let t1' = 
	  try ( log (Pprint.string_of_op o1) ; read_gamma fname (op2id o1))
	  with _ -> 
	    ( log "failure" ; 
	      if is_base_tipe t1 then
		to_base_tipe t1
	      else
		Tipe_tvar (fresh_tvar fname)
	    )
	in
	  (match get_base_typ lt1 with
	     | Some t -> modify_kappa "store/U" (Tipe_eq(t1', t))
	     | None -> ()
	  ) ; 
	  (match read_gamma fname (op2id o2) with
	     | Tipe_tvar(tv2) -> 
		 let r2 = List.nth pools 2 in
		 if is_unknown_pool r2 then
		   ( let szv = fresh_svar fname in
		     modify_kappa "storeU" (Tipe_eq(Tipe_tvar tv2, Tipe_ptrU(Size_var szv, (fname, r2)))) ; 
		     modify_kappa "storeU" (Size_geq(szv, sz)) ; 
		     log (Pprint.string_of_op o1 ^ ": " ^ string_of_int sz) 
		   )
		 else
		   modify_kappa "store" (Tipe_eq(Tipe_tvar tv2, Tipe_ptr(t1', (fname, r2))))
	     | _ -> failwith "did not find tvar in store op2"
	  ) ; 
	  modify_kappa "store/U" (Tipe_size(t1', sz)) ;
	Inl ([SCast.Insn_store (t1, o1, t2, o2)])
    | Opcode.GetElementPtr -> 
	log "gep" ; 
	(* G |- o:TV    fresh_tvars {lt1; ...; ltn} = {TV1; ...; TVn}
	 * TVi = index_typ {TV1; ...; TVn} os 
	 * ---------------------------------------------------------
	 * G |- x = gep {lt1; ...; ltn}* o os !r : G[x:TVi'] @ C[TV = TV'*r][TVi' = TVi*r][TV' = {TV1; ...; TVn}]
	 *)
	let (ops, ts) = List.split (opgenn pools i) in
	let o1 = operand i 0 in
	let t1 = get_llptr_typ (type_of o1) in
	let os1 = List.tl (List.tl ops) in
	let r = List.nth pools 1 in
	let x = name i in
	let o = (* List.hd (List.rev ops) *)
	  let (c, rs) = offset_typ (is_unknown_pool r) t1 os1 in
	  if List.length rs = 0 then
	    ( log ("GEP: " ^ x ^ " " ^ string_of_int c) ; 
	      SCast.Op_const(SCast.Const_int(63, c))
	    )
	  else
	    (* In general, we need to add for the entire register list, but for now
	       we haven't seen many multi-indexing geps ... *)
	    List.hd rs
	in
	(match read_gamma fname (op2id (List.nth ops 0)) with
	   | Tipe_tvar(tv) ->
	       let tv' = get_update_tvar fname x in
	       let tvi' = fresh_tvar fname in
		 if is_unknown_pool r then
		   ( modify_gamma (fname, x) (Tipe_tvar tvi') ;
		     ( if is_valid (op2id (List.nth ops 0)) then
			 ( let szv1 = fresh_svar fname in
			   modify_kappa "gepU" (Tipe_eq(Tipe_tvar tv, Tipe_ptrU(Size_var szv1, (fname, r)))) ;
			   modify_kappa "gepU" (Size_geq(szv1, size_typ t1)) 
			 )
		       else
			 ()
		     ) ; 
		     match o with
		       | SCast.Op_const(SCast.Const_int(_, c)) ->
			   let szv2 = fresh_svar fname in
			   modify_kappa "gepU" (Tipe_eq(Tipe_tvar tvi', Tipe_ptrU(Size_var szv2, (fname, r)))) ; 
			   modify_kappa "gepU" (Size_geq(szv2, size_typ t1 - c))
		       | _ -> ()
		   )
		 else
		   ( match classify_type t1 with
		       | TypeKind.Struct
		       | TypeKind.Vector 
		       | TypeKind.Array ->
			   let tstruct = aggregate_constraints fname t1 tv' in
			   log ("tstruct: " ^ string_of_tipe tstruct) ; 
			   log ("lltype: " ^ string_of_lltype t1) ; 
			   let tvi = index_tipe false t1 tstruct os1 in
			   modify_gamma (fname, x) (Tipe_tvar tvi') ;
			   modify_kappa "gep" (Tipe_eq(Tipe_tvar tv, Tipe_ptr(Tipe_tvar tv', (fname, r)))) ; 
			   modify_kappa "gep" (Tipe_eq(Tipe_tvar tvi', Tipe_ptr(tvi, (fname, r))))
		       | _ -> 
			   let tv' = get_update_tvar fname x in
			   (* let tv' = fresh_tvar fname in *)
			   modify_gamma (fname, x) (Tipe_tvar tv') ; 
			   modify_kappa "gep1" (Tipe_eq(Tipe_tvar tv, Tipe_ptr(Tipe_tvar tv', (fname, r))))
		   )
	   | _ -> 
	       log (string_of_tipeM !gamma) ; 
	       log (Pprint.string_of_ops ops) ; 
	       log (string_of_tipe (read_gamma fname (op2id (List.nth ops 0)))) ; 
	       failwith ("did not find tvar in gep: " ^ x) 
	) ;  
	(match o with
	   | SCast.Op_const(SCast.Const_int(_, 0)) ->
	       (* update_vars x (List.nth ops 0) *)
	       if is_unknown_pool r then
		 update_vars x (List.nth ops 0)
	       else
		 modify_checkaliasM (op2id (List.nth ops 0)) r (SCast.Op_reg x)
	   | _ -> ()
	) ; 
	if is_unknown_pool r then
	  Inl ([SCast.Insn_gepU(x, _DEFAULT_TYP, List.nth ops 0, o)])
	else
	  ( match classify_type t1 with
	      | TypeKind.Struct
	      | TypeKind.Vector
	      | TypeKind.Array ->
		  Inl ([SCast.Insn_gep(x, _DEFAULT_TYP, List.nth ops 0, _DEFAULT_TYP, o)])
	      | _ ->
		  Inl ([SCast.Insn_gep1(x, _DEFAULT_TYP, List.nth ops 0, o)])
	  )

	(* Cast Operators *)
    | Opcode.Trunc ->
	log "trunc" ;
	let (o, t1) = opgen1 pools i in
	let t2 = translate_typ (List.nth pools 0) (type_of i) in
	update_cval (name i) o ; 
	modify_gamma (fname, (name i)) (to_base_tipe t2) ; 
	base_constraints fname "trunc" o t1 ;
	Inl ([SCast.Insn_iconv (name i, SCast.Iconv_trunc, t1, o, t2)])
    | Opcode.ZExt -> 
	log "zext" ;
	let (o, t1) = opgen1 pools i in
	let t2 = translate_typ (List.nth pools 0) (type_of i) in
	modify_gamma (fname, (name i)) (to_base_tipe t2) ;
	base_constraints fname "zext" o t1 ;
	Inl ([SCast.Insn_iconv (name i, SCast.Iconv_zext, t1, o, t2)])
    | Opcode.SExt ->
	log "sext" ;
	let (o, t1) = opgen1 pools i in
	let t2 = translate_typ (List.nth pools 0) (type_of i) in
	modify_gamma (fname, (name i)) (to_base_tipe t2) ;
	base_constraints fname "sext" o t1 ;
	Inl ([SCast.Insn_iconv (name i, SCast.Iconv_sext, t1, o, t2)])
    | Opcode.FPToUI -> 
	log "fptoui" ;
	let (o, t1) = opgen1 pools i in
	let t2 = translate_typ (List.nth pools 0) (type_of i) in
	modify_gamma (fname, (name i)) (to_base_tipe t2) ;
	base_constraints fname "fptoui" o t1 ;
	Inl ([SCast.Insn_iconv (name i, SCast.Iconv_fptoui, t1, o, t2)])
    | Opcode.FPToSI ->
	log "fptosi" ;
	let (o, t1) = opgen1 pools i in
	let t2 = translate_typ (List.nth pools 0) (type_of i) in
	modify_gamma (fname, (name i)) (to_base_tipe t2) ;
	base_constraints fname "fptosi" o t1 ;
	Inl ([SCast.Insn_iconv (name i, SCast.Iconv_fptosi, t1, o, t2)])
    | Opcode.UIToFP ->
	log "uitofp" ;
	let (o, t1) = opgen1 pools i in
	let t2 = translate_typ (List.nth pools 0) (type_of i) in
	modify_gamma (fname, (name i)) (to_base_tipe t2) ;
	base_constraints fname "uitofp" o t1 ;
	Inl ([SCast.Insn_fconv (name i, SCast.Fconv_uitofp, t1, o, t2)])
    | Opcode.SIToFP ->
	log "sitofp" ;
	let (o, t1) = opgen1 pools i in
	let t2 = translate_typ (List.nth pools 0) (type_of i) in
	modify_gamma (fname, (name i)) (to_base_tipe t2) ;
	base_constraints fname "sitofp" o t1 ;
	Inl ([SCast.Insn_fconv (name i, SCast.Fconv_sitofp, t1, o, t2)])
    | Opcode.PtrToInt -> 
	log "ptrtoint" ;
	let (o, t1) = opgen1 pools i in
	let t2 = translate_typ (List.nth pools 0) (type_of i) in
	modify_gamma (fname, (name i)) (to_base_tipe t2) ;
	Inl ([SCast.Insn_ptrtoint (name i, t1, o, t2)])
    | Opcode.IntToPtr ->
	log "inttoptr" ;
	let (o, t1) = opgen1 pools i in
	(* let t2 = translate_typ (List.nth pools 0) (type_of i) in *)
	(* Will I ever see one of these? *)
	update_vars (name i) o ;
	Inl ([SCast.Insn_bitcast (name i, _DEFAULT_TYP, o, _DEFAULT_TYP)])
	(* Inl (SCast.Insn_inttoptr (name i, t1, o, t2)) *)
    | Opcode.BitCast -> 
	log "bitcast" ;
	let (o, t1) = opgen1 pools i in
	update_vars (name i) o ;
	Inl ([SCast.Insn_bitcast (name i, _DEFAULT_TYP, o, _DEFAULT_TYP)])

	(* Other Operators *)
    | Opcode.ICmp -> 
	log "icmp" ;
	let (o1, t1, o2, t2) = opgen2 pools i in
	(match icmp_predicate i with
	  | None -> failwith "Expected predicate but none found in icmp."
	  | Some pred ->
	      modify_gamma (fname, name i) (to_base_tipe (translate_typ "" (type_of i))) ; 
	      (match o1, o2 with
		 | SCast.Op_reg x1, SCast.Op_reg x2 ->
		     let t1' = read_gamma fname x1 in
		     let t2' = read_gamma fname x2 in
		       modify_kappa "icmp" (Tipe_eq(t1', t2'))
		 | SCast.Op_reg x, SCast.Op_const (SCast.Const_int(sz, _))
		 | SCast.Op_const (SCast.Const_int(sz, _)), SCast.Op_reg x ->
		     let t' = read_gamma fname x in
		       modify_kappa "icmp" (Tipe_eq(t', Tipe_int sz))
		 | _, _ -> ()
	      ) ; 
	      Inl ([SCast.Insn_icmp (name i, translate_icmp pred, o1, o2)])
	)
    | Opcode.FCmp ->
	log "fcmp" ;
	let (o1, t1, o2, t2) = opgen2 pools i in
	let pred = Fcmp.False in
        modify_gamma (fname, name i) (to_base_tipe (translate_typ "" (type_of i))) ; 
	base_constraints2 fname "fcmp" o2 t1 o2 t2 ;
	Inl ([SCast.Insn_fcmp (name i, translate_fcmp pred, o1, o2)])

    | Opcode.Call ->
	log "call" ;
	(*
	 * get_update_tvar o:TV    fresh_tvars {o1, ..., om} = {TV1; ...; TVm}
	 * -------------------------------------------------
	 * G |- x = t call o <r1, ..., rn> (o1, ..., om) : G[x:TV'] @ 
	 *     C[TV = TV' fun<r1, ..., rn>(TV1, ..., TVm)]
	 *)
	(*
	let (ops, ts) = List.split (opgenn pools i) in
	let (o, ops) = (match List.rev ops with
			  | [] -> failwith "call needs at least 1 operand"
			  | h::t -> (h, t)
		       ) in
	let ops' = List.rev ops in
	let rgns = List.map op2id (List.filter is_pool ops') in
	let ops = List.filter (fun x -> not (is_pool x)) ops' in
	*)
	let ops = opgenn pools i in
	let ((o, _), ops) = (match List.rev ops with
			  | [] -> failwith "call needs at least 1 operand"
			  | h::t -> (h, t)
		       ) in
	let ops' = List.rev ops in
	let rgns = List.map (fun (o, t) -> op2pool o) (List.filter (fun (o, t) -> is_pool o t) ops') in
	let ops = List.filter (fun (o, t) -> not (is_pool o t)) ops' in
	let (ops, ts) = List.split ops in
	let fname' = operand i (num_operands i - 1) in
	let ftyp = type_of fname' in
	let frtyp = return_type (element_type ftyp) in
	let (x, rtyp) = 
	  match classify_type frtyp with
	    | TypeKind.Void -> (None, None)
	    | _ -> 
		let tv = get_update_tvar fname (name i) in
		if useless_calls o then
		  ()
		else
		  modify_gamma (fname, (name i)) (Tipe_tvar tv) ;
		(Some (name i), Some (translate_typ (List.nth pools 0) frtyp)) 
	in 
	let tmp = (SCast.Insn_call(x, rtyp, o, rgns , ops, "")) in
	(match special_call fname pools ts tmp with
	  | Inl i -> Inl i
	  | Inr nd -> Inr (SCast.Insn_nd nd)
	)

    | Opcode.Invalid -> failwith "translate_insn unsupported: invalid"
    | Opcode.Switch -> 
	log (string_of_int (num_operands i)) ;
	let (o, t) = translate_op_typ "" (operand i 0) in
	log (Pprint.string_of_op o) ; 
	let dl = translate_op "" (operand i 1) in
	log (Pprint.string_of_op dl) ; 
	let rec go i idx n = 
	  if idx < n then
	    let o = translate_op "" (operand i idx) in
	      o :: go i (idx + 2) n
	  else
	    []
	in
	let ls = go i 3 (num_operands i) in
	let sz = 
	  match t with
	    | SCast.Typ_int(sz) -> sz
	    | _ -> failwith "switch should have an integer type"
	in
	  Inr (SCast.Insn_term (SCast.Insn_switch(t, o, op2id dl, List.map (fun l -> ((t, SCast.Const_int(sz, 0)), op2id l)) ls)))

    | Opcode.IndirectBr -> failwith "translate_insn TODO: indirectbr"
    | Opcode.Invoke -> failwith "translate_insn unsupported: invoke"
    | Opcode.Invalid2 -> failwith "translate_insn unsupported: invalid2"
    | Opcode.FPTrunc -> 
	log "fptrunc" ; 
	let (o, t1) = opgen1 pools i in
	let t2 = translate_typ (List.nth pools 0) (type_of i) in
	modify_gamma (fname, (name i)) (to_base_tipe t2) ; 
	base_constraints fname "fptrunc" o t1 ;
	Inl ([SCast.Insn_fconv (name i, SCast.Fconv_fptrunc, t1, o, t2)])
    | Opcode.FPExt -> 
	log "fpext" ;
	let (o, t1) = opgen1 pools i in
	let t2 = translate_typ (List.nth pools 0) (type_of i) in
	modify_gamma (fname, (name i)) (to_base_tipe t2) ; 
	base_constraints fname "fptrunc" o t1 ;
	Inl ([SCast.Insn_fconv (name i, SCast.Fconv_fpext, t1, o, t2)])
    | Opcode.PHI -> failwith "Found phi instruction in translate_insn but it should have been filtered."
    | Opcode.Select -> 
	let ots = opgenn pools i in
	let (o, t) = List.nth ots 0 in
	let (o1, t1) = List.nth ots 1 in
	let (o2, t2) = List.nth ots 2 in
	let tv = get_update_tvar fname (name i) in
	modify_gamma (fname, name i) (Tipe_tvar tv) ; 
	constraints_select fname (name i) [o1; o2] ; 
	  (*
	(match o1, o2 with
	   | SCast.Op_reg x1, SCast.Op_reg x2 ->
	       let t1' = read_gamma fname x1 in
	       let t2' = read_gamma fname x2 in
	       modify_kappa "select" (Tipe_eq(Tipe_tvar tv, t1')) ; 
	       modify_kappa "select" (Tipe_eq(t1', t2'))
	   | SCast.Op_reg x, SCast.Op_const (SCast.Const_int(sz, _))
	   | SCast.Op_const (SCast.Const_int(sz, _)), SCast.Op_reg x ->
	       let t' = read_gamma fname x in
	       modify_kappa "select" (Tipe_eq(Tipe_tvar tv, t')) ; 
	       modify_kappa "select" (Tipe_eq(t', Tipe_int sz))
	   | _, _ -> ()
	) ; 
	  *)
	Inl ([SCast.Insn_select (name i, t, o, t1, o1, t2, o2)])
    | Opcode.UserOp1 -> failwith "unsupported: userop1"
    | Opcode.UserOp2 -> failwith "unsupported: userop2"
    | Opcode.VAArg -> failwith "unsupported: vaarg"
    | Opcode.ExtractElement -> failwith "unsupported: extractelement"
    | Opcode.InsertElement -> failwith "unsupported: insertelement"
    | Opcode.ShuffleVector -> failwith "unsupported: shufflevector"
    | Opcode.ExtractValue -> 
	(* bug? operands doesn't give us constants ... *)
	log "extractvalue" ; 
	let ops = opgenn pools i in
	let (o1, t1) = List.nth ops 0 in
	let idx = 0 in (* Hack ... llvm bindings are messed up and don't give us constant indices. *)
	let c = SCast.Const_int(63, idx) in
	let lt = type_of (operand i 0) in
	let tstruct = lltyp2tipe fname lt in
	( try
	    match read_gamma fname (op2id o1) with
	      | Tipe_tvar(tv) ->
		  modify_kappa "extractvalue" (Tipe_eq(Tipe_tvar tv, tstruct)) ; 
	      | _ -> failwith "extractvalue haz troublez"
	  with _ -> ()
	) ; 
	let tv' = get_update_tvar fname (name i) in
	modify_gamma (fname, name i) (Tipe_tvar tv') ; 
	modify_kappa "extractvalue" (Tipe_eq(Tipe_tvar tv', index_struct_tipe tstruct idx)) ; 
	Inl ([SCast.Insn_extractvalue(name i, t1, o1, _DEFAULT_TYP, c)])

    | Opcode.InsertValue -> 
	log "insertvalue" ; 
	let ops = opgenn pools i in
	let (o1, t1) = List.nth ops 0 in
	let (o2, t2) = List.nth ops 1 in
	log (Pprint.string_of_op o1) ; 
	log (Pprint.string_of_op o2) ; 
	let idx = 0 in (* Hack ... llvm bindings are messed up and don't give us constant indices. *)
	let c = SCast.Const_int(63, idx) in
	let lt = type_of (operand i 0) in
	let tstruct = lltyp2tipe fname lt in
	( try
	    match read_gamma fname (op2id o1) with
	      | Tipe_tvar(tv) ->
		  modify_kappa "insertvalue" (Tipe_eq(Tipe_tvar tv, tstruct)) ; 
	      | _ -> failwith "insertvalue haz troublez"
	  with _ -> ()
	) ; 
	( try
	    match read_gamma fname (op2id o2) with
	      | Tipe_tvar(tv) -> modify_kappa "insertvalue" (Tipe_eq(Tipe_tvar tv, index_struct_tipe tstruct idx))
	      | _ -> ()
	  with _ -> () 
	) ; 
	let tv' = get_update_tvar fname (name i) in
	modify_gamma (fname, name i) (Tipe_tvar tv') ; 
	modify_kappa "insertvalue" (Tipe_eq(Tipe_tvar tv', tstruct)) ; 
	Inl ([SCast.Insn_insertvalue(name i, t1, o1, t2, o2, c)])

    | Opcode.Fence -> failwith "unsupported: fence"
    | Opcode.AtomicCmpXchg -> failwith "unsupported: atomiccmpxchg"
    | Opcode.AtomicRMW -> failwith "unsupported: atomicrmw"
    | Opcode.Resume -> failwith "unsupported: resume"
    | Opcode.LandingPad -> failwith "unsupported: landingpad"
    (* | Opcode.Unwind -> failwith "unsupported: unwind" *)

let is_null o : bool =
  match o with
    | SCast.Op_const (SCast.Const_null) -> true
    | SCast.Op_const (SCast.Const_nullU) -> true
    | _ -> false

let translate_phi fname b p : SCast.phinode =
  let pools = parse_pstr (get_pstr p) in
  let r = List.nth pools 0 in
  match instr_opcode p with
    | Opcode.PHI ->
	log "phi" ; 
	let arms = List.map (fun (o, b) -> (translate_op r o, name (value_of_block b))) (incoming p) in
	let x = name p in
	  (*
	( if List.exists (fun (o, l) -> is_null o) arms && is_unknown_pool r then
	    ( let tv = get_update_tvar fname x in
	      modify_gkappa "phi" (Tipe_eq(Tipe_tvar tv, Tipe_ptrU(Size_const 0, (fname, r)))) ; 
	      modify_gamma (fname, x) (Tipe_tvar tv)
	    )
	 else
	   constraints_phi fname x arms 
	) ; 
	  *)
	let tv = get_update_tvar fname x in
	modify_gamma (fname, x) (Tipe_tvar tv) ; 
	let t = List.fold_left 
	  ( fun acc (o, b) -> 
	      let (o', t') = translate_op_typ r o in
	      t' 
	  ) (SCast.Typ_int(7)) (incoming p) 
	in
	  SCast.Insn_phi(name p, t, arms)
    | _ -> failwith "found non-phi instruction in translate_phi"

let filter_phis_insns fname b : (SCast.phiblock * ((SCast.insn list, SCast.insn_nd_term) sum) list) =
  let phis = filter_phis b in 
  let insns = filter_insns b in
  let phis' = List.fold_left (fun acc p -> translate_phi fname b p :: acc) [] phis in 
  let insns' = List.fold_left (fun acc i -> translate_insn fname i :: acc) [] insns in
  let phis'' = List.map (fun (x, arms) -> 
			   SCast.Insn_phi(x, _DEFAULT_TYP, arms) 
			) !checkphis 
  in
  (List.rev phis' @ phis'', List.rev insns')

(* Skip "useless" calls and record poolinits *)
let skip_call ndtm : bool =
  match ndtm with
    | SCast.Insn_nd (SCast.Insn_call(_, _, o, rgns, _, _)) ->
	useless_calls o
    | SCast.Insn_nd (SCast.Insn_malloc(_, _, _, _, _)) -> false
    | _ -> false

let update_ndtm_lab ndtm l : SCast.insn_nd_term =
  match ndtm with
    | SCast.Insn_nd nd ->
	(match nd with
	  | SCast.Insn_call(x, t, o, rgns, os, _) -> SCast.Insn_nd (SCast.Insn_call(x, t, o, rgns, os, l))
	  | SCast.Insn_malloc(x, t, r, sz, _) -> SCast.Insn_nd (SCast.Insn_malloc(x, t, r, sz, l))
	  | SCast.Insn_unsafe_call(xt, op, os, _) -> SCast.Insn_nd (SCast.Insn_unsafe_call(xt, op, os, l))
	)  
    | SCast.Insn_term _ -> ndtm

let update_phi_lab p : SCast.phinode =
  match p with
    | SCast.Insn_phi(x, t, arms) ->
	let arms' = List.map 
	  ( fun (o, l) -> 
	      let l' = (try SMap.find l !labM with Not_found -> l) in
	      (o, l')
	  ) arms
	in
	SCast.Insn_phi(x, t, arms')

let update_phis_lab ps : SCast.phiblock =
  List.map update_phi_lab ps

let split_block fname b phis (ls:((SCast.insn list, SCast.insn_nd_term) sum) list) : SCast.block list =
  let curr_insns = ref [] in
  let stk_blk = ref [] in
  let first = ref true in
  let blk_ctr = ref 0 in
  List.iter
    (fun i ->
       match i with
	 | Inr ndtm ->
	     if skip_call ndtm then () 
	     else
	       let (currLab, nextLab, phis') = 
		 if !first then 
		   ( first := false ;
	             (name (value_of_block b), 
		      name (value_of_block b) ^ "-" ^ string_of_int (!blk_ctr + 1),
		      phis)
		   )
		 else
		   ( blk_ctr := !blk_ctr + 1 ;
		     (name (value_of_block b) ^ "-" ^ string_of_int !blk_ctr,
		      name (value_of_block b) ^ "-" ^ string_of_int (!blk_ctr + 1),
		      [])
		   ) 
	       in
	       let b = { SCast.b_lab = currLab ;
			 SCast.b_phis = phis' ;
			 SCast.b_insns = List.rev (!curr_insns) ;
			 SCast.b_nd_term = update_ndtm_lab ndtm nextLab
		       } 
	       in
		 stk_blk := b::(!stk_blk) ;
		 curr_insns := []
	 | Inl i -> 
	     match i with
	       | SCast.Insn_bitcast _ :: [] -> ()
	       | _ -> 
		   curr_insns := i @ !curr_insns 
    ) ls ;
  let bs = List.rev (!stk_blk) in
  let entry_lab = (List.hd bs).SCast.b_lab in
  let rewrite_lab = (if !blk_ctr = 0 then entry_lab else entry_lab ^ "-" ^ string_of_int !blk_ctr) in
  labM := SMap.add entry_lab rewrite_lab !labM ;
  bs

(* We get a list of blocks out because we break up calls in the middle of a block. *)  	
let translate_block fname b : SCast.block list =
  log ("translating block: " ^ value_name (value_of_block b)) ;

  currLab := (value_name (value_of_block b)) ; 
  (* log (G.string_of_g preds (fun x -> x)) ; *)
  predLabs := G.S.elements (G.edges preds !currLab) ; 
  reset_checkphis() ; 
  let (phis, insns) = filter_phis_insns fname b in
  split_block fname b phis insns

let translate_params f : (SCast.id * SCast.typ) list =
  let (_, result) = 
    fold_right_params
      (fun p (i, acc) ->
	 let id = op2id (translate_op "" p) in
	   if contains id "PD" then 
	     (i - 1, acc)
	   else if (value_name f) = "main" && id = "argv" then
	     ( let t = translate_typ "NA" (type_of p) in
	       (i - 1, (id, t)::acc)
	     )
	   else
	     ( let t = translate_typ (List.nth !poolArg i) (type_of p)
		 (*
		 try 
		   if is_unknown_pool (List.nth !poolArg i)
		   then translate_typ (List.nth !poolArg i) (type_of p)
		   else SMap.find (List.nth !poolArg i) !poolTypM 
		 with Not_found -> 
		   translate_typ (List.nth !poolArg i) (type_of p)
		 *)
	       in
	       (i - 1, (id, t)::acc)
	     )
      ) f (List.length !poolArg - 1, [])
  in result

let translate_prgns f : (SCast.id * SCast.typ) list =
  fold_right_params
    (fun p acc ->
       let id = op2id (translate_op "" p) in
       if contains id "PD" then 
	 (id, SMap.find id !poolTypM) :: acc
       else if (value_name f) = "main" && id = "argv" then
	 ("NA", SCast.Typ_int(7)) :: acc
       else acc
    ) f []

let gather_constraint_fun_prelim f =
  let (params, typs) = List.split (translate_params f) in
  let fname = value_name f in
  let tvs' = List.map (fun t -> try to_base_tipe t with _ -> Tipe_tvar (fresh_tvar fname)) typs in
  let rtyp = return_type (get_llptr_typ (type_of f)) in
  let tvret = Tipe_tvar(fname, _RET) in
  let tvret' = 
    match classify_type rtyp with
      | TypeKind.Void -> None
      | _ -> Some tvret
  in
  let (prgns, _) = List.split (translate_prgns f) in
  let prgns = List.map (fun x -> (fname, x)) prgns in
  List.iter (fun (x, t') -> modify_gamma (fname, x) t') (List.combine params tvs') ; 
  (match tvret' with
     | Some tvret -> put_callsites fname ((Tipe_scheme(prgns, tvret), []) :: (List.map (fun t -> (Tipe_scheme(prgns, t), [])) tvs'))
     | None -> put_callsites fname (List.map (fun t -> (Tipe_scheme(prgns, t), [])) tvs')
  ) ; 
  modify_gamma (_GLOBAL, fname) (Tipe_fun(prgns, tvs', tvret'))

let backedge_constraint_phi fname p = 
  match p with
    | SCast.Insn_phi(x, t, arms) ->
	let arms' = 
	  List.map (fun (o, l) -> 
		      match o with
			| SCast.Op_reg x -> 
			    let x = idgen2 l x in 
			    if VMap.mem (l, x) !checkvarsM then
			      ( let x' = snd (VMap.find (l, x) !checkvarsM) in
				log ("succeed: " ^ x ^ " " ^ x') ; 
				(SCast.Op_reg x', l)
			      )
			    else
			      ( log ("fail: " ^ x) ; 
				(SCast.Op_reg x, l)
			      )
			| _ -> (o, l)
		   ) arms
	in
	  constraints_phi fname x arms' ; 
	  SCast.Insn_phi(x, t, arms')

let backedges_constraints_phis fname b = 
  List.map (backedge_constraint_phi fname) b.SCast.b_phis

let translate_function (m:llmodule) f : SCast.function0 =
  log ("translating function: " ^ value_name f) ;
  currFunc := value_name f ; 
  let (params, typs) = List.split (translate_params f) in
  let prgns = translate_prgns f in
  let body = fold_left_blocks (fun acc b -> acc @ (translate_block (value_name f) b)) [] f in
  (* let _ = List.iter (fun b -> constraints_phis (value_name f) b) body in *)
  (* let body = Dce.dce_blks body in *)
  let body = List.map 
    ( fun b -> 
	let phis' = backedges_constraints_phis (value_name f) b in
	let phis' = update_phis_lab phis' in
	let insns' = (* Dce.dce_insns *) b.SCast.b_insns in
	{ SCast.b_lab = b.SCast.b_lab ; 
	  SCast.b_phis = phis' ;
	  SCast.b_insns = insns' ; 
	  SCast.b_nd_term = b.SCast.b_nd_term
	}
    ) body 
  in
  let rtyp' = 
    match !frtyp with
      | Some t -> Some t
      | None ->
	  let rtyp = return_type (get_llptr_typ (type_of f)) in
	  let rtyp' = 
	    ( match classify_type rtyp with
		| TypeKind.Void -> None
		| _ -> 
		    log "here" ; 
		    Some (translate_typ (List.nth !poolArg 0) rtyp) 
	    )
	  in rtyp'
  in
  let global_prgn = [] in
  (* let global_prgn = List.map (fun r -> (r, _DEFAULT_TYP)) !gpools in *)
  { SCast.f_lab = (value_name f) ;
    SCast.f_params = params ;    (* id list *)
    SCast.f_sig = typs ;         (* typ list *)
    SCast.f_body = body ;        (* block list *)
    SCast.f_ret = rtyp' ;        (* typ option *)
    SCast.f_prgn = prgns @ global_prgn ;       (* (rgn * typ) list *)
    SCast.f_lrgn = List.rev !localpool (* (rgn * typ) list *)
  }

let translate_library (m:llmodule) f : SCast.function0 =
  let fname = value_name f in
  log ("translating library function: " ^ fname) ;
  if contains fname "llvm.memset" then
    { SCast.f_lab = fname ;
      SCast.f_params = ["4"; "3"; "2"; "1"; "0" ] ;
      SCast.f_sig = [SCast.Typ_ptrU(8, "PD"); SCast.Typ_int(7); SCast.Typ_int(63); SCast.Typ_int(31); SCast.Typ_int(0)] ;
      SCast.f_body = [] ;
      SCast.f_ret = None ;
      SCast.f_prgn = [("PD", SCast.Typ_int(7))] ;
      SCast.f_lrgn = []
    }
  else if fname = "free" then
    { SCast.f_lab = fname ;
      SCast.f_params = [ "0" ] ;
      SCast.f_sig = [ SCast.Typ_int(63) ] ;
      SCast.f_body = [] ;
      SCast.f_ret = None ;
      SCast.f_prgn = [] ;
      SCast.f_lrgn = []
    }
  else
    translate_function m f

let translate_function2 sizeM delta gamma f : SCast.function0 =
  log ("annotating: " ^ f.SCast.f_lab) ; 
  let prgns = Annotate.annotate_rgns f.SCast.f_lab sizeM delta f.SCast.f_prgn in
  let lrgns = Annotate.annotate_rgns f.SCast.f_lab sizeM delta f.SCast.f_lrgn in
  let body' = 
    try Annotate.annotate_blks f.SCast.f_lab sizeM gamma f.SCast.f_body 
    with _ -> 
      log "failing" ; 
      log (Pprint.string_of_fun f) ; 
      Annotate.annotate_blks f.SCast.f_lab sizeM gamma f.SCast.f_body 
  in
  let (sig', ret') = 
    match VMap.find (_GLOBAL, f.SCast.f_lab) gamma with
      | Tipe_fun(_, ts, tret) ->
	  (List.map (Annotate.lower_tipe sizeM) ts, lift_opt (Annotate.lower_tipe sizeM) tret)
      | _ -> failwith "expected function but none found"
  in
  let sig' = List.map Annotate.splat sig' in
  { SCast.f_lab = f.SCast.f_lab ;
    SCast.f_params = f.SCast.f_params ;     (* id list *)
    SCast.f_sig = sig' ;          (* typ list *)
    SCast.f_body = body' ;        (* block list *)
    SCast.f_ret = ret' ;          (* typ option *)
    SCast.f_prgn = prgns ;        (* (rgn * typ) list *)
    SCast.f_lrgn = lrgns          (* (rgn * typ) list *)
  }

(* Filter out SAFEcode library functions *)
let filter_sc_func (f:llvalue) : bool =
  let c = (value_name f) in
    if c = "__sc_dbg_pooldestroy" then false
    else if c = "__sc_dbg_poolinit" then false
    else if c = "__poolalloc_init" then false
    else if c = "poolalloc_global_ctor" then false
    else if c = "poolregister" then false
    else if c = "poolfree" then false
    else if c = "poolstrdup" then false
    else if c = "poolmemalign" then false
    else if c = "poolcalloc" then false
    else if c = "poolrealloc" then false
    else if c = "poolalloc" then false
    else if c = "poolcheck_debug" then false
    else if c = "poolreregister_debug" then false
    else if c = "fastlscheck" then false
    else if c = "fastlscheck_debug" then false
    else if c = "exactcheck2" then false
    else if c = "__fastgepcheck" then false
    else if c = "__faststorecheck" then false
    else if c = "__fastloadcheck" then false
    else if c = "boundscheck_debug" then false
    else if c = "boundscheckui_debug" then false
    else if c = "poolcheckui_debug" then false
    else if c = "pool_unregister_debug" then false
    else if c = "pool_register_debug" then false
    else if c = "pool_register_global" then false
    else if c = "pool_register_stack_debug" then false
    else if c = "pool_unregister_stack_debug" then false
    else if c = "pool_unregister_debug" then false
    else if c = "pool_reregister_debug" then false
    else if c = "poolcheck_freeui_debug" then false
    else if c = "pchk_getActualValue" then false
    else if c = "pool_init_runtime" then false
    else if c = "pool_ctor" then false
    else if c = "pool_printf" then false
    else if c = "pool_vfprintf_debug" then false
    else if c = "pool_fprintf" then false
    else if c = "__sc_fsparameter" then false
    else if c = "__sc_fscallinfo_debug" then false
    else if c = "__sc_vacallregister" then false
    else if c = "__sc_vacallunregister" then false
    else if c = "funccheckui_debug" then false
    else if c = "funccheck_debug" then false
    else if c = "malloc" then false
    else if c = "calloc" then false
    else if c = "realloc" then false
    (* else if c = "free" then false *)
    else if c = "__assert_rtn" then false
    else true 

let filter_nonpool_func clones (f:llvalue) : bool =
  let c = contains (value_name f) in
    if c "clone" then true
    else if c "main" then true
    else if not (S.mem ((value_name f) ^ "_clone") clones) then true
    else false

let filter_library_func (f:llvalue) : bool =
  let fname = value_name f in
  let c = contains fname in
  if c "llvm." then true
  else if fname = "free" then true
  else false

let setPools poolM' poolTypM' poolArg' f =
  log (value_name f) ; 
  poolTypM := (try SMap.find (value_name f) poolTypM' with Not_found -> SMap.empty) ;
  poolArg := (try SMap.find (value_name f) poolArg' with Not_found -> [])

let translate_module filename (m:llmodule) : (SCast.id * SCast.typ) list * SCast.typ SMap.t * SCast.functions =
  let (poolM', poolTypM', poolArg') = Parsepoolinfo.buildPoolInfo filename in
  log (Parsepoolinfo.string_of_poolinfo(poolM', poolTypM')); 

  (* gather_constraint_library_prelim() ; *)

  fold_right_globals (fun g acc -> match classify_value g with
			| ValueKind.Function -> ()
			| ValueKind.GlobalVariable -> 
			    let tv = fresh_tvar _GLOBAL in
			    let name = getGlobalSlot g in
			    if contains name "Pool" then
			      ( modify_gamma (_GLOBAL, name) (Tipe_tvar tv) ;
				modify_gpools name (Tipe_tvar tv)
			      )
			    else
			      ( modify_gamma (_GLOBAL, _GLOBAL ^ name) (Tipe_tvar tv) ; 
				modify_gvars g (_GLOBAL ^ name)
			      )
			| _ -> failwith "Found non-global in fold_right_globals" 
		     ) m () ; 

  let clones = fold_right_functions (fun f acc ->
				       if contains (value_name f) "clone" then
					 S.add (value_name f) acc
				       else acc
				    ) m S.empty
  in
  fold_right_functions (fun f acc -> 
			  if filter_sc_func f && filter_nonpool_func clones f then 
			    ( setPools poolM' poolTypM' poolArg' f ; 
			      gather_constraint_fun_prelim f ; 
			    )
			  else if filter_sc_func f && filter_library_func f then
			    ( setPools poolM' poolTypM' poolArg' f ; 
			      gather_constraint_fun_prelim f ; 
			    )
		       ) m () ; 
  log ("callsites: " ^ string_of_callsites !callsites) ; 
  let fs = fold_right_functions 
    (fun f acc -> 
       clearLocalPool() ; 
       clearSlotTracker() ;
       clearUnsafeValidate() ; 
       clearCval() ; 
       clearVars() ; 
       clearLab() ; 
       clearFrtyp() ; 
       reset_checkvarsM() ; 
       reset_checkaliasM() ; 
       reset_valid() ; 
       G.clear_graph preds ;

       setPools poolM' poolTypM' poolArg' f ; 
       if filter_sc_func f && filter_nonpool_func clones f then 
	 (translate_function m f)::acc 
       else if filter_sc_func f && filter_library_func f then
	 (translate_library m f)::acc
       else acc
    ) m []
  in
  log (Pprint.string_of_funs fs) ; 
  log ("gkappa: " ^ string_of_cs (!gkappa @ callsites_constraints())) ; 
  let (sizeM, delta, gamma) = Infer.infer !delta !gamma (List.rev !kappa) (!gkappa @ callsites_constraints()) in
  let gprgns = Annotate.annotate_rgns _GLOBAL sizeM gamma (List.map (fun x -> (x, _DEFAULT_TYP)) !gpools) in
  let funcs = List.map (translate_function2 sizeM delta gamma) fs in
  let globsM = Annotate.get_globsM() in
  (gprgns, globsM, funcs)

let tc_one gprgns globsM funcs f =
  let structM = Annotate.get_structM() in
  log ("tenv: " ^ Pprint.string_of_tenv structM) ; 
  let tenv = Lower.lower_tenv Lower.lo structM in
  let fpkg = Lower.lower_func Lower.lo structM gprgns globsM f in
  let c = 
    { Tc.c_fs = funcs ;
      Tc.c_lo = Lower.lo ;
      Tc.c_tenv = tenv 
    }
  in
    log (Lower.string_of_psi fpkg.Lower.psi) ;
  if Tc.tc_function c (fpkg.Lower.delta1) (fpkg.Lower.delta2) (fpkg.Lower.psi) (fpkg.Lower.func)
  then print_endline ("tc_func: " ^ f.SCast.f_lab ^ " succeeded") 
  else print_endline ("tc_func: " ^ f.SCast.f_lab ^ " failed")

let tc_all gprgns globsM funcs : bool =
  log "begin tc_all" ; 
  let is_intrinsic name = contains name "llvm." in
  let structM = Annotate.get_structM() in
  log ("tenv: " ^ Pprint.string_of_tenv structM) ; 
  let tenv = Lower.lower_tenv Lower.lo structM in
  let c =
    { Tc.c_fs = funcs ;
      Tc.c_lo = Lower.lo ;
      Tc.c_tenv = tenv 
    }
  in
    List.fold_left 
      ( fun acc f ->
	  if is_intrinsic f.SCast.f_lab then acc
	  else if List.length f.SCast.f_body = 0 then acc
	  else
	    ( try
	      log ("tc: " ^ f.SCast.f_lab) ; 
	      let fpkg = Lower.lower_func Lower.lo structM gprgns globsM f in
	      log (f.SCast.f_lab) ; 
	      log (Lower.string_of_psi fpkg.Lower.psi) ; 
	      if Tc.tc_function c (fpkg.Lower.delta1) (fpkg.Lower.delta2) (fpkg.Lower.psi) (fpkg.Lower.func)
	      then 
		( print_endline ("tc_func: " ^ f.SCast.f_lab ^ " succeeded") ;
		  acc
		)
	      else 
		( print_endline ("tc_func: " ^ f.SCast.f_lab ^ " failed") ;
		  false
		)
	      with Failure s -> (print_endline ("tc_func: " ^ f.SCast.f_lab ^ " " ^ s) ; false)
	    )
      ) true funcs

let main in_filename =
  let ic = global_context () in
  let imbuf = MemoryBuffer.of_file in_filename in

  let im = Llvm_bitreader.parse_bitcode ic imbuf in
  let (gprgns, globsM, funcs) = translate_module in_filename im in
  print_endline ("Gprgns:\n" ^ Pprint.string_of_gprgns gprgns) ; 
  print_endline ("Globs:\n" ^ Pprint.string_of_globsM globsM) ; 
  print_endline (Pprint.string_of_funs funcs) ; 
  ( if tc_all gprgns globsM funcs 
    then print_endline "Typechecking program succeeded"
    else print_endline "Typechecking program failed" 
  ) ;

  ()
	
let _ = 
  let len = Array.length Sys.argv in
  if len < 1 then
    failwith "# of argv is 0"
  else
    main (Array.get Sys.argv 1)

