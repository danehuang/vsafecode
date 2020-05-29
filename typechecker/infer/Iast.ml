open Pprint

type rvar = string * string (* (function name, region name) *)
type tvar = string * string (* (function name, tvar name) *)
type svar = string * string (* (function name, svar name) *)

type size = 
  | Size_const of int
  | Size_var of svar

(* Types that are present during inference. *)
type tipe =
  | Tipe_float
  | Tipe_double
  | Tipe_int of int
  | Tipe_ptr of tipe * rvar
  | Tipe_ptrU of size * rvar
  | Tipe_struct of tipe list
  | Tipe_fun of rvar list * tipe list * tipe option
  | Tipe_array of tipe * int
  | Tipe_tvar of tvar
  | Tipe_join of tipe list
  | Tipe_scheme of rvar list * tipe

type rgn_scheme = (rvar list * rvar list) option

(* Constraint's that are generated during inference. *)
type sc_constraint =
  | Tipe_eq of tipe * tipe               (* t1 = t2 *)
  | Tipe_size of tipe * int              (* sizeof(t) = sz *)
  (* | Rgn_scheme of tipe * rgn_scheme   (* Forall(r1, ..., rn). t *) *)
  | Size_geq of svar * int               (* szv >= int *)
  (* | Disjunct of sc_constraint list    (* c1 \/ c2 \/ ... \/ cn *) *)

type sc_constraint2 = string * sc_constraint (* location, constraint *)

(*----------------------------------------------------------------------------*)
let is_float t = 
  match t with
    | Tipe_float -> true
    | _ -> false

let is_double t = 
  match t with
    | Tipe_double -> true
    | _ -> false

let is_int t = 
  match t with
    | Tipe_int _ -> true
    | _ -> false

let is_ptr t =
  match t with
    | Tipe_ptr _ -> true
    | _ -> false

let is_ptrU t =
  match t with
    | Tipe_ptrU _ -> true
    | _ -> false

let is_struct t = 
  match t with
    | Tipe_struct _ -> true
    | _ -> false

let is_fun t = 
  match t with
    | Tipe_fun _ -> true
    | _ -> false

let is_array t = 
  match t with
    | Tipe_array _ -> true
    | _ -> false

let is_tvar t = 
  match t with
    | Tipe_tvar _ -> true
    | _ -> false

let is_join t = 
  match t with
    | Tipe_join _ -> true
    | _ -> false

let is_scheme t = 
  match t with
    | Tipe_scheme _ -> true
    | _ -> false

let get_scheme_tipe t = 
  match t with
    | Tipe_scheme(rs, t) -> t
    | _ -> failwith "expected tipe scheme but none found"

(*----------------------------------------------------------------------------*)
(* Pretty-printing *)

let string_of_rvar rv =
  let (fname, r) = rv in
  fname ^ "." ^ r

let string_of_rvars rvs = 
  sep_by ", " string_of_rvar rvs

let string_of_tvar tv =
  let (fname, t) = tv in
  fname ^ "." ^ t

let string_of_svar sv = 
  let (fname, sz) = sv in
  fname ^ "." ^ sz

let string_of_size sz =
  match sz with
    | Size_const i -> string_of_int i
    | Size_var(fname, s) -> string_of_svar (fname, s)

let rec string_of_tipe t =
  match t with
    | Tipe_float -> "float"
    | Tipe_double -> "double"
    | Tipe_int(sz) -> "i" ^ string_of_int(sz)
    | Tipe_ptr(t, r) -> string_of_tipe t ^ "*" ^ string_of_rvar r
    | Tipe_ptrU(sv, r) -> "U(" ^ string_of_size sv ^ ")*" ^ string_of_rvar r
    | Tipe_struct(ts) -> "{" ^ sep_by ", " string_of_tipe ts ^ "}"
    | Tipe_fun(rs, ts, t) -> 
	(match t with
	  | Some t -> string_of_tipe t ^ " <" ^ string_of_rvars rs ^ ">(" ^ sep_by ", " string_of_tipe ts ^ ")"
	  | None -> "void <" ^ string_of_rvars rs ^ ">(" ^ sep_by ", " string_of_tipe ts ^ ")" 
	)
    | Tipe_array(t, sz) -> "[" ^ string_of_tipe t ^ " x " ^ string_of_int sz ^ "]"
    | Tipe_tvar(tv) -> string_of_tvar tv
    | Tipe_join(ts) -> "join(" ^ sep_by ", " string_of_tipe ts ^ ")"
    | Tipe_scheme(rs, t) -> "<" ^ string_of_rvars rs ^ ">" ^ string_of_tipe t

let string_of_tipes ts = 
  sep_by ", " string_of_tipe ts 

let string_of_scheme rs = 
  let (rvs1, rvs2) = rs in
  "<" ^ string_of_rvars rvs1 ^ "> <" ^ string_of_rvars rvs2 ^ ">"

let rec string_of_c c =
  match c with
    | Tipe_eq(t1, t2) -> string_of_tipe t1 ^ " = " ^ string_of_tipe t2
    | Tipe_size(t, sz) -> "sizeof(" ^ string_of_tipe t ^ ") = " ^ string_of_int sz
    | Size_geq(sv, i) -> string_of_svar sv ^ " >= " ^ string_of_int i

let string_of_c2 (tag, c) =
  "(" ^ tag ^ ", " ^ string_of_c c ^ ")"

let string_of_cs cs =
  sep_by "\n" string_of_c2 cs

(* Var map *)
module VMap = Map.Make(struct type t = (string * string) let compare = compare end)

module VSet = Set.Make(struct type t = (string * string) let compare = compare end)

let modify_vmap m x v = 
  m := VMap.add x v !m

let get_vmap m x =
  VMap.find x !m

let string_of_tipeM gamma =
  VMap.fold (fun (fname, k) v acc -> fname ^ "." ^ k ^ ": " ^ string_of_tipe v ^ "\n" ^ acc) gamma ""

let string_of_schemeM gamma =
  VMap.fold (fun (fname, k) v acc -> 
	       fname ^ "." ^ k ^ ": " ^ string_of_scheme v ^ "\n" ^ acc
	    ) gamma ""

let string_of_strM strM = 
  VMap.fold (fun (fname, k) v acc -> fname ^ "." ^ k ^ ": " ^ v ^ "\n" ^ acc) strM ""

let string_of_delta m =
  VMap.fold (fun (fname, k) (sz, t) acc -> fname ^ "." ^ k ^ ": (" ^ string_of_int sz ^ ", " ^ string_of_tipe t ^ ")\n" ^ acc) m ""
