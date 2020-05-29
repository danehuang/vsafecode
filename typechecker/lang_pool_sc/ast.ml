type nat = int
type rgn = string
type id = string
type lab = string

type typ =
| Typ_float
| Typ_int of nat
| Typ_ptr of typ * rgn
| Typ_name of id * rgn list
| Typ_fun of rgn list * typ list * typ option
| Typ_unknown 

type ftyp =
| Ftyp_float
| Ftyp_int of nat
| Ftyp_ptr of typ * rgn
| Ftyp_fun of rgn list * typ list * typ option
| Ftyp_unknown

type pooltyps = (rgn * (rgn list) * (typ list)) list

type fpooltyps = (string * pooltyps * id list) list

let rec sep_by sep f ls =
  match ls with
    | [] -> ""
    | hd::[] -> f hd
    | hd::ls -> f hd ^ sep ^ sep_by sep f ls

let string_of_rgns rgns =
  sep_by ", " (fun x -> x) rgns

let rec string_of_typ t =
  match t with
    | Typ_unknown -> "UNKNOWN"
    | Typ_float -> "float"
    | Typ_int(sz) -> "i" ^ string_of_int sz
    | Typ_ptr(t,r) -> string_of_typ t ^ "*" ^ r
    | Typ_name(name,rgns) -> name ^"<" ^ ">"
    | Typ_fun(rgns, ts, ret) ->
	let rgns' = string_of_rgns rgns in
	let ts' = sep_by ", " string_of_typ ts in
	match ret with
	  | None -> "<" ^ rgns' ^ ">(" ^ ts' ^ ")"
	  | Some t -> string_of_typ t ^ " <" ^ rgns' ^ ">(" ^ ts' ^ ")" 

let rec string_of_ftyp t =
  match t with
    | Ftyp_unknown -> "FUNKNOWN"
    | Ftyp_float -> "ffloat"
    | Ftyp_int(sz) -> "fi" ^ string_of_int sz
    | Ftyp_ptr(t, r) -> string_of_typ t ^ "*" ^ r
    | Ftyp_fun(rgns, ts, ret) ->
	let rgns' = string_of_rgns rgns in
	let ts' = sep_by ", " string_of_typ ts in
	match ret with
	  | None -> "<" ^ rgns' ^ ">(" ^ ts' ^ ")"
	  | Some t -> string_of_typ t ^ " <" ^ rgns' ^ ">(" ^ ts' ^ ")" 

let string_of_ftyps ts =
  sep_by ", " string_of_ftyp ts

let string_of_pooltyp (r, rgns, ts) =
  r ^ "(" ^ string_of_rgns rgns ^ "): " ^ sep_by ", " string_of_typ ts

let string_of_pooltyps pts = 
  sep_by "\n" string_of_pooltyp pts

let string_of_fpooltyps fpts = 
  sep_by "\n" (fun (f, pts,params) -> 
		 f ^ " (" ^ sep_by ", " (fun x -> x) params ^ ") {\n" ^ string_of_pooltyps pts ^ "}\n"
	      ) fpts
