open Utility
open Ast

let parse_name filename : string =
  let i = String.index filename '.' in
  (String.sub filename 0 i) ^ ".pool"
 
let parse_file filename : fpooltyps =
  let ch = open_in (parse_name filename) in
  Parse.program Lex.lexer (Lexing.from_channel ch)

let is_unknown t : bool =
  match t with
    | Typ_int(7) -> true
    | _ -> false

let rec translate_typ (poolM:SCast.rgn SMap.t) (r:rgn) (t:typ) : SCast.typ =
  match t with
    | Typ_unknown -> SCast.Typ_int(7)
    | Typ_float -> SCast.Typ_float
    | Typ_int(sz)-> SCast.Typ_int(sz)
    | Typ_ptr(t, r') -> 
	let r'' = SMap.find r poolM in
	if is_unknown t
	then SCast.Typ_ptrU(1, r'')
	else SCast.Typ_ptr(translate_typ poolM r'' t, r'')
    | Typ_name(x, rgns) -> SCast.Typ_name(x, rgns)
    | Typ_fun(rgns, ts, rt) -> 
	let rt = 
	  match rt with
	    | Some t -> Some (translate_typ poolM r t)
	    | None -> None
	in
	SCast.Typ_fun(rgns, List.map (translate_typ poolM r) ts, rt)

let buildPoolInfo' (pts:(rgn * (rgn list) * (typ list)) list) : (SCast.rgn SMap.t * SCast.typ SMap.t) =
  let poolM = List.fold_left 
    ( fun acc (r, rgns, ts) ->
	try 
	  let h = List.hd rgns in
	  SMap.add r h acc
	with hd -> 
	  SMap.add r "" acc
    ) SMap.empty pts
  in
  let poolTypM = List.fold_left
    ( fun acc (r, rgns, ts) ->
	try
	  let t = List.hd ts in
	  let t' = translate_typ poolM r t in
	  SMap.add r t' acc
	with hd ->
	  acc
    ) SMap.empty pts
  in
  let poolM = SMap.add "" "" poolM in     (* corner case *)
  let poolM = SMap.add "NA" "NA" poolM in (* corner case *)
    ( poolM, poolTypM )
	    
let buildPoolInfo filename : (SCast.rgn SMap.t SMap.t * SCast.typ SMap.t SMap.t * string list SMap.t) =
  let fpts = parse_file filename in
  List.fold_left
    ( fun (acc1, acc2, acc3) (f, pts, params) -> 
	let (poolM, poolTypM) = buildPoolInfo' pts in
	(SMap.add f poolM acc1, SMap.add f poolTypM acc2, SMap.add f params acc3)
    ) (SMap.empty, SMap.empty, SMap.empty) fpts

let string_of_poolinfo1' (poolM:SCast.rgn SMap.t) = 
  SMap.fold ( fun k v acc -> 
		k ^ ": " ^ v ^ "\n" ^ acc
	    ) poolM ""

let string_of_poolinfo2' (poolTypM:SCast.typ SMap.t) =
  SMap.fold ( fun k v acc ->
		k ^ ": " ^ Pprint.string_of_typ v ^ "\n" ^ acc
	    ) poolTypM ""

let string_of_poolinfo ((poolM, poolTypM):(SCast.rgn SMap.t SMap.t * SCast.typ SMap.t SMap.t)) =
  let str1 = SMap.fold ( fun k v acc ->
			   k ^ "{\n" ^ string_of_poolinfo1' v ^ "}\n" ^ acc
		       ) poolM "" in
  let str2 = SMap.fold ( fun k v acc ->
			   k ^ "{\n" ^ string_of_poolinfo2' v ^ "}\n" ^ acc
		       ) poolTypM "" in
  "poolConn:\n" ^ str1 ^ "\npoolTyp:\n" ^ str2
