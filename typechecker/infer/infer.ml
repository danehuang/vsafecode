open Utility
open Iast
open Pprint

(* debugging functions *)
let debug = ref true
let log str =
  if (!debug) then print_endline str else ()

let gamma : tipe SMap.t ref = ref SMap.empty          (* program var -> tipe *)
let delta : (int * tipe) SMap.t ref = ref SMap.empty  (* region var -> (size * tipe) *)
let kappa : sc_constraint list ref = ref []              (* set of constraints *)
let tvarM : string SMap.t ref = ref SMap.empty

let instantiate_rgn rmap (fname, r) = 
  if contains r "GlobalPool" then
    try VMap.find ("G", r) rmap with Not_found -> (fname, r)
  else
    try VMap.find (fname, r) rmap with Not_found -> (fname, r)

let rec instantiate_tipe rmap t = 
  match t with
    | Tipe_float -> t
    | Tipe_double -> t
    | Tipe_int sz -> t
    | Tipe_ptr(t, r) -> Tipe_ptr(instantiate_tipe rmap t, instantiate_rgn rmap r)
    | Tipe_ptrU(sz, r) -> Tipe_ptrU(sz, instantiate_rgn rmap r)
    | Tipe_struct ts -> Tipe_struct (List.map (instantiate_tipe rmap) ts)
    | Tipe_fun(rs, ts, t) -> Tipe_fun (List.map (instantiate_rgn rmap) rs, List.map (instantiate_tipe rmap) ts, lift_opt (instantiate_tipe rmap) t)
    | Tipe_array(t', sz) -> Tipe_array(instantiate_tipe rmap t', sz)
    | Tipe_tvar _ -> t
    | Tipe_join ts -> Tipe_join (List.map (instantiate_tipe rmap) ts)
    | Tipe_scheme(rs, t) -> Tipe_scheme(rs, instantiate_tipe rmap t)

let instantiate_prgns prgns prgns' = 
  List.fold_left 
    (fun acc ((fname1, r1), (fname2, r2)) -> 
       if contains r1 "GlobalPool" then
	 VMap.add ("G", r1) (fname2, r2) acc
       else
	 VMap.add (fname1, r1) (fname2, r2) acc
    ) VMap.empty (List.combine prgns prgns')

(* Check to see if a tipe variable tv appears in tipe t. *)
let rec occurs tv t = 
  match t with
    | Tipe_float -> false
    | Tipe_double -> false
    | Tipe_int(sz) -> false
    | Tipe_ptr(t, r) -> occurs tv t
    | Tipe_ptrU(sz, r) -> false
    | Tipe_struct(ts) -> List.fold_left (fun acc t -> occurs tv t || acc) false ts
    | Tipe_fun(rs, ts, tret) -> 
	let b = (List.fold_left (fun acc t -> occurs tv t || acc) false ts) in
	(match tret with
	   | Some tret -> occurs tv tret || b
	   | None -> b
	)
    | Tipe_array(t, sz) -> occurs tv t
    | Tipe_tvar(tv') -> tv = tv'
    | Tipe_join(ts) -> List.fold_left (fun acc t -> occurs tv t || acc) false ts
    | Tipe_scheme(rs, t) -> occurs tv t

(* Substitute a tipe for a tipe variable in a tipe. *)
let rec sub_tv_tipe tv t' t =
  match t with
    | Tipe_float -> t
    | Tipe_double -> t
    | Tipe_int(sz) -> t
    | Tipe_ptr(t, r) -> Tipe_ptr(sub_tv_tipe tv t' t, r)
    | Tipe_ptrU(sz, r) -> t
    | Tipe_struct(ts) -> Tipe_struct(List.map (sub_tv_tipe tv t') ts)
    | Tipe_fun(rs, ts, tret) -> 
	Tipe_fun(rs, List.map (sub_tv_tipe tv t') ts, lift_opt (sub_tv_tipe tv t') tret)
    | Tipe_array(t, sz) -> Tipe_array(sub_tv_tipe tv t' t, sz)
    | Tipe_tvar(tv') -> 
	if tv = tv' then t' else Tipe_tvar tv'
    | Tipe_join(ts) -> Tipe_join(List.map (sub_tv_tipe tv t') ts)
    | Tipe_scheme(rs, t) -> Tipe_scheme(rs, sub_tv_tipe tv t' t)

(* Substitute a tipe for a tipe variable in a constraint. *)
let rec sub_tv_c tv t' c =
  match c with
    | Tipe_eq(t1, t2) -> Tipe_eq(sub_tv_tipe tv t' t1, sub_tv_tipe tv t' t2)
    | Tipe_size(t, sz) -> Tipe_size(sub_tv_tipe tv t' t, sz)
    | Size_geq(sv, sz) -> c

(* Substitute a tipe for a tipe variable in a list of constraints. *)
let sub_tv_cs tv t' cs =
  List.map (fun (tag, c) -> (tag, sub_tv_c tv t' c)) cs

let sub_tv_c_change tv t' (c:sc_constraint) = 
  let c' = sub_tv_c tv t' c in
  (c = c', c')

let sub_tv_blacklist tv t' (bls: (bool * sc_constraint) list) = 
  let bls' = 
    List.map (fun (change, c) -> 
		let (change', c') = sub_tv_c_change tv t' c in
		  (change', c')
	     ) bls
  in
    List.filter (fun (change, c) -> not change) bls'

(* Substitute a tipe for a tipe variable in our gamma context. *)
let sub_tv_gamma tv t' (gamma:tipe VMap.t) =
  VMap.map (fun t -> (sub_tv_tipe tv t' t)) gamma

(* Substitute a tipe for a tipe variable in our delta context. *)
let sub_tv_delta tv t' (delta:(int * tipe) VMap.t) =
  VMap.map (fun (i, t) -> (i, sub_tv_tipe tv t' t)) delta

(* Substitute a tipe for a tipe variable in our substitution context. *)
let sub_tv_subM tv t' (subM:tipe VMap.t) =
  VMap.map (sub_tv_tipe tv t') subM

(* Substitute a size for a size variable in a size variable *)
let sub_sz_var sv1 sv2 sv =
  if sv1 = sv then sv2 else sv

(* Substitute a size for a size variable in a size. *)
let sub_sz sv sz' sz = 
  match sz with
    | Size_const i -> sz
    | Size_var sv'' -> if sv = sv'' then sz' else sz

(* Substitute a size for a size variable in a tipe. *)
let rec sub_sz_tipe sv sz t =
  match t with
    | Tipe_float -> t
    | Tipe_double -> t
    | Tipe_int(sz) -> t
    | Tipe_ptr(t, r') -> Tipe_ptr(sub_sz_tipe sv sz t, r')
    | Tipe_ptrU(sc, r') -> Tipe_ptrU(sub_sz sv sz sc, r')
    | Tipe_struct(ts) -> Tipe_struct(List.map (sub_sz_tipe sv sz) ts)
    | Tipe_fun(rs, ts, t') -> Tipe_fun(rs, List.map (sub_sz_tipe sv sz) ts, lift_opt (sub_sz_tipe sv sz) t')
    | Tipe_array(t, sz') -> Tipe_array(sub_sz_tipe sv sz t, sz')
    | Tipe_tvar(tv) -> t
    | Tipe_join(ts) -> Tipe_join(List.map (sub_sz_tipe sv sz) ts)
    | Tipe_scheme(rs, t) -> Tipe_scheme(rs, sub_sz_tipe sv sz t)

(* Substitute a size for a size variable in a constraint. *)
let rec sub_sz_c sv sz c =
  match c with
    | Tipe_eq(t1, t2) -> Tipe_eq(sub_sz_tipe sv sz t1, sub_sz_tipe sv sz t2)
    | Tipe_size(t, sz') -> Tipe_size(sub_sz_tipe sv sz t, sz')
    | Size_geq(sv', sz') -> 
	(match sz with
	   | Size_const _ -> c
	   | Size_var sv'' -> Size_geq(sub_sz_var sv sv'' sv', sz')
	)

(* Substitute a size constraint for a size constraint in a list of constraints. *)
let sub_sz_cs sv sz cs = 
  List.map (fun (tag, c) -> (tag, sub_sz_c sv sz c)) cs

let sub_sz_c_change tv t' c = 
  let c' = sub_sz_c tv t' c in
  (c = c', c')

let sub_sz_blacklist tv t' bls = 
  let bls' = 
    List.map (fun (change, c) -> 
		let (change', c') = sub_sz_c_change tv t' c in
		  (change', c')
	     ) bls
  in
    List.filter (fun (change, c) -> not change) bls'

let sub_sz_gamma sv sz (gamma:tipe VMap.t) =
  VMap.map (sub_sz_tipe sv sz) gamma

let sub_sz_delta sv sz (delta:(int * tipe) VMap.t) =
  VMap.map (fun (i, t) -> (i, sub_sz_tipe sv sz t)) delta

(*----------------------------------------------------------------------------*)
(* Unification *)

let rvarc = counter() (* region variable counter *)

let fresh_rvar fname =
  let tmp = fresh rvarc in
  (fname, "RV" ^ string_of_int tmp)

let sizes : (tipe * int) list ref = ref []     (* (Tipe var, size) list *)

let resetSizes() = sizes := []

let string_of_sizeM sizeM =
  VMap.fold (fun k v acc ->
	       string_of_svar k ^ " = " ^ string_of_int v ^ "\n" ^ acc) sizeM ""

let rec unify_list tag ts1 ts2 =
  match ts1, ts2 with
    | [], [] -> []
    | t1::ts1, t2::ts2 -> (tag, Tipe_eq(t1, t2)) :: unify_list tag ts1 ts2
    | _, _ -> []

let rec flatten_join t = 
  match t with
    | Tipe_join ts' -> List.fold_left (fun acc t -> flatten_join t @ acc) [] ts'
    | _ -> [t]

let unify_sub blacklist delta subM sizeM gamma extracs cs tv t =
  let blacklist' = sub_tv_blacklist tv t blacklist in
  let delta' = sub_tv_gamma tv t delta in
  let subM' = sub_tv_gamma tv t (VMap.add tv t subM) in
  let sizeM' = sizeM in
  let gamma' = sub_tv_gamma tv t gamma in
  let extracs' = sub_tv_cs tv t extracs in
  let cs' = sub_tv_cs tv t cs in
  (blacklist', delta', subM', sizeM', gamma', extracs', cs')

let rec unify_size sz1 sz2 =
  match sz1, sz2 with
    | Size_var sv1, Size_var sv2 -> Some (sv1, sz2)
    | Size_var sv, Size_const i -> Some (sv, sz2)
    | Size_const i, Size_var sv -> Some (sv, sz1)
    | Size_const i1, Size_const i2 ->
	if i1 <> i2 then 
	  failwith "inconsistent constant sizes"
	else
	  None

let unify_join_int blacklist delta subM sizeM gamma extracs cs t1 t2 = 
  match t1, t2 with
    | Tipe_int sz1, Tipe_int sz2 -> 
	if sz1 = sz2 then 
	  (blacklist, delta, subM, sizeM, gamma, extracs, cs)
	else failwith "different sized ints"
    | Tipe_int _, Tipe_tvar _
    | Tipe_tvar _, Tipe_int _
    | Tipe_tvar _, Tipe_tvar _ -> (blacklist, delta, subM, sizeM, gamma, extracs, ("join int", Tipe_eq(t1, t2)) :: cs)
    | Tipe_int _, Tipe_ptrU _
    | Tipe_ptrU _, Tipe_int _
    | Tipe_int _, Tipe_ptr _
    | Tipe_ptr _, Tipe_int _ 
    | Tipe_join _, Tipe_int _ 
    | Tipe_int _, Tipe_join _ -> (blacklist, delta, subM, sizeM, gamma, extracs, cs)
    | _, _ -> 
	(blacklist, delta, subM, sizeM, gamma, extracs, cs)

let rec unify_size' sz1 sz2 =
  match sz1, sz2 with
    | Size_var sv1, Size_var sv2 -> Some (sv1, sz2)
    | Size_var sv, Size_const i -> Some (sv, sz2)
    | Size_const i, Size_var sv -> None (* Some (sv, sz1) *)
    | Size_const i1, Size_const i2 ->
	if i1 <> i2 then 
	  failwith "inconsistent constant sizes"
	else
	  None

let unify_join_ptrU blacklist delta subM sizeM gamma extracs cs t1 t2 = 
  match t1, t2 with
    | Tipe_ptrU(sz1, r1), Tipe_ptrU(sz2, r2) ->
	(match sz1, sz2 with
	   | Size_var sv1, Size_var sv2 ->
	       let sz1 = try VMap.find sv1 sizeM with Not_found -> 0 in
	       let sz2 = try VMap.find sv2 sizeM with Not_found -> 0 in 
	       let sizeM' = 
		 if sz2 = 0 then
		   VMap.add sv2 sz1 sizeM
		 else
		   sizeM
	       in
		 (blacklist, delta, subM, sizeM', gamma, extracs, cs)
	   | Size_var sv, Size_const sz ->
	       let sz' = try VMap.find sv sizeM with Not_found -> sz in
	       let sizeM' = VMap.add sv (min sz sz') sizeM in
	       (blacklist, delta, subM, sizeM', gamma, extracs, cs)
	   | _, _ -> (blacklist, delta, subM, sizeM, gamma, extracs, cs)
	)
    | _, _ -> (blacklist, delta, subM, sizeM, gamma, extracs, cs)

let unify_join_ptrU' blacklist delta subM sizeM gamma extracs (cs:sc_constraint2 list) t ts = 
  let szs = 
    List.map (fun t ->
		match t with
		  | Tipe_ptrU(sz, _) ->
		      (match sz with 
			 | Size_const i -> i
			 | Size_var sv -> try VMap.find sv sizeM with Not_found -> 0
		      )
		  | _ -> 0  
	     ) ts
  in
  let acc = try List.hd szs with _ -> 0 in
  let sz = List.fold_left (fun acc i -> min acc i) acc szs in
  let t' = 
    List.find (fun t ->
		 match t with
		   | Tipe_ptrU(sz1, r1) -> true
		   | _ -> false
	      ) ts
  in
  let pool = 
    match t' with
      | Tipe_ptrU(sz1, r1) -> r1
      | _ -> failwith "no region found in unify_join_ptrU'"
  in
  (blacklist, delta, subM, sizeM, gamma, extracs, ("join ptrU'", Tipe_eq(t, Tipe_ptrU(Size_const sz, pool))) :: cs)

let unify_join_ptr blacklist delta subM sizeM gamma extracs cs t1 t2 = 
  match t1, t2 with 
    | Tipe_ptr(t1, r1), Tipe_ptr(t2, r2) ->
	(* if r1 = r2 then *)
	  (blacklist, delta, subM, sizeM, gamma, extracs, ("join ptr", Tipe_eq(t1, t2)) :: cs)
        (* else failwith "different regions in ptr during unification" *)
    | Tipe_ptr _, Tipe_tvar _ 
    | Tipe_tvar _, Tipe_ptr _ 
    | Tipe_tvar _, Tipe_tvar _ -> (blacklist, delta, subM, sizeM, gamma, extracs, ("join ptr", Tipe_eq(t1, t2)) :: cs)
    | _, _ -> failwith "found non-ptr or non-tvar in unify_join_ptr"

let unify_join blacklist delta subM sizeM gamma extracs cs f t ts =
  let ts' = List.map (fun t' -> (t, t')) ts in
    List.fold_left (fun (blacklist, delta, subM, sizeM, gamma, extracs, cs) (t1, t2) ->
		      f blacklist delta subM sizeM gamma extracs cs t1 t2)
      (blacklist, delta, subM, sizeM, gamma, extracs, cs)
      ts'

let instantiate_join t1 ts = 
  match t1 with
    | Tipe_scheme(rs1, t1) ->
	List.map (fun t2 ->
		    match t2 with
		      | Tipe_scheme(rs2, t2) ->
			  instantiate_tipe (instantiate_prgns rs2 rs1) t2
		      | _ -> failwith "expected tipe scheme"
		 ) ts
    | _ -> failwith "expected tipe scheme"

let uncurry6 f (a, b, c, d, e, g) = f a b c d e g
let uncurry7 f (a, b, c, d, e, g, h) = f a b c d e g h

let is_scheme_tvar t =
  match t with
    | Tipe_scheme (_, Tipe_tvar _) -> true
    | _ -> false

let rec unify blacklist delta subM sizeM gamma extracs cs = 
  match cs with
    | [] -> (delta, subM, sizeM, gamma, extracs)
    | (tag, c)::cs ->
	log ("unifying constraint: " ^ string_of_c2 (tag, c)) ; 
	(match c with
	  | Tipe_eq(t1, t2) -> 
	      (match t1, t2 with
		 (* Joins *)
		 | Tipe_join ts, t
		 | t, Tipe_join ts ->
		     if not (List.mem (false, c) blacklist) then
		       ( if List.exists is_scheme_tvar ts then
			   ( (* blacklist *)
			     unify ((false, c) :: blacklist) delta subM sizeM gamma extracs (cs @ [(tag, c)])
			   )
			 else if List.exists is_scheme ts then
			   ( let ts' = instantiate_join t ts in
			     unify blacklist delta subM sizeM gamma extracs ((tag, Tipe_eq(get_scheme_tipe t, Tipe_join ts')) :: cs)
			   )
		         else if List.exists is_int ts then
			   ( let t' = List.find is_int ts in
			     let cs' = (tag, Tipe_eq(t, t')) :: cs in
			     uncurry7 unify (unify_join blacklist delta subM sizeM gamma extracs cs' unify_join_int t' ts)
			   )
			 else if is_int t then
			   ( uncurry7 unify (unify_join blacklist delta subM sizeM gamma extracs cs unify_join_int t ts)
			   )
			 else if List.exists is_tvar ts then
			   ( (* blacklist *)
			     unify ((false, c) :: blacklist) delta subM sizeM gamma extracs (cs @ [(tag, c)])
			   )
			 else
			   ( (* solve normally *)
			     match t with
			       | Tipe_tvar tv ->
				   if List.exists is_ptrU ts then
				     uncurry7 unify (unify_join_ptrU' blacklist delta subM sizeM gamma extracs cs t ts)
				   else
				     unify blacklist delta subM sizeM gamma extracs 
				       ((tag, Tipe_eq(List.hd ts, Tipe_join (List.tl ts))) :: (tag, Tipe_eq(Tipe_tvar tv, List.hd ts)) :: cs)
			       | Tipe_int sz ->
				   unify blacklist delta subM sizeM gamma extracs cs
			       | Tipe_float ->
				   unify blacklist delta subM sizeM gamma extracs cs
			       | Tipe_double ->
				   unify blacklist delta subM sizeM gamma extracs cs
			       | Tipe_ptr _ ->
				   uncurry7 unify (unify_join blacklist delta subM sizeM gamma extracs cs unify_join_ptr t ts)
			       | Tipe_ptrU _ ->
				   uncurry7 unify (unify_join blacklist delta subM sizeM gamma extracs cs unify_join_ptrU t ts)
			       | Tipe_struct _ ->
				   unify blacklist delta subM sizeM gamma extracs cs
			       | Tipe_array _ ->
				   unify blacklist delta subM sizeM gamma extracs cs
			       | Tipe_fun _ ->
				   unify blacklist delta subM sizeM gamma extracs cs
			       | Tipe_join _ ->
				   unify blacklist delta subM sizeM gamma extracs cs
			       | Tipe_scheme(rs, t) ->
				   unify blacklist delta subM sizeM gamma extracs cs
			   )
		       )
		     else
		       ( if List.exists is_scheme ts then
			   ( let ts' = instantiate_join t ts in
			     unify blacklist delta subM sizeM gamma extracs ((tag, Tipe_eq(get_scheme_tipe t, Tipe_join ts')) :: cs)
			   )
			 else
			   unify blacklist delta subM sizeM gamma extracs cs
		       )

		 (* Tipe variables *)
		 | Tipe_tvar tv, _ -> 
		     if not (occurs tv t2) then
		       ( uncurry7 unify (unify_sub blacklist delta subM sizeM gamma extracs cs tv t2)
		       )
		     else unify blacklist delta subM sizeM gamma extracs cs
		 | _, Tipe_tvar tv ->
		     if not (occurs tv t1) then
		       ( uncurry7 unify (unify_sub blacklist delta subM sizeM gamma extracs cs tv t1)
		       )
		     else unify blacklist delta subM sizeM gamma extracs cs

		 (* Base tipes *)
		 | Tipe_float, Tipe_float ->
		     unify blacklist delta subM sizeM gamma extracs cs
		 | Tipe_double, Tipe_double ->
		     unify blacklist delta subM sizeM gamma extracs cs
		 | Tipe_int(sz1), Tipe_int(sz2) -> 
		     if sz1 = sz2 then 
		       unify blacklist delta subM sizeM gamma extracs cs
		     else 
		       failwith "different sized ints during unification"
		 | Tipe_ptr(t1, (f1, r1)), Tipe_ptr(t2, (f2, r2)) ->
		     if (r1 = r2 && f1 = f2) || f1 <> f2 then
		       if t1 = t2 then
			 unify blacklist delta subM sizeM gamma extracs cs
		       else
			 unify blacklist delta subM sizeM gamma extracs ((tag, Tipe_eq(t1, t2))::cs)
		     else failwith ("different regions in ptr during unification: " ^ string_of_rvar (f1, r1) ^ " " ^ string_of_rvar (f2, r2)) 
		 | Tipe_ptrU(sz1, (f1, r1)), Tipe_ptrU(sz2, (f2, r2)) ->
		     if (r1 = r2 && f1 = f2) || f1 <> f2 then
		       ( match unify_size sz1 sz2 with
			   | Some(sv, sz) ->
			       let delta = sub_sz_gamma sv sz delta in
			       let subM = sub_sz_gamma sv sz subM in
			       let gamma = sub_sz_gamma sv sz gamma in
			       let sizeM = 
				 (match sz with
				    | Size_const i -> sizeM
				    | Size_var sv' -> 
					let sz = try VMap.find sv sizeM with Not_found -> 0 in
					let sz' = try VMap.find sv' sizeM with Not_found -> 0 in
					VMap.add sv' (max sz sz') sizeM
				 )
			       in
			       unify (sub_sz_cs sv sz blacklist) delta subM sizeM gamma (sub_sz_cs sv sz extracs) (sub_sz_cs sv sz cs)
			   | None ->
			       unify blacklist delta subM sizeM gamma extracs cs
		       )
		     else failwith ("different regions in ptrU during unification: " ^ string_of_rvar (f1, r1) ^ " " ^ string_of_rvar (f2, r2)) 
		 
		 (* Structs *)
		 | Tipe_struct ts1, Tipe_struct ts2 -> 
		     unify blacklist delta subM sizeM gamma extracs (unify_list tag ts1 ts2 @ cs)

		 (* Arrays *)
		 | Tipe_array(t1, sz1), Tipe_array(t2, sz2) ->
		     unify blacklist delta subM sizeM gamma extracs ((tag, Tipe_eq(t1, t2)) :: cs)

		 (* Functions *)
		 | Tipe_fun(rs1, ts1, tret1), Tipe_fun(rs2, ts2, tret2) ->
		     if List.length ts1 = List.length ts2 then
		       if List.length rs1 = List.length rs2 then
			 ( let sig_cs = unify_list tag ts1 ts2 in
			   let ret_cs = 
			     match tret1, tret2 with
			       | Some tret1, Some tret2 -> [(tag, Tipe_eq(tret1, tret2))]
			       | None, None -> []
			       | _, _ -> failwith "function return types differ"
			   in
			     unify blacklist delta subM sizeM gamma extracs (ret_cs @ sig_cs @ cs)
			 )
		       else
			 failwith "functions differ in number of polymorphic regions."
		     else
		       failwith "functions differ in number of arguments."
		       
		 (* Subtyping with ints and pointers *)
		 | Tipe_ptr _, Tipe_int _
		 | Tipe_int _, Tipe_ptr _
		 | Tipe_ptrU _, Tipe_int _
		 | Tipe_int _, Tipe_ptrU _ ->
		     unify blacklist delta subM sizeM gamma extracs cs

		 (* Subtyping with ints and floats *)
		 | Tipe_int _, Tipe_float 
		 | Tipe_float, Tipe_int _ ->
		     unify blacklist delta subM sizeM gamma extracs cs

		 (* Subtyping with ints and doubles *)
		 | Tipe_int _, Tipe_double
		 | Tipe_double, Tipe_int _ ->
		     unify blacklist delta subM sizeM gamma extracs cs

		 (* Subtyping with structs and base tipes *)
		 | Tipe_float, Tipe_struct ts ->
		     unify blacklist delta subM sizeM gamma extracs ((tag, Tipe_eq(List.nth ts 0, t1)) :: cs)
		 | Tipe_double, Tipe_struct ts ->
		    unify blacklist delta subM sizeM gamma extracs ((tag, Tipe_eq(List.nth ts 0, t1)) :: cs) 
		 | Tipe_int _, Tipe_struct ts ->
		     unify blacklist delta subM sizeM gamma extracs ((tag, Tipe_eq(List.nth ts 0, t1)) :: cs)
		 | Tipe_ptr _, Tipe_struct ts ->
		     unify blacklist delta subM sizeM gamma extracs ((tag, Tipe_eq(List.nth ts 0, t1)) :: cs)
		 | Tipe_ptrU _, Tipe_struct ts ->
		     unify blacklist delta subM sizeM gamma extracs ((tag, Tipe_eq(List.nth ts 0, t1)) :: cs)
		 | Tipe_array _, Tipe_struct ts ->
		     unify blacklist delta subM sizeM gamma extracs ((tag, Tipe_eq(List.nth ts 0, t1)) :: cs)

		 | Tipe_struct ts, Tipe_float ->
		     unify blacklist delta subM sizeM gamma extracs ((tag, Tipe_eq(List.nth ts 0, t2)) :: cs)
		 | Tipe_struct ts, Tipe_double ->
		     unify blacklist delta subM sizeM gamma extracs ((tag, Tipe_eq(List.nth ts 0, t2)) :: cs)   
		 | Tipe_struct ts, Tipe_int _ ->
		     unify blacklist delta subM sizeM gamma extracs ((tag, Tipe_eq(List.nth ts 0, t2)) :: cs)
		 | Tipe_struct ts, Tipe_ptr _ ->
		     unify blacklist delta subM sizeM gamma extracs ((tag, Tipe_eq(List.nth ts 0, t2)) :: cs)
		 | Tipe_struct ts, Tipe_ptrU _ ->
		     unify blacklist delta subM sizeM gamma extracs ((tag, Tipe_eq(List.nth ts 0, t2)) :: cs)
		 | Tipe_struct ts, Tipe_array _ ->
		     unify blacklist delta subM sizeM gamma extracs ((tag, Tipe_eq(List.nth ts 0, t2)) :: cs)

		 (* Subtyping with arrays *)
		 | Tipe_float, Tipe_array(t, sz) ->
		     unify blacklist delta subM sizeM gamma extracs ((tag, Tipe_eq(t, t1)) :: cs)
		 | Tipe_double, Tipe_array(t, sz) ->
		     unify blacklist delta subM sizeM gamma extracs ((tag, Tipe_eq(t, t1)) :: cs)	       
		 | Tipe_int _, Tipe_array(t, sz) ->
		     unify blacklist delta subM sizeM gamma extracs ((tag, Tipe_eq(t, t1)) :: cs)
		 | Tipe_ptr _, Tipe_array(t, sz) ->
		     unify blacklist delta subM sizeM gamma extracs ((tag, Tipe_eq(t, t1)) :: cs)
		 | Tipe_ptrU _, Tipe_array(t, sz) ->
		     unify blacklist delta subM sizeM gamma extracs ((tag, Tipe_eq(t, t1)) :: cs)

		 | Tipe_array(t, sz), Tipe_float ->
		     unify blacklist delta subM sizeM gamma extracs ((tag, Tipe_eq(t, t2)) :: cs)
		 | Tipe_array(t, sz), Tipe_double ->
		     unify blacklist delta subM sizeM gamma extracs ((tag, Tipe_eq(t, t2)) :: cs)
		 | Tipe_array(t, sz), Tipe_int _ ->
		     unify blacklist delta subM sizeM gamma extracs ((tag, Tipe_eq(t, t2)) :: cs)
		 | Tipe_array(t, sz), Tipe_ptr _ ->
		     unify blacklist delta subM sizeM gamma extracs ((tag, Tipe_eq(t, t2)) :: cs)
		 | Tipe_array(t, sz), Tipe_ptrU _ ->
		     unify blacklist delta subM sizeM gamma extracs ((tag, Tipe_eq(t, t2)) :: cs)

		 | _ -> 
		     log "delta: " ;
		     log (string_of_tipeM delta) ;
		     log "subM: " ; 
		     log (string_of_tipeM subM) ;
		     log "gamma: " ; 
		     log (string_of_tipeM gamma) ;
		     log "sizeM: " ;
		     log (string_of_sizeM sizeM) ; 
		     log "remaining constraints: " ; 
		     log (string_of_cs cs) ;
		     failwith ("no matching cases in unify_one: " ^ string_of_c c)
	      )

	  | Tipe_size(t, sz) ->
	      sizes := (t, sz) :: !sizes ; 
	      unify blacklist delta subM sizeM gamma extracs cs

	  | Size_geq(sv, sz) ->
	      let sz' = try VMap.find sv sizeM with Not_found -> sz in
	      let sizeM = VMap.add sv (max sz sz') sizeM in
	      unify blacklist delta subM sizeM gamma extracs cs
	)

let rec collapse_join_one ts = 
  if List.exists is_int ts then
    List.find is_int ts
  else if List.exists is_ptr ts then
    List.find is_ptr ts
  else if List.exists is_ptrU ts then
    List.find is_ptrU ts
  else if List.exists is_join ts then
    ( let ts' = List.filter is_join ts in 
      let rec go ts' = 
	match ts' with
	  | [] -> failwith "everything failed"
	  | Tipe_join ts :: ts' -> (try collapse_join_one ts with _ -> go ts')
	  | _ -> failwith "shouldn't happen" 
      in
	go ts' 
    )
  else 
    failwith ("cannot collapse join: " ^ string_of_tipes ts)

(*
let collapse_joins delta subM sizeM gamma = 
  let gamma' = VMap.map (fun t -> collapse_joins_tipe t) gamma in
  (delta, subM, sizeM, gamma')
*)

let rec find_joins_tipe t = 
  match t with
    | Tipe_float -> []
    | Tipe_double -> []
    | Tipe_int sz -> []
    | Tipe_ptr(t, r) -> find_joins_tipe t
    | Tipe_ptrU(sz, r) -> []
    | Tipe_struct ts -> List.fold_left (fun acc t -> find_joins_tipe t @ acc) [] ts
    | Tipe_fun(rs, ts, t) -> 
	(match t with
	   | None -> List.fold_left (fun acc t -> find_joins_tipe t @ acc) [] ts
	   | Some t -> find_joins_tipe t @ (List.fold_left (fun acc t -> find_joins_tipe t @ acc) [] ts)
	)
    | Tipe_array(t, sz) -> find_joins_tipe t
    | Tipe_tvar _ -> []
    | Tipe_join ts -> [Tipe_join ts]
    | Tipe_scheme(rs, t) -> []

let rec collapse_joins_tipe t =
  match t with
    | Tipe_float -> t
    | Tipe_double -> t
    | Tipe_int sz -> t
    | Tipe_ptr(t, r) -> Tipe_ptr(collapse_joins_tipe t, r)
    | Tipe_ptrU(sz, r) -> t
    | Tipe_struct ts -> Tipe_struct(List.map collapse_joins_tipe ts)
    | Tipe_fun(rs, ts, t) -> Tipe_fun(rs, List.map collapse_joins_tipe ts, lift_opt collapse_joins_tipe t)
    | Tipe_array(t, sz) -> Tipe_array(collapse_joins_tipe t, sz)
    | Tipe_tvar tv -> t
    | Tipe_join ts -> collapse_join_one ts
    | Tipe_scheme(rs, t) -> t

let collapse_join delta subM sizeM gamma ts = 
  List.hd ts

let collapse_joins delta subM sizeM gamma = 
  let js = VMap.fold (fun k v acc -> find_joins_tipe v @ acc) gamma []
  in
  (* let (delta', subM', sizeM', gamma', _) = unify_joins delta subM sizeM gamma js in *)
  let (delta', subM', sizeM', gamma') = (delta, subM, sizeM, gamma) in
  let gamma'' = 
    VMap.map (fun t -> collapse_joins_tipe t) gamma'
  in
  (delta', subM', sizeM', gamma'')

let string_of_delta m =
  VMap.fold (fun (fname, k) (sz, t) acc -> fname ^ "." ^ k ^ ": (" ^ string_of_int sz ^ ", " ^ string_of_tipe t ^ ")\n" ^ acc) m ""

let rec free_tvars t = 
  match t with
    | Tipe_float -> []
    | Tipe_double -> []
    | Tipe_int _ -> []
    | Tipe_tvar(tv) -> [tv]
    | Tipe_ptr(t, _) -> free_tvars t
    | Tipe_ptrU _ -> []
    | Tipe_fun(rs, ts, tret) -> 
	(match tret with
	   | Some tret -> free_tvars tret @ (List.fold_left (fun acc t -> free_tvars t @ acc) [] ts)
	   | None -> (List.fold_left (fun acc t -> free_tvars t @ acc) [] ts)
	)
    | Tipe_array(t, sz) -> free_tvars t
    | Tipe_struct(ts) -> List.fold_left (fun acc t -> free_tvars t @ acc) [] ts
    | Tipe_join(ts) -> List.fold_left (fun acc t -> free_tvars t @ acc) [] ts
    | Tipe_scheme(rs, t) -> free_tvars t

let rec find_size sizes tv = 
  match sizes with
    | [] -> None
    | (t, sz)::sizes ->
	match t with
	  | Tipe_tvar tv' -> if tv = tv' then Some sz else find_size sizes tv
	  | _ -> find_size sizes tv

let assign_tipes subM gamma = 
  let tvars = VMap.fold (fun k v acc -> free_tvars v @ acc) gamma [] in
  List.fold_left (fun acc tv -> 
		    if VMap.mem tv subM then
		      acc
		    else
		      (match find_size !sizes tv with
			 | Some sz -> VMap.add tv (Tipe_int(max (sz * 8 - 1) 0)) acc
			 | None -> VMap.add tv (Tipe_int(63)) acc
		      )
		 ) VMap.empty tvars

let apply_subM subM gamma =
  VMap.fold (fun k v acc -> sub_tv_gamma k v acc) subM gamma 

let infer delta gamma cs gcs = 
  log "initial gamma:" ;
  log (string_of_tipeM gamma) ; 
  log "initial delta:" ; 
  log (string_of_tipeM delta) ; 
  log ("") ; 
  log "initial constraints:" ; 
  log (string_of_cs cs) ; 
  log ("") ; 
  log "global constraints:" ; 
  log (string_of_cs gcs) ;
  log ("") ; 
  
  (* unify *)
  let (delta', subM', sizeM', gamma', gcs') = unify [] delta VMap.empty VMap.empty gamma gcs cs in
  
  log ("\n--------------------------------------------------------------") ; 
  log "new global constraints:" ;
  log (string_of_cs gcs') ;
  log ("") ; 

  let phics = List.filter (fun (tag, c) -> tag = "phi") gcs' in
  let callcs = List.filter (fun (tag, c) -> tag = "call") gcs' in
    
  let (delta'', subM'', sizeM'', gamma'', _) = unify [] delta' subM' sizeM' gamma' [] gcs' in

  log "final gamma: " ; 
  log (string_of_tipeM gamma'') ;
  log "tvar sub: " ;
  log (string_of_tipeM subM'') ; 
  log "delta: " ;
  log (string_of_tipeM delta'') ; 
  log "tipe size constraints" ; 
  log (sep_by "\n" (fun (t, sz) -> string_of_tipe t ^ ": " ^ string_of_int sz) !sizes) ; 
  log ("") ; 
  log ("sizes: " ) ; 
  log (string_of_sizeM sizeM'') ; 

  (* return the mapping of program variables to tipes *)
  let subM''' = assign_tipes subM'' gamma'' in
  log ("\nafter assigning tipes") ; 
  log (string_of_tipeM subM''') ; 
  let subM4 = assign_tipes subM'' delta'' in
  (sizeM'', apply_subM subM4 delta'', apply_subM subM''' gamma'')

