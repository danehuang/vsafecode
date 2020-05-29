open Utility
open SCast

(* debugging functions *)
let debug = ref false
let log str =
  if (!debug) then print_endline str else ()

(*----------------------------------------------------------------------------*)

let cfa_nd (nd:insn_nd) : lab list =
  match nd with
    | Insn_call(_, _, _, _, _, l) -> [l]
    | Insn_malloc(_, _, _, _, l) -> [l]
    | Insn_unsafe_call(_, _, _, l) -> [l]

let cfa_tm (tm:terminator) : lab list =
  match tm with
    | Insn_return _ -> []
    | Insn_return_void -> []
    | Insn_br_uncond(l) -> [l]
    | Insn_br(_, l1, l2) -> [l1 ; l2]
    | Insn_switch(_, _, l, arms) -> l :: (List.map (fun (_, l) -> l) arms)
    | Insn_indirect_br(_, _, ls) -> ls
    | Insn_unreachable -> []

let cfa_ndtm (ndtm:insn_nd_term) : lab list =
  match ndtm with
    | Insn_nd(nd) -> cfa_nd nd
    | Insn_term(tm) -> cfa_tm tm

let cfa_blk_map (succM : (lab list) SMap.t) (b:block) : (lab list) SMap.t =
  SMap.add b.b_lab (cfa_ndtm b.b_nd_term) succM

let cfa_blks_map (bs:block list) : (lab list) SMap.t =
  List.fold_left (fun acc b -> cfa_blk_map acc b) SMap.empty bs

let cfa_blks (bs:block list) : G.graph = 
  let g = G.graph() in
  let succM : (lab list) SMap.t ref = ref (cfa_blks_map bs) in
  SMap.fold (fun k v acc -> 
	       let succs = List.fold_left (fun acc l -> G.S.add l acc) G.S.empty v in
	       G.add_edges g k succs 
	    ) !succM () ; 
  g


(*----------------------------------------------------------------------------*)
(* Dominator tree analysis. 
 *
 * // dominator of the start node is the start itself
 * Dom(n0) = {n0}
 * // for all other nodes, set all nodes as the dominators
 * for each n in N - {n0}
 *   Dom(n) = N;
 *   // iteratively eliminate nodes that are not dominators
 *   while changes in any Dom(n)
 *     for each n in N - {n0}:
 *        Dom(n) = {n} union with intersection over Dom(p) for all p in pred(n)
 *)

let dominator (f:function0) : G.graph = 
  let cfg = cfa_blks f.f_body in 
  log (Pprint.string_of_blks f.f_body) ; 
  log ("CFA: ") ;
  log (G.string_of_g cfg (fun x -> x)) ; 
  let cfg_rev = G.reverse cfg in
  let vs = G.vertices cfg in
  let e_blk = try List.hd f.f_body with _ -> failwith ("Dominator: no entry block in " ^ f.f_lab) in
  let e_lab = e_blk.b_lab in
  let domG = G.graph() in
  let _ = G.add_edge domG e_lab e_lab in
  let vs' = G.S.remove e_lab vs in
  G.S.iter (fun l -> if not (l = e_lab) then G.add_edges domG l vs) vs' ;   

  let update v =
    let preds = G.edges cfg_rev v in
    let curr_dom = G.edges domG v in
    let new_dom = G.S.add v (G.S.fold (fun v acc -> G.S.inter (G.edges domG v) acc) preds vs) in 
    G.clear_vertex domG v ; 
    G.add_edges domG v new_dom ;
    not (G.S.equal curr_dom new_dom)
  in
  let rec go() =
    let cont = G.S.fold (fun v acc -> update v || acc) vs' false in
    if cont then go() else ()	
  in
    go() ;
    let domG = G.remove_self domG in
    domG

(*----------------------------------------------------------------------------*)

(* Reachability analysis. Computes for each label, the set of labels whose
 * definitions can flow to it. *)
let reachable (f:function0) : G.graph =
  let g = cfa_blks f.f_body in
  log ("CFA: ") ;
  log (G.string_of_g g (fun x -> x)) ; 
  log ("REV: ") ;
  log (G.string_of_g (G.reverse g) (fun x -> x)) ; 
  G.transitive_closure (G.reverse g)
