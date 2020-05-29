open Graph

let dominator (cfg:G.graph) : G.graph = 
  let cfg_rev = G.reverse cfg in
  let vs = G.vertices cfg in
  let e_lab = "entry" in
  let domG = G.graph() in
  let _ = G.add_edge domG e_lab e_lab in
  let vs' = G.S.remove e_lab vs in
  G.S.iter (fun l -> if not (l = e_lab) then G.add_edges domG l vs) vs' ; 
  print_endline (G.string_of_g domG (fun x -> x)) ; 
(*
  // dominator of the start node is the start itself
  Dom(n0) = {n0}
  // for all other nodes, set all nodes as the dominators
  for each n in N - {n0}
    Dom(n) = N;
  // iteratively eliminate nodes that are not dominators
  while changes in any Dom(n)
    for each n in N - {n0}:
      Dom(n) = {n} union with intersection over Dom(p) for all p in pred(n)
*)

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

let g = G.graph()
let _ = 
  G.add_edge g "entry" "if.then" ;
  G.add_edge g "if.then" "if.end" ; 
  G.add_edge g "entry" "if.end" ; 
  G.add_edge g "if.end" "while.cond" ; 
  G.add_edge g "while.cond" "while.body" ; 
  G.add_edge g "while.body" "if.then11" ; 
  G.add_edge g "if.then11" "if.then13" ;
  G.add_edge g "if.then13" "while.cond" ; 
  G.add_edge g "if.then11" "if.else" ; 
  G.add_edge g "if.else" "while.cond" ; 
  G.add_edge g "while.body" "if.else19" ; 
  G.add_edge g "if.else19" "if.then21" ;
  G.add_edge g "if.then21" "while.cond" ; 
  G.add_edge g "if.else19" "if.else24" ; 
  G.add_edge g "if.else24" "while.cond" ; 
  G.add_edge g "while.cond" "while.end" ; 
  G.add_edge g "while.end" "if.then32" ; 
  G.add_edge g "if.then32" "if.end38" ; 
  G.add_edge g "while.end" "if.end38" ; 
  print_endline ("CFG:\n" ^ G.string_of_g g (fun x -> x)) ;
  let dom = dominator g in
  print_endline ("DOM:\n" ^ G.string_of_g dom (fun x -> x))
    
