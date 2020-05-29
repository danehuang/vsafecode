module Make (Ord_type : Set.OrderedType) = 
  struct
    module S = Set.Make(Ord_type)
    module H = Map.Make(Ord_type)

    type vertex = S.elt
    type graph = S.t H.t ref

    let graph() = ref H.empty

    let clear_graph (g:graph) : unit =
      g := H.empty

    let clear_vertex (g:graph) (v:vertex) : unit = 
      g := H.add v S.empty (!g)

    let add_edge (g:graph) (v1:vertex) (v2:vertex) : unit =
      (try 
	let vs = H.find v1 (!g) in
	  g := H.add v1 (S.add v2 vs) (!g)
      with 
	  Not_found -> 
	    g := H.add v1 (S.singleton v2) (!g)
      ) ; 
      (try 
	 let _ = H.find v2 (!g) in ()
       with Not_found -> g := H.add v2 S.empty (!g)
      ) ;
      ()

    let add_edges (g:graph) (v1:vertex) (vs:S.t) : unit =
      S.fold (fun v2 acc -> add_edge g v1 v2) vs ()
	
    let vertices (g:graph) : S.t  =
      H.fold (fun k v acc -> S.add k acc) (!g) S.empty
      
    let edges (g:graph) (v:vertex) : S.t = 
      try
	H.find v (!g)
      with Not_found -> S.empty

    let copy (g:graph) : graph =
      let copyM = H.fold (fun v vs acc -> H.add v vs acc) (!g) H.empty in
      ref copyM

    let reverse (g:graph) : graph =
      let g' = ref H.empty in
      let _ = H.fold (fun v vs acc -> 
			S.fold (fun v' acc' -> add_edge g' v' v) vs ()
		     ) (!g) () in
	g'
	
    let string_of_v (g:graph) f (vs:S.t) : string = 
      S.fold (fun e acc -> f e ^ ", " ^ acc) vs ""

    let string_of_g (g:graph) f : string =
      H.fold (fun k v acc -> f k ^ ": " ^ string_of_v g f v ^ "\n" ^ acc) (!g) ""

    let transitive_closure (g:graph) : graph = 
      let do1 (g:graph) (vs:S.t) : S.t =
	S.fold (fun v acc -> S.union (edges g v) acc) vs S.empty
      in
      let update (g:graph) (v:vertex) (vs: S.t) : bool =
	let curr_vs = edges g v in
	let grow_vs = S.union vs curr_vs in
	add_edges g v vs ; 
	not (S.equal grow_vs curr_vs)
      in
      let rec transitive_closure' (g:graph) : graph = 
	let cont = H.fold (fun v vs acc -> update g v (do1 g vs) || acc) (!g) false in
	if cont then transitive_closure' g else g
      in
      let g' = copy g in
      transitive_closure' g'
	
    let remove_self (g:graph) : graph =
      H.fold (fun v vs acc -> g := H.add v (S.remove v vs) !g) !g () ;
      g
	
end

module G = Make(struct type t = string let compare = compare end)

