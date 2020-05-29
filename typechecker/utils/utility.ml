open Llvm

(* Contains random utility functions and functor instantiations *)

(* String utility functions *)
let contains s1 s2 =
  try
    let len = String.length s2 in
    for i = 0 to String.length s1 - len do
      if String.sub s1 i len = s2 then raise Exit
    done;
    false
  with Exit -> true

(* Sum types *)
type ('a,'b) sum = Inl of 'a | Inr of 'b

(* Sum utility functions *) 
let filter_left ls =
  List.map (fun x -> match x with Inl x -> x | Inr _ -> failwith "filter_left found right injection")
    (List.filter (fun x -> match x with Inl _ -> true | Inr _ -> false) ls)

let filter_right ls =
  List.map (fun x -> match x with Inl x -> failwith "filter_right found left injection" | Inr x -> x)
    (List.filter (fun x -> match x with Inl _ -> false | Inr _ -> true) ls)

(* String map *)
module SMap = Map.Make(struct type t = string let compare = compare end)

(* Imperative graph *)
module G = Graph.Make(struct type t = string let compare = compare end)

(* String set *)
module S = Set.Make(struct type t = string let compare = compare end)

(* lltype map *)
module TMap = Map.Make(struct type t = lltype let compare = compare end)

(* Create n element list of e *)
let rec list_repeat n e =
  if n = 0 then [] else e :: list_repeat (n - 1) e

(* Counters *)

type counter = int ref

let counter() : counter = ref 0
let fresh (ctr:counter) : int = 
  let tmp = !ctr in
  ctr := !ctr + 1 ;
  tmp 

let lift_opt f o = 
  match o with
    | Some x -> Some (f x)
    | None -> None

let opt2bool o =
  match o with
    | Some _ -> true
    | None -> false
