open Utility
open SCast

(* debugging functions *)
let debug = ref true
let log str =
  if (!debug) then print_endline str else ()

(* -------------------------------------------------------------------------- *)
(* This module will serve to lower anything in Ocaml land down to the types
 * required by the extract Coq type-checker, if any exist. *)

type funcpkg = { func : function0 ;
		 delta1 : typ Tc.Nenv.t ;
		 delta2 : typ Tc.Nenv.t ;
		 psi : ((ftyp list) Tc.Nenv.t) Tc.Ienv.t
	       }

let lower_precond (lo:Tc.layout) (tenv:Tc.tenv_t) (gamma:typ SMap.t) : (ftyp list) Tc.Nenv.t = 
  SMap.fold (fun k v acc -> Tc.Nenv.add k (Tc.flatten_typ lo tenv v) acc) gamma Tc.Nenv.empty

let lower_preconds (lo:Tc.layout) structM (tenv:Tc.tenv_t) (globsM:typ SMap.t) (f:function0) : ((ftyp list) Tc.Nenv.t) Tc.Ienv.t = 
  let preconds = Precond.precond_func globsM structM f in
  List.fold_left ( fun acc (l, gamma) ->
		     let gamma' = lower_precond lo tenv gamma in
		     Tc.Ienv.add l gamma' acc
		 ) Tc.Ienv.empty preconds

let lower_delta init (rts:(rgn * typ) list) : typ Tc.Nenv.t =
  List.fold_left (fun acc (r,t) -> Tc.Nenv.add r t acc) init rts

let fix_entry_name_phi name orig p =
  match p with
    | Insn_phi(x, t, arms) ->
	let arms' = List.map (fun (o, l) -> if orig = l then (o, name) else (o, l)) arms in
	Insn_phi(x, t, arms')

let fix_entry_name_phis name orig bs =
  List.map (fun b -> 
	      let phis' = List.map (fix_entry_name_phi name orig) b.b_phis in
	      { b_lab = b.b_lab ;
		b_phis = phis' ;
		b_insns = b.b_insns ;
		b_nd_term = b.b_nd_term ;
	      }) bs

let fix_entry_name (name:string) (bs:block list) : block list =
  match bs with
    | [] -> []
    | b::t -> 
	let b' = { b_lab = name ;
		   b_phis = b.b_phis ; 
		   b_insns = b.b_insns ;
		   b_nd_term = b.b_nd_term
		 }
	in
	  fix_entry_name_phis name (b.b_lab) (b'::t)

let lower_tenv (lo:Tc.layout) (tenv:(typ list * rgn list) SMap.t) : Tc.tenv_t = 
  SMap.fold 
    (fun k v acc ->
       let (ts, rs) = 
	 try SMap.find k tenv
	 with Not_found -> failwith "Lower: named type not found in environment"
       in
       let ts' = List.fold_left (fun acc t -> acc @ Tc.flatten_typ lo Tc.Nenv.empty t) [] ts in
       Tc.Nenv.add k ((ts', rs), false) acc
    ) tenv Tc.Nenv.empty
    
let lower_func (lo:Tc.layout) structM (gprgns:(rgn * typ) list) (globsM:typ SMap.t) (f:function0) : funcpkg =
  (* Thread through globals. *)
  let (gparams', sig') = List.split (SMap.fold (fun k v acc -> (k, v) :: acc) globsM []) in
  let tenv = lower_tenv lo structM in
  let f' = 
    { f_lab = f.f_lab ; 
      f_params = f.f_params @ gparams' ; 
      f_sig = f.f_sig @ sig' ;
      f_body = fix_entry_name f.f_lab f.f_body ; 
      f_ret = f.f_ret ; 
      f_prgn = f.f_prgn @ gprgns ;
      f_lrgn = f.f_lrgn
    } 
  in
  let delta1 = lower_delta Tc.Nenv.empty f'.f_prgn in
  let delta2 = lower_delta delta1 f'.f_lrgn in
    { func = f' ;
      delta1 = delta1 ;
      delta2 = delta2 ;
      psi = lower_preconds lo structM tenv globsM f' 
    }

let lo =
  { Tc.endian = false; 
    Tc.lo_float_half_info = 4; 
    Tc.lo_float_float_info = 4;
    Tc.lo_float_double_info = 8;
    Tc.lo_float_fp128_info = 8;
    Tc.lo_ptr_info = 8; 
    Tc.lo_fun_info = 8 }

(* -------------------------------------------------------------------------- *)
(* Random pretty printing *)

let string_of_gamma (gamma:(ftyp list) Tc.Nenv.t) : string = 
  "{"^
  Tc.Nenv.fold
    ( fun k v acc ->
	"(" ^ k ^ ", " ^ Pprint.string_of_ftyps v ^ ") " ^ acc
    ) gamma "" ^ "}"

let string_of_psi (psi:((ftyp list) Tc.Nenv.t) Tc.Ienv.t) : string =
  Tc.Ienv.fold 
    ( fun k v acc ->
	acc ^ k ^ ": " ^ string_of_gamma v ^ "\n"
    ) psi ""
