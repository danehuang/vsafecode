module String_as_OT =
  struct
    type t = string
	
    (** val compare : nat -> nat -> nat compare0 **)
	
    let compare (x:t) (y:t) : t compare0 =
      let i = compare x y in
	if i = 0 then EQ
	else if i < 0 then LT
	else GT
	  
    (** val eq_dec : string -> string -> bool **)
	  
    let eq_dec = (fun x y -> if x = y then true else false)
  end
