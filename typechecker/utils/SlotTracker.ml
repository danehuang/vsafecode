(* Emulate the LLVM slot tracker class ... *)

open Llvm 

module SlotMap = Map.Make(struct type t = llvalue let compare = compare end)

type slottracker_internal = { localSlotMap : (int SlotMap.t) ;
			      globalSlotMap : (int SlotMap.t) ;
			      localSlotCtr : int ;
			      globalSlotCtr : int
			    }

type slottracker = slottracker_internal ref

let slotTracker() : slottracker =
  ref { localSlotMap = SlotMap.empty ;
	globalSlotMap = SlotMap.empty ;
	localSlotCtr = 0 ;
	globalSlotCtr = 0
      }

let getGlobalSlot (st:slottracker) (v:llvalue) : string =
  if value_name v = "" then
    try 
      string_of_int (SlotMap.find v (!st.globalSlotMap))
    with 
	Not_found ->
	  let tmp = !st.globalSlotCtr in
	  st := 
	    { localSlotMap = !st.localSlotMap ;
	      globalSlotMap = SlotMap.add v tmp !st.globalSlotMap ;
	      localSlotCtr = !st.localSlotCtr ;
	      globalSlotCtr = tmp + 1
	    } ;
	  string_of_int tmp 
  else value_name v

let getLocalSlot (st:slottracker) (v:llvalue) : string =
  if value_name v = "" then
    try 
      string_of_int (SlotMap.find v (!st.localSlotMap))
    with 
	Not_found ->
	  let tmp = !st.localSlotCtr in
	  st := 
	    { localSlotMap = SlotMap.add v tmp !st.localSlotMap ;
	      globalSlotMap = !st.globalSlotMap ;
	      localSlotCtr = tmp + 1 ;
	      globalSlotCtr = !st.globalSlotCtr
	    } ;
	  string_of_int tmp 
  else value_name v

let reset (st:slottracker) : unit =
  st := { localSlotMap = SlotMap.empty ;
	  globalSlotMap = SlotMap.empty ;
	  localSlotCtr = 0 ;
	  globalSlotCtr = 0
	}
