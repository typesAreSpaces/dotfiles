open Prims



let bool_of_or : 'Ap 'Aq . ('Ap,'Aq) Prims.c_or -> Prims.bool =
  fun t  ->
    match t with
    | Prims.Left uu____60 -> true
    | Prims.Right uu____62 -> false
  



type 'Ap pow = unit
type ('a,'b) retract =
  | MkR of unit * unit * unit 
let uu___is_MkR : 'a 'b . ('a,'b) retract -> Prims.bool =
  fun projectee  -> true 



type ('a,'b) retract_cond =
  | MkC of unit * unit * unit 
let uu___is_MkC : 'a 'b . ('a,'b) retract_cond -> Prims.bool =
  fun projectee  -> true 




let false_elim : 'Aa . Prims.l_False -> 'Aa =
  fun a1  -> (fun f  -> Obj.magic (failwith "unreachable")) a1 

type u = unit