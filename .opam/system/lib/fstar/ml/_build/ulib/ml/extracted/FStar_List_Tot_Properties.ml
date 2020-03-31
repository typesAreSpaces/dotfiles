open Prims
type ('Aa,'An) llist = 'Aa Prims.list
























let rec rev' : 'a . 'a Prims.list -> 'a Prims.list =
  fun uu___1_187  ->
    match uu___1_187 with
    | [] -> []
    | hd1::tl1 -> FStar_List_Tot_Base.op_At (rev' tl1) [hd1]
  
let rev'T :
  'Auu____200 . unit -> 'Auu____200 Prims.list -> 'Auu____200 Prims.list =
  fun uu____208  -> rev' 

























let rec sorted : 'a . ('a -> 'a -> Prims.bool) -> 'a Prims.list -> Prims.bool
  =
  fun f  ->
    fun uu___4_440  ->
      match uu___4_440 with
      | [] -> true
      | uu____449::[] -> true
      | x::y::tl1 -> (f x y) && (sorted f (y :: tl1))
  
type ('Aa,'Af) total_order = unit













































