open Prims
type 'Aa regional =
  | Rgl of unit * unit * 'Aa * unit * unit * unit * unit * unit * unit * unit
  * (unit -> 'Aa) * ('Aa -> unit) 
let uu___is_Rgl : 'Aa . 'Aa regional -> Prims.bool = fun projectee  -> true 


let __proj__Rgl__item__dummy : 'Aa . 'Aa regional -> 'Aa =
  fun projectee  ->
    match projectee with
    | Rgl
        (region_of,loc_of,dummy,r_inv,r_inv_reg,repr,r_repr,r_sep,irepr,r_alloc_p,r_alloc,r_free)
        -> dummy
  
type ('Aa,'Aprojectee,'Auu____551,'Auu____552) __proj__Rgl__item__r_inv =
  Obj.t

type ('Aa,'Aprojectee) __proj__Rgl__item__repr = Obj.t



type ('Aa,'Aprojectee,'Auu____809) __proj__Rgl__item__r_alloc_p = Obj.t
let __proj__Rgl__item__r_alloc : 'Aa . 'Aa regional -> unit -> 'Aa =
  fun projectee  ->
    match projectee with
    | Rgl
        (region_of,loc_of,dummy,r_inv,r_inv_reg,repr,r_repr,r_sep,irepr,r_alloc_p,r_alloc,r_free)
        -> r_alloc
  
let __proj__Rgl__item__r_free : 'Aa . 'Aa regional -> 'Aa -> unit =
  fun projectee  ->
    match projectee with
    | Rgl
        (region_of,loc_of,dummy,r_inv,r_inv_reg,repr,r_repr,r_sep,irepr,r_alloc_p,r_alloc,r_free)
        -> r_free
  