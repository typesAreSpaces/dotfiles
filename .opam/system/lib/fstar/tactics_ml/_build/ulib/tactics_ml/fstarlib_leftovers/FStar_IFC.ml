open Prims
type ('Aa,'Af) associative = unit
type ('Aa,'Af) commutative = unit
type ('Aa,'Af) idempotent = unit
type semi_lattice =
  | SemiLattice of unit * Obj.t * (Obj.t -> Obj.t -> Obj.t) 
let (uu___is_SemiLattice : semi_lattice -> Prims.bool) =
  fun projectee  -> true 
type 'Aprojectee __proj__SemiLattice__item__carrier = Obj.t
let (__proj__SemiLattice__item__top : semi_lattice -> Obj.t) =
  fun projectee  ->
    match projectee with | SemiLattice (carrier,top,lub) -> top
  
let (__proj__SemiLattice__item__lub :
  semi_lattice -> Obj.t -> Obj.t -> Obj.t) =
  fun projectee  ->
    match projectee with | SemiLattice (carrier,top,lub) -> lub
  
type sl = unit
type 'Asl lattice_element = unit

type ('Asl,'Al,'Ab) protected = 'Ab

let (hide : unit -> unit -> unit -> Obj.t -> Obj.t) =
  fun sl  -> fun l  -> fun b  -> fun x  -> x 


let (return : unit -> unit -> unit -> Obj.t -> Obj.t) =
  fun sl  -> fun a  -> fun l  -> fun x  -> hide () () () x 
let map :
  'Aa 'Ab .
    unit ->
      unit ->
        (unit,unit,'Aa) protected ->
          ('Aa -> 'Ab) -> (unit,unit,'Ab) protected
  = fun sl  -> fun l  -> fun x  -> fun f  -> f x 
let (join : unit -> unit -> unit -> unit -> Obj.t -> Obj.t) =
  fun sl  -> fun l1  -> fun l2  -> fun a  -> fun x  -> let y = x  in y 
let (bind :
  unit -> unit -> unit -> Obj.t -> unit -> unit -> (Obj.t -> Obj.t) -> Obj.t)
  =
  fun sl  ->
    fun l1  ->
      fun a  ->
        fun x  ->
          fun l2  -> fun b  -> fun f  -> join () () () () (map () () x f)
  