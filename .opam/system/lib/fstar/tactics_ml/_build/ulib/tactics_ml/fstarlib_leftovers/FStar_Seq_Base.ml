open Prims
type 'Aa seq =
  | MkSeq of 'Aa Prims.list 
let uu___is_MkSeq : 'Aa . 'Aa seq -> Prims.bool = fun projectee  -> true 
let __proj__MkSeq__item__l : 'Aa . 'Aa seq -> 'Aa Prims.list =
  fun projectee  -> match projectee with | MkSeq l -> l 
let length : 'Aa . 'Aa seq -> Prims.nat =
  fun s  -> FStar_List_Tot_Base.length (__proj__MkSeq__item__l s) 
let index : 'Aa . 'Aa seq -> Prims.nat -> 'Aa =
  fun s  -> fun i  -> FStar_List_Tot_Base.index (__proj__MkSeq__item__l s) i 
let cons : 'Aa . 'Aa -> 'Aa seq -> 'Aa seq =
  fun x  -> fun s  -> MkSeq (x :: (__proj__MkSeq__item__l s)) 
let hd : 'Aa . 'Aa seq -> 'Aa =
  fun s  -> FStar_List_Tot_Base.hd (__proj__MkSeq__item__l s) 
let tl : 'Aa . 'Aa seq -> 'Aa seq =
  fun s  -> MkSeq (FStar_List_Tot_Base.tl (__proj__MkSeq__item__l s)) 
let rec create : 'Aa . Prims.nat -> 'Aa -> 'Aa seq =
  fun len  ->
    fun v  ->
      if len = Prims.int_zero
      then MkSeq []
      else cons v (create (len - Prims.int_one) v)
  
let rec init_aux :
  'Aa . Prims.nat -> Prims.nat -> (Prims.nat -> 'Aa) -> 'Aa seq =
  fun len  ->
    fun k  ->
      fun contents  ->
        if (k + Prims.int_one) = len
        then MkSeq [contents k]
        else cons (contents k) (init_aux len (k + Prims.int_one) contents)
  
let init : 'Aa . Prims.nat -> (Prims.nat -> 'Aa) -> 'Aa seq =
  fun len  ->
    fun contents  ->
      if len = Prims.int_zero
      then MkSeq []
      else init_aux len Prims.int_zero contents
  
let empty : 'Aa . unit -> 'Aa seq = fun uu____276  -> MkSeq [] 
let createEmpty : 'Aa . unit -> 'Aa seq = fun uu____284  -> empty () 

let rec upd : 'Aa . 'Aa seq -> Prims.nat -> 'Aa -> 'Aa seq =
  fun s  ->
    fun n  ->
      fun v  ->
        if n = Prims.int_zero
        then cons v (tl s)
        else cons (hd s) (upd (tl s) (n - Prims.int_one) v)
  
let append : 'Aa . 'Aa seq -> 'Aa seq -> 'Aa seq =
  fun s1  ->
    fun s2  ->
      MkSeq
        (FStar_List_Tot_Base.append (__proj__MkSeq__item__l s1)
           (__proj__MkSeq__item__l s2))
  
let op_At_Bar : 'Aa . 'Aa seq -> 'Aa seq -> 'Aa seq =
  fun s1  -> fun s2  -> append s1 s2 
let rec slice : 'Aa . 'Aa seq -> Prims.nat -> Prims.nat -> 'Aa seq =
  fun s  ->
    fun i  ->
      fun j  ->
        if i > Prims.int_zero
        then slice (tl s) (i - Prims.int_one) (j - Prims.int_one)
        else
          if j = Prims.int_zero
          then MkSeq []
          else cons (hd s) (slice (tl s) i (j - Prims.int_one))
  













type ('Aa,'As1,'As2) equal = unit
let rec eq_i : 'Aa . 'Aa seq -> 'Aa seq -> Prims.nat -> Prims.bool =
  fun s1  ->
    fun s2  ->
      fun i  ->
        if i = (length s1)
        then true
        else
          if (index s1 i) = (index s2 i)
          then eq_i s1 s2 (i + Prims.int_one)
          else false
  
let eq : 'Aa . 'Aa seq -> 'Aa seq -> Prims.bool =
  fun s1  ->
    fun s2  ->
      if (length s1) = (length s2) then eq_i s1 s2 Prims.int_zero else false
  









