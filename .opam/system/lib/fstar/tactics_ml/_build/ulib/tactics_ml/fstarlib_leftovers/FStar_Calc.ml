open Prims
type ('At,'dummyV0,'dummyV1,'dummyV2) calc_proof =
  | CalcRefl of 'At 
  | CalcStep of unit Prims.list * unit * 'At * 'At * 'At *
  ('At,unit,unit,unit) calc_proof * unit 
let uu___is_CalcRefl :
  'At .
    unit Prims.list ->
      'At -> 'At -> ('At,unit,unit,unit) calc_proof -> Prims.bool
  =
  fun uu____139  ->
    fun uu____140  ->
      fun uu____141  ->
        fun projectee  ->
          match projectee with | CalcRefl x -> true | uu____157 -> false
  
let __proj__CalcRefl__item__x :
  'At .
    unit Prims.list -> 'At -> 'At -> ('At,unit,unit,unit) calc_proof -> 'At
  =
  fun uu____215  ->
    fun uu____216  ->
      fun uu____217  ->
        fun projectee  -> match projectee with | CalcRefl x -> x
  
let uu___is_CalcStep :
  'At .
    unit Prims.list ->
      'At -> 'At -> ('At,unit,unit,unit) calc_proof -> Prims.bool
  =
  fun uu____286  ->
    fun uu____287  ->
      fun uu____288  ->
        fun projectee  ->
          match projectee with
          | CalcStep (rs,p,x,y,z,_5,_6) -> true
          | uu____322 -> false
  
let __proj__CalcStep__item__rs :
  'At .
    unit Prims.list ->
      'At -> 'At -> ('At,unit,unit,unit) calc_proof -> unit Prims.list
  =
  fun uu____388  ->
    fun uu____389  ->
      fun uu____390  ->
        fun projectee  ->
          match projectee with | CalcStep (rs,p,x,y,z,_5,_6) -> rs
  
type ('At,'Auu____455,'Auu____456,'Auu____457,'Aprojectee,'Auu____459,
  'Auu____460) __proj__CalcStep__item__p = Obj.t
let __proj__CalcStep__item__x :
  'At .
    unit Prims.list -> 'At -> 'At -> ('At,unit,unit,unit) calc_proof -> 'At
  =
  fun uu____519  ->
    fun uu____520  ->
      fun uu____521  ->
        fun projectee  ->
          match projectee with | CalcStep (rs,p,x,y,z,_5,_6) -> x
  
let __proj__CalcStep__item__y :
  'At .
    unit Prims.list -> 'At -> 'At -> ('At,unit,unit,unit) calc_proof -> 'At
  =
  fun uu____606  ->
    fun uu____607  ->
      fun uu____608  ->
        fun projectee  ->
          match projectee with | CalcStep (rs,p,x,y,z,_5,_6) -> y
  
let __proj__CalcStep__item__z :
  'At .
    unit Prims.list -> 'At -> 'At -> ('At,unit,unit,unit) calc_proof -> 'At
  =
  fun uu____693  ->
    fun uu____694  ->
      fun uu____695  ->
        fun projectee  ->
          match projectee with | CalcStep (rs,p,x,y,z,_5,_6) -> z
  
let __proj__CalcStep__item___5 :
  'At .
    unit Prims.list ->
      'At ->
        'At ->
          ('At,unit,unit,unit) calc_proof -> ('At,unit,unit,unit) calc_proof
  =
  fun uu____790  ->
    fun uu____791  ->
      fun uu____792  ->
        fun projectee  ->
          match projectee with | CalcStep (rs,p,x,y,z,_5,_6) -> _5
  

type ('At,'Ax,'Ay) calc_pack =
  {
  rels: unit Prims.list ;
  proof: ('At,unit,unit,unit) calc_proof }
let __proj__Mkcalc_pack__item__rels :
  'At . 'At -> 'At -> ('At,unit,unit) calc_pack -> unit Prims.list =
  fun x  ->
    fun y  ->
      fun projectee  -> match projectee with | { rels; proof;_} -> rels
  
let __proj__Mkcalc_pack__item__proof :
  'At .
    'At ->
      'At -> ('At,unit,unit) calc_pack -> ('At,unit,unit,unit) calc_proof
  =
  fun x  ->
    fun y  ->
      fun projectee  -> match projectee with | { rels; proof;_} -> proof
  
let pk_rels :
  'At . 'At -> 'At -> ('At,unit,unit) calc_pack -> unit Prims.list =
  fun x  -> fun y  -> fun pk  -> pk.rels 
type ('At,'Ars,'Ax,'Ay) calc_chain_related = Obj.t
type ('At,'Ars,'Ap) calc_chain_compatible = unit

let _calc_init : 'At . 'At -> ('At,unit,unit,unit) calc_proof =
  fun x  -> CalcRefl x 
let calc_init : 'At . 'At -> ('At,unit,unit) calc_pack =
  fun x  -> { rels = []; proof = (_calc_init x) } 


