open Prims
type ('Aa,'Ab,'Af,'Ag) inverses = unit
type ('Aa,'Ab) view =
  | View of Prims.pos * unit * unit 
let uu___is_View : 'Aa 'Ab . ('Aa,'Ab) view -> Prims.bool =
  fun projectee  -> true 
let __proj__View__item__n : 'Aa 'Ab . ('Aa,'Ab) view -> Prims.pos =
  fun projectee  -> match projectee with | View (n1,get1,put) -> n1 


type ('Aa,'Arrel,'Arel,'Ab) buffer_view =
  | BufferView of ('Aa,'Arrel,'Arel) LowStar_Monotonic_Buffer.mbuffer *
  ('Aa,'Ab) view 
let uu___is_BufferView :
  'Aa 'Arrel 'Arel 'Ab . ('Aa,'Arrel,'Arel,'Ab) buffer_view -> Prims.bool =
  fun projectee  -> true 
let __proj__BufferView__item__buf :
  'Aa 'Arrel 'Arel 'Ab .
    ('Aa,'Arrel,'Arel,'Ab) buffer_view ->
      ('Aa,'Arrel,'Arel) LowStar_Monotonic_Buffer.mbuffer
  = fun projectee  -> match projectee with | BufferView (buf1,v1) -> buf1 
let __proj__BufferView__item__v :
  'Aa 'Arrel 'Arel 'Ab . ('Aa,'Arrel,'Arel,'Ab) buffer_view -> ('Aa,'Ab) view
  = fun projectee  -> match projectee with | BufferView (buf1,v1) -> v1 
type 'Adest buffer =
  (unit,unit,unit,(Obj.t,Obj.t,Obj.t,'Adest) buffer_view)
    FStar_Pervasives.dtuple4
type ('Adest,'Ab) as_buffer_t =
  (unit,unit,unit) LowStar_Monotonic_Buffer.mbuffer

let as_buffer : 'Ab . 'Ab buffer -> ('Ab,unit) as_buffer_t =
  fun a1  ->
    (fun v1  ->
       Obj.magic
         (__proj__BufferView__item__buf
            (FStar_Pervasives.__proj__Mkdtuple4__item___4 v1))) a1
  

let get_view : 'Ab . 'Ab buffer -> (unit,'Ab) view =
  fun a2  ->
    (fun v1  ->
       Obj.magic
         (__proj__BufferView__item__v
            (FStar_Pervasives.__proj__Mkdtuple4__item___4 v1))) a2
  

type ('Ab,'Ah,'Avb) live =
  (unit,unit,unit,unit,unit) LowStar_Monotonic_Buffer.live











type ('Ab,'Avb,'Ah,'Ah') modifies =
  (unit,unit,unit) LowStar_Monotonic_Buffer.modifies






