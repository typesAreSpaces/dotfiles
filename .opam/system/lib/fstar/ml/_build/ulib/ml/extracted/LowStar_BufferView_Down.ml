open Prims
type ('Aa,'Ab,'Af,'Ag) inverses = unit
type ('Aa,'Ab) view =
  | View of Prims.pos * unit * unit 
let uu___is_View : 'Aa 'Ab . ('Aa,'Ab) view -> Prims.bool =
  fun projectee  -> true 
let __proj__View__item__n : 'Aa 'Ab . ('Aa,'Ab) view -> Prims.pos =
  fun projectee  -> match projectee with | View (n1,get1,put) -> n1 


type ('Asrc,'Arrel,'Arel,'Adest) buffer_view =
  | BufferView of ('Asrc,'Arrel,'Arel) LowStar_Monotonic_Buffer.mbuffer *
  ('Asrc,'Adest) view 
let uu___is_BufferView :
  'Asrc 'Arrel 'Arel 'Adest .
    ('Asrc,'Arrel,'Arel,'Adest) buffer_view -> Prims.bool
  = fun projectee  -> true 
let __proj__BufferView__item__buf :
  'Asrc 'Arrel 'Arel 'Adest .
    ('Asrc,'Arrel,'Arel,'Adest) buffer_view ->
      ('Asrc,'Arrel,'Arel) LowStar_Monotonic_Buffer.mbuffer
  = fun projectee  -> match projectee with | BufferView (buf1,v1) -> buf1 
let __proj__BufferView__item__v :
  'Asrc 'Arrel 'Arel 'Adest .
    ('Asrc,'Arrel,'Arel,'Adest) buffer_view -> ('Asrc,'Adest) view
  = fun projectee  -> match projectee with | BufferView (buf1,v1) -> v1 
type 'Adest buffer =
  (unit,unit,unit,(Obj.t,Obj.t,Obj.t,'Adest) buffer_view)
    FStar_Pervasives.dtuple4
type ('Adest,'Ab) as_buffer_t =
  (unit,unit,unit) LowStar_Monotonic_Buffer.mbuffer

let as_buffer : 'Ab . 'Ab buffer -> ('Ab,unit) as_buffer_t =
  fun a1  ->
    (fun v1  ->
       let uu____1060 = v1  in
       match uu____1060 with
       | FStar_Pervasives.Mkdtuple4
           (uu____1063,uu____1064,uu____1065,BufferView (b,uu____1067)) ->
           Obj.magic b) a1
  

let get_view : 'Ab . 'Ab buffer -> (unit,'Ab) view =
  fun a2  ->
    (fun bv  ->
       let uu____1210 = bv  in
       match uu____1210 with
       | FStar_Pervasives.Mkdtuple4
           (uu____1213,uu____1214,uu____1215,BufferView (uu____1216,v1)) ->
           Obj.magic v1) a2
  

type ('Ab,'Ah,'Avb) live =
  (unit,unit,unit,unit,unit) LowStar_Monotonic_Buffer.live







type ('Ab,'Avb,'Ah,'Ah') mods =
  (unit,unit,unit) LowStar_Monotonic_Buffer.modifies




type ('Ab,'Avb,'Ah,'Ah') modifies =
  (unit,unit,unit) LowStar_Monotonic_Buffer.modifies


















