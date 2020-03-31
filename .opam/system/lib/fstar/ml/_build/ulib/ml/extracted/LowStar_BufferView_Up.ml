open Prims
type ('Auu____21,'Auu____22,'Af,'Ag) inverses = unit
type ('Aa,'Ab) view =
  | View of Prims.pos * unit * unit 
let uu___is_View : 'Aa 'Ab . ('Aa,'Ab) view -> Prims.bool =
  fun projectee  -> true 
let __proj__View__item__n : 'Aa 'Ab . ('Aa,'Ab) view -> Prims.pos =
  fun projectee  -> match projectee with | View (n1,get1,put) -> n1 


type 'Adest buffer =
  | Buffer of unit * Obj.t LowStar_BufferView_Down.buffer * (Obj.t,'Adest)
  view 
let uu___is_Buffer : 'Adest . 'Adest buffer -> Prims.bool =
  fun projectee  -> true 
type ('Adest,'Aprojectee) __proj__Buffer__item__src = Obj.t
let __proj__Buffer__item__down_buf :
  'Adest . 'Adest buffer -> Obj.t LowStar_BufferView_Down.buffer =
  fun projectee  ->
    match projectee with | Buffer (src,down_buf,v1) -> down_buf
  
let __proj__Buffer__item__v : 'Adest . 'Adest buffer -> (Obj.t,'Adest) view =
  fun projectee  -> match projectee with | Buffer (src,down_buf,v1) -> v1 

type ('Ab,'Abv) buffer_src = Obj.t
let as_down_buffer : 'Ab . 'Ab buffer -> Obj.t LowStar_BufferView_Down.buffer
  = fun bv  -> __proj__Buffer__item__down_buf bv 
let get_view : 'Ab . 'Ab buffer -> (Obj.t,'Ab) view =
  fun v1  -> __proj__Buffer__item__v v1 

type ('Ab,'Ah,'Avb) live =
  (unit,unit,unit,unit,unit) LowStar_Monotonic_Buffer.live












type ('Ab,'Avb,'Ah,'Ah') modifies =
  (unit,unit,unit) LowStar_Monotonic_Buffer.modifies






