open Prims
type ('Aa,'Ar,'dummyV0,'dummyV1) _closure =
  | Refl of 'Aa 
  | Step of 'Aa * 'Aa * 'Ar 
  | Closure of 'Aa * 'Aa * 'Aa * ('Aa,'Ar,unit,unit) _closure *
  ('Aa,'Ar,unit,unit) _closure 
let uu___is_Refl :
  'Aa 'Ar . 'Aa -> 'Aa -> ('Aa,'Ar,unit,unit) _closure -> Prims.bool =
  fun uu____147  ->
    fun uu____148  ->
      fun projectee  ->
        match projectee with | Refl x -> true | uu____162 -> false
  
let __proj__Refl__item__x :
  'Aa 'Ar . 'Aa -> 'Aa -> ('Aa,'Ar,unit,unit) _closure -> 'Aa =
  fun uu____215  ->
    fun uu____216  -> fun projectee  -> match projectee with | Refl x -> x
  
let uu___is_Step :
  'Aa 'Ar . 'Aa -> 'Aa -> ('Aa,'Ar,unit,unit) _closure -> Prims.bool =
  fun uu____274  ->
    fun uu____275  ->
      fun projectee  ->
        match projectee with | Step (x,y,_2) -> true | uu____291 -> false
  
let __proj__Step__item__x :
  'Aa 'Ar . 'Aa -> 'Aa -> ('Aa,'Ar,unit,unit) _closure -> 'Aa =
  fun uu____346  ->
    fun uu____347  ->
      fun projectee  -> match projectee with | Step (x,y,_2) -> x
  
let __proj__Step__item__y :
  'Aa 'Ar . 'Aa -> 'Aa -> ('Aa,'Ar,unit,unit) _closure -> 'Aa =
  fun uu____405  ->
    fun uu____406  ->
      fun projectee  -> match projectee with | Step (x,y,_2) -> y
  
let __proj__Step__item___2 :
  'Aa 'Ar . 'Aa -> 'Aa -> ('Aa,'Ar,unit,unit) _closure -> 'Ar =
  fun uu____464  ->
    fun uu____465  ->
      fun projectee  -> match projectee with | Step (x,y,_2) -> _2
  
let uu___is_Closure :
  'Aa 'Ar . 'Aa -> 'Aa -> ('Aa,'Ar,unit,unit) _closure -> Prims.bool =
  fun uu____527  ->
    fun uu____528  ->
      fun projectee  ->
        match projectee with
        | Closure (x,y,z,_3,_4) -> true
        | uu____566 -> false
  
let __proj__Closure__item__x :
  'Aa 'Ar . 'Aa -> 'Aa -> ('Aa,'Ar,unit,unit) _closure -> 'Aa =
  fun uu____623  ->
    fun uu____624  ->
      fun projectee  -> match projectee with | Closure (x,y,z,_3,_4) -> x
  
let __proj__Closure__item__y :
  'Aa 'Ar . 'Aa -> 'Aa -> ('Aa,'Ar,unit,unit) _closure -> 'Aa =
  fun uu____706  ->
    fun uu____707  ->
      fun projectee  -> match projectee with | Closure (x,y,z,_3,_4) -> y
  
let __proj__Closure__item__z :
  'Aa 'Ar . 'Aa -> 'Aa -> ('Aa,'Ar,unit,unit) _closure -> 'Aa =
  fun uu____789  ->
    fun uu____790  ->
      fun projectee  -> match projectee with | Closure (x,y,z,_3,_4) -> z
  
let __proj__Closure__item___3 :
  'Aa 'Ar .
    'Aa ->
      'Aa -> ('Aa,'Ar,unit,unit) _closure -> ('Aa,'Ar,unit,unit) _closure
  =
  fun uu____882  ->
    fun uu____883  ->
      fun projectee  -> match projectee with | Closure (x,y,z,_3,_4) -> _3
  
let __proj__Closure__item___4 :
  'Aa 'Ar .
    'Aa ->
      'Aa -> ('Aa,'Ar,unit,unit) _closure -> ('Aa,'Ar,unit,unit) _closure
  =
  fun uu____975  ->
    fun uu____976  ->
      fun projectee  -> match projectee with | Closure (x,y,z,_3,_4) -> _4
  


type ('Aa,'Ar,'Auu____1058,'Auu____1059) closure =
  ('Aa,'Ar,unit,unit) _closure




