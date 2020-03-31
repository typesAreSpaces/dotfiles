open Prims
let op_Array_Access :
  'Aa 'Arrel 'Arel .
    unit ->
      ('Aa,'Arrel,'Arel) LowStar_Monotonic_Buffer.mbuffer ->
        FStar_UInt32.t -> 'Aa
  = fun uu____60  -> LowStar_Monotonic_Buffer.index 
let op_Array_Assignment :
  'Aa 'Arrel 'Arel .
    ('Aa,'Arrel,'Arel) LowStar_Monotonic_Buffer.mbuffer ->
      FStar_UInt32.t -> 'Aa -> unit
  =
  fun b  ->
    fun i  ->
      fun v1  ->
        let h = FStar_HyperStack_ST.get ()  in
        LowStar_Monotonic_Buffer.upd' b i v1
  
let op_Bang_Star :
  'Aa 'Arrel 'Arel .
    ('Aa,'Arrel,'Arel) LowStar_Monotonic_Buffer.mbuffer -> 'Aa
  =
  fun p  ->
    LowStar_Monotonic_Buffer.index p (FStar_UInt32.uint_to_t Prims.int_zero)
  
let op_Star_Equals :
  'Aa 'Arrel 'Arel .
    ('Aa,'Arrel,'Arel) LowStar_Monotonic_Buffer.mbuffer -> 'Aa -> unit
  =
  fun p  ->
    fun v1  ->
      let h = FStar_HyperStack_ST.get ()  in
      LowStar_Monotonic_Buffer.upd' p (FStar_UInt32.uint_to_t Prims.int_zero)
        v1
  
let blit :
  'Aa 'Arrel1 'Arel1 'Arrel2 'Arel2 .
    unit ->
      ('Aa,'Arrel1,'Arrel2) LowStar_Monotonic_Buffer.mbuffer ->
        FStar_UInt32.t ->
          ('Aa,'Arel1,'Arel2) LowStar_Monotonic_Buffer.mbuffer ->
            FStar_UInt32.t -> FStar_UInt32.t -> unit
  = fun uu____500  -> LowStar_Monotonic_Buffer.blit 