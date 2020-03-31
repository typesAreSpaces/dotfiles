open Prims

let buffer_dummy : 'Auu____8 . unit -> 'Auu____8 LowStar_Buffer.buffer =
  fun uu____11  -> LowStar_Monotonic_Buffer.mnull () 
type ('Aa,'Alen,'Ah,'Av) buffer_r_inv = unit

type ('Aa,'Alen) buffer_repr = 'Aa FStar_Seq_Base.seq



type ('Aa,'Av) buffer_r_alloc_p = unit
let buffer_r_alloc :
  'Aa . 'Aa -> FStar_UInt32.t -> unit -> 'Aa LowStar_Buffer.buffer =
  fun ia  -> fun len  -> fun r  -> LowStar_Monotonic_Buffer.mmalloc () ia len 
let buffer_r_free : 'Aa . FStar_UInt32.t -> 'Aa LowStar_Buffer.buffer -> unit
  = fun len  -> fun v1  -> LowStar_Monotonic_Buffer.free v1 
let buffer_copy :
  'Aa .
    FStar_UInt32.t ->
      'Aa LowStar_Buffer.buffer -> 'Aa LowStar_Buffer.buffer -> unit
  =
  fun len  ->
    fun src  ->
      fun dst  ->
        LowStar_Monotonic_Buffer.blit src
          (FStar_UInt32.uint_to_t Prims.int_zero) dst
          (FStar_UInt32.uint_to_t Prims.int_zero) len
  
let buffer_regional :
  'Aa .
    'Aa ->
      FStar_UInt32.t -> 'Aa LowStar_Buffer.buffer LowStar_Regional.regional
  =
  fun ia  ->
    fun len  ->
      LowStar_Regional.Rgl
        ((), (), (buffer_dummy ()), (), (), (), (), (), (), (),
          (buffer_r_alloc ia len), (buffer_r_free len))
  
let buffer_copyable :
  'Aa .
    'Aa ->
      FStar_UInt32.t ->
        ('Aa LowStar_Buffer.buffer,unit) LowStar_RVector.copyable
  = fun ia  -> fun len  -> LowStar_RVector.Cpy (buffer_copy len) 

let vector_dummy :
  'Aa . 'Aa LowStar_Regional.regional -> ('Aa,unit) LowStar_RVector.rvector =
  fun rg  ->
    LowStar_Vector.Vec
      ((FStar_UInt32.uint_to_t Prims.int_zero),
        (FStar_UInt32.uint_to_t Prims.int_zero),
        (LowStar_Monotonic_Buffer.mnull ()))
  
type ('Aa,'Arg,'Ah,'Av) vector_r_inv = unit

type ('Aa,'Arg) vector_repr = Obj.t FStar_Seq_Base.seq



type ('Aa,'Arg,'Av) vector_r_alloc_p = unit
let vector_r_alloc :
  'Aa .
    'Aa LowStar_Regional.regional ->
      unit -> ('Aa,unit) LowStar_RVector.rvector
  =
  fun rg  ->
    fun r  ->
      FStar_HyperStack_ST.new_region ();
      LowStar_Vector.alloc_reserve (FStar_UInt32.uint_to_t Prims.int_one)
        (LowStar_Regional.__proj__Rgl__item__dummy rg) ()
  
let vector_r_free :
  'Aa .
    'Aa LowStar_Regional.regional ->
      ('Aa,unit) LowStar_RVector.rvector -> unit
  = fun rg  -> fun v1  -> LowStar_RVector.free rg v1 
let vector_regional :
  'Aa .
    'Aa LowStar_Regional.regional ->
      ('Aa,unit) LowStar_RVector.rvector LowStar_Regional.regional
  =
  fun rg  ->
    LowStar_Regional.Rgl
      ((), (), (vector_dummy rg), (), (), (), (), (), (), (),
        (vector_r_alloc rg), (vector_r_free rg))
  