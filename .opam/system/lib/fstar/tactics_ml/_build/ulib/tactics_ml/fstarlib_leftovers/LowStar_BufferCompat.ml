open Prims
type ('Aa,'Ar,'Alen,'Ab,'Ah0,'Ah1,'As) rcreate_post_mem_common = unit
let rfree : 'Aa . 'Aa LowStar_Buffer.buffer -> unit =
  fun b  -> LowStar_Monotonic_Buffer.free b 
let rcreate :
  'Aa . unit -> 'Aa -> FStar_UInt32.t -> 'Aa LowStar_Buffer.buffer =
  fun r  ->
    fun init1  ->
      fun len  ->
        let b = LowStar_Monotonic_Buffer.mgcmalloc () init1 len  in b
  
let rcreate_mm :
  'Aa . unit -> 'Aa -> FStar_UInt32.t -> 'Aa LowStar_Buffer.buffer =
  fun r  ->
    fun init1  -> fun len  -> LowStar_Monotonic_Buffer.mmalloc () init1 len
  
let create : 'Aa . 'Aa -> FStar_UInt32.t -> 'Aa LowStar_Buffer.buffer =
  fun init1  -> fun len  -> LowStar_Monotonic_Buffer.malloca init1 len 
type ('Aa,'Ainit) createL_pre = unit
let createL : 'Aa . 'Aa Prims.list -> 'Aa LowStar_Buffer.buffer =
  fun init1  -> LowStar_Monotonic_Buffer.malloca_of_list init1 