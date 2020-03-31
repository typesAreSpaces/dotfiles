open Prims
type u8 = FStar_UInt8.t
type u32 = FStar_UInt32.t
let (le_to_n : u8 FStar_Seq_Base.seq -> Prims.nat) =
  fun s  -> FStar_Endianness.le_to_n s 
let (frozen_until : u8 FStar_Seq_Base.seq -> Prims.nat) =
  fun s  ->
    le_to_n (FStar_Seq_Base.slice s Prims.int_zero (Prims.of_int (4)))
  
type ('As1,'As2) pre = unit
type ('Auu____50,'Auu____51) prefix_freezable_preorder = unit

type ('An,'As) frozen_until_at_least = unit
type ('Ai,'Aj,'Asnap,'As) slice_is = unit
type buffer = (u8,unit,unit) LowStar_Monotonic_Buffer.mbuffer
type 'Alen lbuffer = buffer
type ('Ar,'Alen) malloc_pre = unit
type ('Ah0,'Ab,'Ah1) alloc_post_mem_common = unit
let (update_frozen_until_alloc :
  (u8,(unit,unit) prefix_freezable_preorder,(unit,unit)
                                              prefix_freezable_preorder)
    LowStar_Monotonic_Buffer.mbuffer -> unit)
  =
  fun b  ->
    LowStar_Endianness.store32_le_i b (FStar_UInt32.uint_to_t Prims.int_zero)
      (FStar_UInt32.uint_to_t (Prims.of_int (4)));
    LowStar_Monotonic_Buffer.witness_p b ()
  
let (gcmalloc : unit -> u32 -> buffer) =
  fun r  ->
    fun len  ->
      let h0 = FStar_HyperStack_ST.get ()  in
      let b =
        LowStar_Monotonic_Buffer.mgcmalloc ()
          (FStar_UInt8.uint_to_t Prims.int_zero)
          (FStar_UInt32.add len (FStar_UInt32.uint_to_t (Prims.of_int (4))))
         in
      let h = FStar_HyperStack_ST.get ()  in update_frozen_until_alloc b; b
  
let (malloc : unit -> u32 -> buffer) =
  fun r  ->
    fun len  ->
      let h0 = FStar_HyperStack_ST.get ()  in
      let b =
        LowStar_Monotonic_Buffer.mmalloc ()
          (FStar_UInt8.uint_to_t Prims.int_zero)
          (FStar_UInt32.add len (FStar_UInt32.uint_to_t (Prims.of_int (4))))
         in
      let h = FStar_HyperStack_ST.get ()  in update_frozen_until_alloc b; b
  
type 'Alen alloca_pre = unit
let (alloca : u32 -> buffer) =
  fun len  ->
    let h0 = FStar_HyperStack_ST.get ()  in
    let b =
      LowStar_Monotonic_Buffer.malloca (FStar_UInt8.uint_to_t Prims.int_zero)
        (FStar_UInt32.add len (FStar_UInt32.uint_to_t (Prims.of_int (4))))
       in
    let h = FStar_HyperStack_ST.get ()  in update_frozen_until_alloc b; b
  
let (upd : buffer -> u32 -> u8 -> unit) =
  fun b  ->
    fun i  ->
      fun v1  ->
        LowStar_Monotonic_Buffer.recall_p b ();
        (let h = FStar_HyperStack_ST.get ()  in
         LowStar_Monotonic_Buffer.upd' b i v1)
  

let (freeze : buffer -> u32 -> unit) =
  fun b  ->
    fun i  ->
      LowStar_Monotonic_Buffer.recall_p b ();
      LowStar_Endianness.store32_le_i b
        (FStar_UInt32.uint_to_t Prims.int_zero) i;
      LowStar_Monotonic_Buffer.witness_p b ()
  
let (frozen_until_st : buffer -> u32) =
  fun b  ->
    LowStar_Endianness.load32_le_i b (FStar_UInt32.uint_to_t Prims.int_zero)
  
let (witness_slice : buffer -> u32 -> u32 -> unit -> unit) =
  fun b  ->
    fun i  -> fun j  -> fun snap  -> LowStar_Monotonic_Buffer.witness_p b ()
  
let (recall_slice : buffer -> u32 -> u32 -> unit -> unit) =
  fun b  ->
    fun i  -> fun j  -> fun snap  -> LowStar_Monotonic_Buffer.recall_p b ()
  
let (witness_frozen_until : buffer -> Prims.nat -> unit) =
  fun b  -> fun n1  -> LowStar_Monotonic_Buffer.witness_p b () 
let (recall_frozen_until : buffer -> Prims.nat -> unit) =
  fun b  -> fun n1  -> LowStar_Monotonic_Buffer.recall_p b () 
let (recall_frozen_until_default : buffer -> unit) =
  fun b  -> LowStar_Monotonic_Buffer.recall_p b () 