open Prims
let new_to_old_st :
  'At . 'At LowStar_Buffer.buffer -> 'At FStar_Buffer.buffer =
  fun b  -> failwith "Not yet implemented:new_to_old_st" 
let old_to_new_st :
  'At . 'At FStar_Buffer.buffer -> 'At LowStar_Buffer.buffer =
  fun b  -> failwith "Not yet implemented:old_to_new_st" 
type ('Ais_new,'Auu____74,'Auu____75) old_and_new_aloc = Obj.t
let (old_and_new_cl : Prims.bool -> Obj.t FStar_ModifiesGen.cls) =
  fun a1  ->
    (fun is_new  ->
       if is_new
       then
         Obj.magic
           (Obj.repr
              (FStar_ModifiesGen.raise_cls LowStar_Monotonic_Buffer.cloc_cls))
       else Obj.magic (Obj.repr FStar_Modifies.cloc_cls)) a1
  
let (old_and_new_cl_union :
  (Obj.t,unit,unit) FStar_ModifiesGen.aloc_union FStar_ModifiesGen.cls) =
  FStar_ModifiesGen.cls_union old_and_new_cl 














let coerce : 'At2 'At1 . 'At1 -> 'At2 = fun a2  -> (fun x  -> Obj.magic x) a2 







let ex1 :
  'Aa . Prims.nat LowStar_Buffer.buffer -> 'Aa LowStar_Buffer.buffer -> unit
  =
  fun b  ->
    fun b1  ->
      let old = new_to_old_st b  in
      FStar_Buffer.upd old (FStar_UInt32.uint_to_t Prims.int_zero)
        Prims.int_zero
  
let new_eqb :
  'Aa .
    'Aa LowStar_Buffer.buffer ->
      'Aa LowStar_Buffer.buffer -> FStar_UInt32.t -> Prims.bool
  =
  fun b1  ->
    fun b2  ->
      fun len  ->
        let b1' = new_to_old_st b1  in
        let b2' = new_to_old_st b2  in FStar_Buffer.eqb b1' b2' len
  
let new_blit :
  'At .
    'At LowStar_Buffer.buffer ->
      FStar_UInt32.t ->
        'At LowStar_Buffer.buffer -> FStar_UInt32.t -> FStar_UInt32.t -> unit
  =
  fun src  ->
    fun idx_src  ->
      fun dst  ->
        fun idx_dst  ->
          fun len  ->
            let src' = new_to_old_st src  in
            let dst' = new_to_old_st dst  in
            FStar_Buffer.blit src' idx_src dst' idx_dst len
  
let new_fill :
  'At . 'At LowStar_Buffer.buffer -> 'At -> FStar_UInt32.t -> unit =
  fun b  ->
    fun z  ->
      fun len  -> let b' = new_to_old_st b  in FStar_Buffer.fill b' z len
  
let ex1' :
  'Aa . Prims.nat FStar_Buffer.buffer -> 'Aa FStar_Buffer.buffer -> unit =
  fun b  ->
    fun b1  ->
      let ne = old_to_new_st b  in
      let h = FStar_HyperStack_ST.get ()  in
      LowStar_Monotonic_Buffer.upd' ne
        (FStar_UInt32.uint_to_t Prims.int_zero) Prims.int_zero
  
let ex1'' :
  'Aa . Prims.nat LowStar_Buffer.buffer -> 'Aa LowStar_Buffer.buffer -> unit
  =
  fun b  ->
    fun b1  ->
      let old = new_to_old_st b  in
      let old1 = new_to_old_st b1  in ex1' old old1
  