open Prims
type ('Aa,'As1,'As2) initialization_preorder = unit
type 'Aa ubuffer =
  ('Aa FStar_Pervasives_Native.option,unit,unit)
    LowStar_Monotonic_Buffer.mbuffer
let unull : 'Aa . unit -> 'Aa ubuffer =
  fun uu____112  -> LowStar_Monotonic_Buffer.mnull () 


type 'Aa pointer = 'Aa ubuffer
type 'Aa pointer_or_null = 'Aa ubuffer
let usub :
  'Aa .
    unit ->
      ('Aa FStar_Pervasives_Native.option,('Aa,unit,unit)
                                            initialization_preorder,('Aa,
                                                                    unit,
                                                                    unit)
                                                                    initialization_preorder)
        LowStar_Monotonic_Buffer.mbuffer ->
        FStar_UInt32.t ->
          unit ->
            ('Aa FStar_Pervasives_Native.option,('Aa,unit,unit)
                                                  initialization_preorder,
              ('Aa,unit,unit) initialization_preorder)
              LowStar_Monotonic_Buffer.mbuffer
  = fun uu____350  -> LowStar_Monotonic_Buffer.msub 
let uoffset :
  'Aa .
    unit ->
      ('Aa FStar_Pervasives_Native.option,('Aa,unit,unit)
                                            initialization_preorder,('Aa,
                                                                    unit,
                                                                    unit)
                                                                    initialization_preorder)
        LowStar_Monotonic_Buffer.mbuffer ->
        FStar_UInt32.t ->
          ('Aa FStar_Pervasives_Native.option,('Aa,unit,unit)
                                                initialization_preorder,
            ('Aa,unit,unit) initialization_preorder)
            LowStar_Monotonic_Buffer.mbuffer
  = fun uu____583  -> LowStar_Monotonic_Buffer.moffset 
type ('Aa,'Ai,'As) ipred = unit
type ('Aa,'Ab,'Ai) initialized_at =
  ('Aa FStar_Pervasives_Native.option,unit,unit,unit,unit)
    LowStar_Monotonic_Buffer.witnessed
let uindex : 'Aa . 'Aa ubuffer -> FStar_UInt32.t -> 'Aa =
  fun b  ->
    fun i  ->
      let y_opt = LowStar_Monotonic_Buffer.index b i  in
      LowStar_Monotonic_Buffer.recall_p b ();
      FStar_Pervasives_Native.__proj__Some__item__v y_opt
  
let uupd : 'Aa . 'Aa ubuffer -> FStar_UInt32.t -> 'Aa -> unit =
  fun b  ->
    fun i  ->
      fun v1  ->
        (let h = FStar_HyperStack_ST.get ()  in
         LowStar_Monotonic_Buffer.upd' b i (FStar_Pervasives_Native.Some v1));
        LowStar_Monotonic_Buffer.witness_p b ()
  
type ('Aa,'Alen) lubuffer = 'Aa ubuffer
type ('Aa,'Alen,'Ar) lubuffer_or_null = 'Aa ubuffer
let ugcmalloc : 'Aa . unit -> FStar_UInt32.t -> 'Aa ubuffer =
  fun r  ->
    fun len  ->
      LowStar_Monotonic_Buffer.mgcmalloc () FStar_Pervasives_Native.None len
  
let ugcmalloc_partial : 'Aa . unit -> FStar_UInt32.t -> 'Aa ubuffer =
  fun r  ->
    fun len  ->
      LowStar_Monotonic_Buffer.mgcmalloc () FStar_Pervasives_Native.None len
  
let umalloc : 'Aa . unit -> FStar_UInt32.t -> 'Aa ubuffer =
  fun r  ->
    fun len  ->
      LowStar_Monotonic_Buffer.mmalloc () FStar_Pervasives_Native.None len
  
let umalloc_partial : 'Aa . unit -> FStar_UInt32.t -> 'Aa ubuffer =
  fun r  ->
    fun len  ->
      LowStar_Monotonic_Buffer.mmalloc () FStar_Pervasives_Native.None len
  
let ualloca : 'Aa . FStar_UInt32.t -> 'Aa ubuffer =
  fun len  ->
    LowStar_Monotonic_Buffer.malloca FStar_Pervasives_Native.None len
  
type ('Aa,'Arrel,'Arel,'Asrc,'Aidx_src,'Adst,'Aidx_dst,'Aj) valid_j_for_blit =
  unit
type ('Aa,'Arrel,'Arel,'Asrc,'Aidx_src,'Adst,'Aidx_dst,'Aj,'Ah0,'Ah1) ublit_post_j =
  unit
let ublit :
  'Aa 'Arrel 'Arel .
    ('Aa,'Arrel,'Arel) LowStar_Monotonic_Buffer.mbuffer ->
      FStar_UInt32.t ->
        'Aa ubuffer -> FStar_UInt32.t -> FStar_UInt32.t -> unit
  =
  fun src  ->
    fun idx_src  ->
      fun dst  ->
        fun idx_dst  ->
          fun len  ->
            let rec aux j =
              if j = len
              then ()
              else
                if FStar_UInt32.lt j len
                then
                  ((let uu____1761 =
                      LowStar_Monotonic_Buffer.index src
                        (FStar_UInt32.add idx_src j)
                       in
                    uupd dst (FStar_UInt32.add idx_dst j) uu____1761);
                   aux
                     (FStar_UInt32.add j
                        (FStar_UInt32.uint_to_t Prims.int_one)))
                else ()
               in
            aux (FStar_UInt32.uint_to_t Prims.int_zero)
  
let witness_initialized : 'Aa . 'Aa ubuffer -> Prims.nat -> unit =
  fun b  -> fun i  -> LowStar_Monotonic_Buffer.witness_p b () 
let recall_initialized : 'Aa . 'Aa ubuffer -> Prims.nat -> unit =
  fun b  -> fun i  -> LowStar_Monotonic_Buffer.recall_p b () 