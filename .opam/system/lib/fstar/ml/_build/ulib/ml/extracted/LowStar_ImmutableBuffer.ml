open Prims
type ('Aa,'As1,'As2) immutable_preorder = unit
type 'Aa ibuffer = ('Aa,unit,unit) LowStar_Monotonic_Buffer.mbuffer
let inull : 'Aa . unit -> 'Aa ibuffer =
  fun uu____115  -> LowStar_Monotonic_Buffer.mnull () 


type 'Aa ipointer = 'Aa ibuffer
type 'Aa ipointer_or_null = 'Aa ibuffer
let isub :
  'Aa .
    unit ->
      ('Aa,('Aa,unit,unit) immutable_preorder,('Aa,unit,unit)
                                                immutable_preorder)
        LowStar_Monotonic_Buffer.mbuffer ->
        FStar_UInt32.t ->
          unit ->
            ('Aa,('Aa,unit,unit) immutable_preorder,('Aa,unit,unit)
                                                      immutable_preorder)
              LowStar_Monotonic_Buffer.mbuffer
  = fun uu____347  -> LowStar_Monotonic_Buffer.msub 
let ioffset :
  'Aa .
    unit ->
      ('Aa,('Aa,unit,unit) immutable_preorder,('Aa,unit,unit)
                                                immutable_preorder)
        LowStar_Monotonic_Buffer.mbuffer ->
        FStar_UInt32.t ->
          ('Aa,('Aa,unit,unit) immutable_preorder,('Aa,unit,unit)
                                                    immutable_preorder)
            LowStar_Monotonic_Buffer.mbuffer
  = fun uu____574  -> LowStar_Monotonic_Buffer.moffset 
type ('Aa,'As,'As1) cpred = unit
type ('a,'As,'As') seq_eq = unit
type ('Aa,'Ab,'As) value_is =
  ('Aa,unit,unit,unit,unit) LowStar_Monotonic_Buffer.witnessed

type ('Aa,'Alen,'As) libuffer =
  ('Aa,unit,unit) LowStar_Monotonic_Buffer.mbuffer
type ('Aa,'Alen,'Ar,'As) libuffer_or_null =
  ('Aa,unit,unit) LowStar_Monotonic_Buffer.mbuffer
let igcmalloc :
  'Aa .
    unit ->
      'Aa ->
        FStar_UInt32.t ->
          ('Aa,('Aa,unit,unit) immutable_preorder,('Aa,unit,unit)
                                                    immutable_preorder)
            LowStar_Monotonic_Buffer.mbuffer
  =
  fun r  ->
    fun init1  ->
      fun len  ->
        let b = LowStar_Monotonic_Buffer.mgcmalloc () init1 len  in
        LowStar_Monotonic_Buffer.witness_p b (); b
  
let igcmalloc_and_blit :
  'Aa .
    unit ->
      unit ->
        unit ->
          ('Aa,Obj.t,Obj.t) LowStar_Monotonic_Buffer.mbuffer ->
            FStar_UInt32.t ->
              FStar_UInt32.t ->
                ('Aa,('Aa,unit,unit) immutable_preorder,('Aa,unit,unit)
                                                          immutable_preorder)
                  LowStar_Monotonic_Buffer.mbuffer
  =
  fun r  ->
    fun rrel1  ->
      fun rel1  ->
        fun src  ->
          fun id_src  ->
            fun len  ->
              let b =
                LowStar_Monotonic_Buffer.mgcmalloc_and_blit () () () src
                  id_src len
                 in
              let h0 = FStar_HyperStack_ST.get ()  in
              LowStar_Monotonic_Buffer.witness_p b (); b
  
let igcmalloc_partial :
  'Aa .
    unit ->
      'Aa ->
        FStar_UInt32.t ->
          ('Aa,('Aa,unit,unit) immutable_preorder,('Aa,unit,unit)
                                                    immutable_preorder)
            LowStar_Monotonic_Buffer.mbuffer
  = fun r  -> fun init1  -> fun len  -> igcmalloc () init1 len 
let imalloc :
  'Aa .
    unit ->
      'Aa ->
        FStar_UInt32.t ->
          ('Aa,('Aa,unit,unit) immutable_preorder,('Aa,unit,unit)
                                                    immutable_preorder)
            LowStar_Monotonic_Buffer.mbuffer
  =
  fun r  ->
    fun init1  ->
      fun len  ->
        let b = LowStar_Monotonic_Buffer.mmalloc () init1 len  in
        LowStar_Monotonic_Buffer.witness_p b (); b
  
let imalloc_and_blit :
  'Aa .
    unit ->
      unit ->
        unit ->
          ('Aa,Obj.t,Obj.t) LowStar_Monotonic_Buffer.mbuffer ->
            FStar_UInt32.t ->
              FStar_UInt32.t ->
                ('Aa,('Aa,unit,unit) immutable_preorder,('Aa,unit,unit)
                                                          immutable_preorder)
                  LowStar_Monotonic_Buffer.mbuffer
  =
  fun r  ->
    fun rrel1  ->
      fun rel1  ->
        fun src  ->
          fun id_src  ->
            fun len  ->
              let b =
                LowStar_Monotonic_Buffer.mmalloc_and_blit () () () src id_src
                  len
                 in
              let h0 = FStar_HyperStack_ST.get ()  in
              LowStar_Monotonic_Buffer.witness_p b (); b
  
let imalloc_partial :
  'Aa .
    unit ->
      'Aa ->
        FStar_UInt32.t ->
          ('Aa,('Aa,unit,unit) immutable_preorder,('Aa,unit,unit)
                                                    immutable_preorder)
            LowStar_Monotonic_Buffer.mbuffer
  = fun r  -> fun init1  -> fun len  -> imalloc () init1 len 
let ialloca :
  'Aa .
    'Aa ->
      FStar_UInt32.t ->
        ('Aa,('Aa,unit,unit) immutable_preorder,('Aa,unit,unit)
                                                  immutable_preorder)
          LowStar_Monotonic_Buffer.mbuffer
  =
  fun init1  ->
    fun len  ->
      let b = LowStar_Monotonic_Buffer.malloca init1 len  in
      LowStar_Monotonic_Buffer.witness_p b (); b
  
let ialloca_and_blit :
  'Aa 'Arrel1 'Arel1 .
    ('Aa,'Arrel1,'Arel1) LowStar_Monotonic_Buffer.mbuffer ->
      FStar_UInt32.t ->
        FStar_UInt32.t ->
          ('Aa,('Aa,unit,unit) immutable_preorder,('Aa,unit,unit)
                                                    immutable_preorder)
            LowStar_Monotonic_Buffer.mbuffer
  =
  fun src  ->
    fun id_src  ->
      fun len  ->
        let b = LowStar_Monotonic_Buffer.malloca_and_blit src id_src len  in
        let h0 = FStar_HyperStack_ST.get ()  in
        LowStar_Monotonic_Buffer.witness_p b (); b
  
let ialloca_of_list :
  'Aa .
    'Aa Prims.list ->
      ('Aa,('Aa,unit,unit) immutable_preorder,('Aa,unit,unit)
                                                immutable_preorder)
        LowStar_Monotonic_Buffer.mbuffer
  =
  fun init1  ->
    let b = LowStar_Monotonic_Buffer.malloca_of_list init1  in
    LowStar_Monotonic_Buffer.witness_p b (); b
  
let igcmalloc_of_list :
  'Aa .
    unit ->
      'Aa Prims.list ->
        ('Aa,('Aa,unit,unit) immutable_preorder,('Aa,unit,unit)
                                                  immutable_preorder)
          LowStar_Monotonic_Buffer.mbuffer
  =
  fun r  ->
    fun init1  ->
      let b = LowStar_Monotonic_Buffer.mgcmalloc_of_list () init1  in
      LowStar_Monotonic_Buffer.witness_p b (); b
  
let igcmalloc_of_list_partial :
  'Aa .
    unit ->
      'Aa Prims.list ->
        ('Aa,('Aa,unit,unit) immutable_preorder,('Aa,unit,unit)
                                                  immutable_preorder)
          LowStar_Monotonic_Buffer.mbuffer
  = fun r  -> fun init1  -> igcmalloc_of_list () init1 
let witness_contents : 'Aa . 'Aa ibuffer -> 'Aa FStar_Seq_Base.seq -> unit =
  fun b  -> fun s  -> LowStar_Monotonic_Buffer.witness_p b () 
let recall_contents : 'Aa . 'Aa ibuffer -> 'Aa FStar_Seq_Base.seq -> unit =
  fun b  -> fun s  -> LowStar_Monotonic_Buffer.recall_p b () 
let witness_value : 'Aa . 'Aa ibuffer -> unit =
  fun b  ->
    let h = FStar_HyperStack_ST.get ()  in
    LowStar_Monotonic_Buffer.witness_p b ()
  
let recall_value : 'Aa . 'Aa ibuffer -> unit -> unit =
  fun b  -> fun s  -> LowStar_Monotonic_Buffer.recall_p b () 

