open Prims
type ('Aa,'Auu____23,'Auu____24) trivial_preorder = unit
type 'Aa buffer = ('Aa,unit,unit) LowStar_Monotonic_Buffer.mbuffer
let null : 'Aa . unit -> 'Aa buffer =
  fun uu____109  -> LowStar_Monotonic_Buffer.mnull () 


type 'Aa pointer = 'Aa buffer
type 'Aa pointer_or_null = 'Aa buffer
let sub :
  'Aa .
    unit ->
      ('Aa,('Aa,unit,unit) trivial_preorder,('Aa,unit,unit) trivial_preorder)
        LowStar_Monotonic_Buffer.mbuffer ->
        FStar_UInt32.t ->
          unit ->
            ('Aa,('Aa,unit,unit) trivial_preorder,('Aa,unit,unit)
                                                    trivial_preorder)
              LowStar_Monotonic_Buffer.mbuffer
  = fun uu____341  -> LowStar_Monotonic_Buffer.msub 
let offset :
  'Aa .
    unit ->
      ('Aa,('Aa,unit,unit) trivial_preorder,('Aa,unit,unit) trivial_preorder)
        LowStar_Monotonic_Buffer.mbuffer ->
        FStar_UInt32.t ->
          ('Aa,('Aa,unit,unit) trivial_preorder,('Aa,unit,unit)
                                                  trivial_preorder)
            LowStar_Monotonic_Buffer.mbuffer
  = fun uu____568  -> LowStar_Monotonic_Buffer.moffset 
type ('Aa,'Alen) lbuffer = ('Aa,unit,unit) LowStar_Monotonic_Buffer.mbuffer
let gcmalloc :
  'Aa .
    unit ->
      unit ->
        'Aa ->
          FStar_UInt32.t ->
            ('Aa,('Aa,unit,unit) trivial_preorder,('Aa,unit,unit)
                                                    trivial_preorder)
              LowStar_Monotonic_Buffer.mbuffer
  = fun uu____805  -> LowStar_Monotonic_Buffer.mgcmalloc 
let malloc :
  'Aa .
    unit ->
      unit ->
        'Aa ->
          FStar_UInt32.t ->
            ('Aa,('Aa,unit,unit) trivial_preorder,('Aa,unit,unit)
                                                    trivial_preorder)
              LowStar_Monotonic_Buffer.mbuffer
  = fun uu____920  -> LowStar_Monotonic_Buffer.mmalloc 
let alloca :
  'Aa .
    unit ->
      'Aa ->
        FStar_UInt32.t ->
          ('Aa,('Aa,unit,unit) trivial_preorder,('Aa,unit,unit)
                                                  trivial_preorder)
            LowStar_Monotonic_Buffer.mbuffer
  = fun uu____1031  -> LowStar_Monotonic_Buffer.malloca 
let alloca_of_list :
  'Aa .
    unit ->
      'Aa Prims.list ->
        ('Aa,('Aa,unit,unit) trivial_preorder,('Aa,unit,unit)
                                                trivial_preorder)
          LowStar_Monotonic_Buffer.mbuffer
  = fun uu____1146  -> LowStar_Monotonic_Buffer.malloca_of_list 
let gcmalloc_of_list :
  'Aa .
    unit ->
      unit ->
        'Aa Prims.list ->
          ('Aa,('Aa,unit,unit) trivial_preorder,('Aa,unit,unit)
                                                  trivial_preorder)
            LowStar_Monotonic_Buffer.mbuffer
  = fun uu____1262  -> LowStar_Monotonic_Buffer.mgcmalloc_of_list 
type ('Aa,'Al) assign_list_t = 'Aa buffer -> unit
let rec assign_list : 'Aa . 'Aa Prims.list -> 'Aa buffer -> unit =
  fun l  ->
    fun b  ->
      match l with
      | [] -> let h = FStar_HyperStack_ST.get ()  in ()
      | hd1::tl1 ->
          let b_hd =
            LowStar_Monotonic_Buffer.msub b
              (FStar_UInt32.uint_to_t Prims.int_zero) ()
             in
          let b_tl =
            LowStar_Monotonic_Buffer.moffset b
              (FStar_UInt32.uint_to_t Prims.int_one)
             in
          let h = FStar_HyperStack_ST.get ()  in
          ((let h1 = FStar_HyperStack_ST.get ()  in
            LowStar_Monotonic_Buffer.upd' b_hd
              (FStar_UInt32.uint_to_t Prims.int_zero) hd1);
           (let h0 = FStar_HyperStack_ST.get ()  in
            assign_list tl1 b_tl;
            (let h1 = FStar_HyperStack_ST.get ()  in ())))
  