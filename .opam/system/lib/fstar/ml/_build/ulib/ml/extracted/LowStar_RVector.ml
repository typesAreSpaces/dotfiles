open Prims
type ('Aa,'Arg) copyable =
  | Cpy of ('Aa -> 'Aa -> unit) 
let uu___is_Cpy :
  'Aa . 'Aa LowStar_Regional.regional -> ('Aa,unit) copyable -> Prims.bool =
  fun rg  -> fun projectee  -> true 
let __proj__Cpy__item__copy :
  'Aa .
    'Aa LowStar_Regional.regional ->
      ('Aa,unit) copyable -> 'Aa -> 'Aa -> unit
  = fun rg  -> fun projectee  -> match projectee with | Cpy copy -> copy 
type ('Aa,'Arg) rvector = 'Aa LowStar_Vector.vector

type ('Aa,'Arg,'Ah,'Ars,'Ai,'Aj) rs_elems_inv = unit
type ('Aa,'Arg,'Ah,'Arv,'Ai,'Aj) rv_elems_inv = unit
type ('Aa,'Arg,'Ah,'Arv) elems_inv = unit
type ('Aa,'Arg,'Ars,'Aprid,'Ai,'Aj) rs_elems_reg = unit
type ('Aa,'Arg,'Ah,'Arv,'Ai,'Aj) rv_elems_reg = unit
type ('Aa,'Arg,'Ah,'Arv) elems_reg = unit
type ('Aa,'Arg,'Ah,'Arv) rv_itself_inv = unit
type ('Aa,'Arg,'Ah,'Arv) rv_inv = unit







































let alloc_empty : 'Aa . 'Aa LowStar_Regional.regional -> ('Aa,unit) rvector =
  fun rg  ->
    LowStar_Vector.Vec
      ((FStar_UInt32.uint_to_t Prims.int_zero),
        (FStar_UInt32.uint_to_t Prims.int_zero),
        (LowStar_Monotonic_Buffer.mnull ()))
  
let rec alloc_ :
  'Aa .
    'Aa LowStar_Regional.regional ->
      ('Aa,unit) rvector -> LowStar_Vector.uint32_t -> unit
  =
  fun rg  ->
    fun rv  ->
      fun cidx  ->
        let hh0 = FStar_HyperStack_ST.get ()  in
        if cidx = (FStar_UInt32.uint_to_t Prims.int_zero)
        then ()
        else
          (FStar_HyperStack_ST.new_region ();
           (let v1 = LowStar_Regional.__proj__Rgl__item__r_alloc rg ()  in
            let hh1 = FStar_HyperStack_ST.get ()  in
            LowStar_Vector.assign rv
              (FStar_UInt32.sub cidx (FStar_UInt32.uint_to_t Prims.int_one))
              v1;
            (let hh2 = FStar_HyperStack_ST.get ()  in
             alloc_ rg rv
               (FStar_UInt32.sub cidx (FStar_UInt32.uint_to_t Prims.int_one));
             (let hh3 = FStar_HyperStack_ST.get ()  in ()))))
  
let alloc_rid :
  'Aa .
    'Aa LowStar_Regional.regional ->
      LowStar_Vector.uint32_t -> unit -> ('Aa,unit) rvector
  =
  fun rg  ->
    fun len  ->
      fun rid  ->
        let vec =
          LowStar_Vector.alloc_rid len
            (LowStar_Regional.__proj__Rgl__item__dummy rg) ()
           in
        alloc_ rg vec len; vec
  
let alloc_reserve :
  'Aa .
    'Aa LowStar_Regional.regional ->
      LowStar_Vector.uint32_t -> unit -> ('Aa,unit) rvector
  =
  fun rg  ->
    fun len  ->
      fun rid  ->
        LowStar_Vector.alloc_reserve len
          (LowStar_Regional.__proj__Rgl__item__dummy rg) ()
  
let alloc :
  'Aa .
    'Aa LowStar_Regional.regional ->
      LowStar_Vector.uint32_t -> ('Aa,unit) rvector
  =
  fun rg  ->
    fun len  -> FStar_HyperStack_ST.new_region (); alloc_rid rg len ()
  
let insert :
  'Aa .
    'Aa LowStar_Regional.regional ->
      ('Aa,unit) rvector -> 'Aa -> ('Aa,unit) rvector
  =
  fun rg  ->
    fun rv  ->
      fun v1  ->
        let hh0 = FStar_HyperStack_ST.get ()  in
        let irv = LowStar_Vector.insert rv v1  in
        let hh1 = FStar_HyperStack_ST.get ()  in irv
  
let insert_copy :
  'Aa .
    'Aa LowStar_Regional.regional ->
      ('Aa,unit) copyable -> ('Aa,unit) rvector -> 'Aa -> ('Aa,unit) rvector
  =
  fun rg  ->
    fun cp  ->
      fun rv  ->
        fun v1  ->
          let hh0 = FStar_HyperStack_ST.get ()  in
          FStar_HyperStack_ST.new_region ();
          (let nv = LowStar_Regional.__proj__Rgl__item__r_alloc rg ()  in
           let hh1 = FStar_HyperStack_ST.get ()  in
           let copy = __proj__Cpy__item__copy rg cp  in
           copy v1 nv;
           (let hh2 = FStar_HyperStack_ST.get ()  in insert rg rv nv))
  
let assign :
  'Aa .
    'Aa LowStar_Regional.regional ->
      ('Aa,unit) rvector -> LowStar_Vector.uint32_t -> 'Aa -> unit
  =
  fun rg  ->
    fun rv  ->
      fun i1  ->
        fun v1  ->
          let hh0 = FStar_HyperStack_ST.get ()  in
          LowStar_Vector.assign rv i1 v1;
          (let hh1 = FStar_HyperStack_ST.get ()  in ())
  

let assign_copy :
  'Aa .
    'Aa LowStar_Regional.regional ->
      ('Aa,unit) copyable ->
        ('Aa,unit) rvector -> LowStar_Vector.uint32_t -> 'Aa -> unit
  =
  fun rg  ->
    fun cp  ->
      fun rv  ->
        fun i1  ->
          fun v1  ->
            let hh0 = FStar_HyperStack_ST.get ()  in
            let copy = __proj__Cpy__item__copy rg cp  in
            (let uu____2241 = LowStar_Vector.index rv i1  in
             copy v1 uu____2241);
            (let hh1 = FStar_HyperStack_ST.get ()  in ())
  
let rec free_elems :
  'Aa .
    'Aa LowStar_Regional.regional ->
      ('Aa,unit) rvector -> LowStar_Vector.uint32_t -> unit
  =
  fun rg  ->
    fun rv  ->
      fun idx  ->
        let hh0 = FStar_HyperStack_ST.get ()  in
        (let uu____2295 = LowStar_Vector.index rv idx  in
         LowStar_Regional.__proj__Rgl__item__r_free rg uu____2295);
        (let hh1 = FStar_HyperStack_ST.get ()  in
         if idx <> (FStar_UInt32.uint_to_t Prims.int_zero)
         then
           free_elems rg rv
             (FStar_UInt32.sub idx (FStar_UInt32.uint_to_t Prims.int_one))
         else ())
  
let flush :
  'Aa .
    'Aa LowStar_Regional.regional ->
      ('Aa,unit) rvector -> LowStar_Vector.uint32_t -> ('Aa,unit) rvector
  =
  fun rg  ->
    fun rv  ->
      fun i1  ->
        let hh0 = FStar_HyperStack_ST.get ()  in
        if i1 = (FStar_UInt32.uint_to_t Prims.int_zero)
        then ()
        else
          free_elems rg rv
            (FStar_UInt32.sub i1 (FStar_UInt32.uint_to_t Prims.int_one));
        (let hh1 = FStar_HyperStack_ST.get ()  in
         let frv =
           LowStar_Vector.flush rv
             (LowStar_Regional.__proj__Rgl__item__dummy rg) i1
            in
         let hh2 = FStar_HyperStack_ST.get ()  in frv)
  
let rec free_elems_from :
  'Aa .
    'Aa LowStar_Regional.regional ->
      ('Aa,unit) rvector -> LowStar_Vector.uint32_t -> unit
  =
  fun rg  ->
    fun rv  ->
      fun idx  ->
        let hh0 = FStar_HyperStack_ST.get ()  in
        (let uu____2458 = LowStar_Vector.index rv idx  in
         LowStar_Regional.__proj__Rgl__item__r_free rg uu____2458);
        (let hh1 = FStar_HyperStack_ST.get ()  in
         if
           FStar_UInt32.lt
             (FStar_UInt32.add idx (FStar_UInt32.uint_to_t Prims.int_one))
             (match rv with | LowStar_Vector.Vec (sz,cap,vs) -> sz)
         then
           free_elems_from rg rv
             (FStar_UInt32.add idx (FStar_UInt32.uint_to_t Prims.int_one))
         else ())
  
let shrink :
  'Aa .
    'Aa LowStar_Regional.regional ->
      ('Aa,unit) rvector -> LowStar_Vector.uint32_t -> ('Aa,unit) rvector
  =
  fun rg  ->
    fun rv  ->
      fun new_size  ->
        let size = match rv with | LowStar_Vector.Vec (sz,cap,vs) -> sz  in
        let hh0 = FStar_HyperStack_ST.get ()  in
        if FStar_UInt32.gte new_size size
        then rv
        else
          (free_elems_from rg rv new_size;
           (let hh1 = FStar_HyperStack_ST.get ()  in
            let frv = LowStar_Vector.shrink rv new_size  in
            let hh2 = FStar_HyperStack_ST.get ()  in frv))
  
let free : 'Aa . 'Aa LowStar_Regional.regional -> ('Aa,unit) rvector -> unit
  =
  fun rg  ->
    fun rv  ->
      let hh0 = FStar_HyperStack_ST.get ()  in
      if
        (match rv with | LowStar_Vector.Vec (sz,cap,vs) -> sz) =
          (FStar_UInt32.uint_to_t Prims.int_zero)
      then ()
      else
        free_elems rg rv
          (FStar_UInt32.sub
             (match rv with | LowStar_Vector.Vec (sz,cap,vs) -> sz)
             (FStar_UInt32.uint_to_t Prims.int_one));
      (let hh1 = FStar_HyperStack_ST.get ()  in LowStar_Vector.free rv)
  