open Prims
type uint32_t = FStar_UInt32.t
let (max_uint32 : uint32_t) =
  FStar_UInt32.uint_to_t (Prims.parse_int "4294967295") 
type 'Aa vector_str =
  | Vec of uint32_t * uint32_t * 'Aa LowStar_Buffer.buffer 
let uu___is_Vec : 'Aa . 'Aa vector_str -> Prims.bool = fun projectee  -> true 
let __proj__Vec__item__sz : 'Aa . 'Aa vector_str -> uint32_t =
  fun projectee  -> match projectee with | Vec (sz,cap,vs) -> sz 
let __proj__Vec__item__cap : 'Aa . 'Aa vector_str -> uint32_t =
  fun projectee  -> match projectee with | Vec (sz,cap,vs) -> cap 
let __proj__Vec__item__vs : 'Aa . 'Aa vector_str -> 'Aa LowStar_Buffer.buffer
  = fun projectee  -> match projectee with | Vec (sz,cap,vs) -> vs 
type 'Aa vector = 'Aa vector_str

let size_of : 'Aa . 'Aa vector -> uint32_t =
  fun vec  -> match vec with | Vec (sz,cap,vs) -> sz 
let capacity_of : 'Aa . 'Aa vector -> uint32_t =
  fun vec  -> match vec with | Vec (sz,cap,vs) -> cap 
let is_empty : 'Aa . 'Aa vector -> Prims.bool =
  fun vec  ->
    (match vec with | Vec (sz,cap,vs) -> sz) =
      (FStar_UInt32.uint_to_t Prims.int_zero)
  

type ('Aa,'Ah,'Avec) live =
  ('Aa,unit,unit,unit,unit) LowStar_Monotonic_Buffer.live
type ('Aa,'Avec) freeable =
  ('Aa,unit,unit,unit) LowStar_Monotonic_Buffer.freeable










type ('Ah0,'Ah1) hmap_dom_eq = (unit,unit,unit) FStar_Set.equal


let alloc_empty : 'Aa . unit -> 'Aa vector =
  fun uu____619  ->
    Vec
      ((FStar_UInt32.uint_to_t Prims.int_zero),
        (FStar_UInt32.uint_to_t Prims.int_zero),
        (LowStar_Monotonic_Buffer.mnull ()))
  

let alloc_rid : 'Aa . uint32_t -> 'Aa -> unit -> 'Aa vector =
  fun len  ->
    fun v1  ->
      fun rid  ->
        let uu____705 = LowStar_Monotonic_Buffer.mmalloc () v1 len  in
        Vec (len, len, uu____705)
  
let alloc : 'Aa . uint32_t -> 'Aa -> 'Aa vector =
  fun len  -> fun v1  -> alloc_rid len v1 () 
let alloc_reserve : 'Aa . uint32_t -> 'Aa -> unit -> 'Aa vector =
  fun len  ->
    fun ia  ->
      fun rid  ->
        let uu____802 = LowStar_Monotonic_Buffer.mmalloc () ia len  in
        Vec ((FStar_UInt32.uint_to_t Prims.int_zero), len, uu____802)
  
let alloc_by_buffer :
  'Aa . uint32_t -> 'Aa LowStar_Buffer.buffer -> 'Aa vector =
  fun len  -> fun buf1  -> Vec (len, len, buf1) 
let free : 'Aa . 'Aa vector -> unit =
  fun vec  ->
    LowStar_Monotonic_Buffer.free (match vec with | Vec (sz,cap,vs) -> vs)
  

let index : 'Aa . 'Aa vector -> uint32_t -> 'Aa =
  fun vec  ->
    fun i1  ->
      LowStar_Monotonic_Buffer.index (match vec with | Vec (sz,cap,vs) -> vs)
        i1
  
let front : 'Aa . 'Aa vector -> 'Aa =
  fun vec  ->
    LowStar_Monotonic_Buffer.index (match vec with | Vec (sz,cap,vs) -> vs)
      (FStar_UInt32.uint_to_t Prims.int_zero)
  
let back : 'Aa . 'Aa vector -> 'Aa =
  fun vec  ->
    LowStar_Monotonic_Buffer.index (match vec with | Vec (sz,cap,vs) -> vs)
      (FStar_UInt32.sub (match vec with | Vec (sz,cap,vs) -> sz)
         (FStar_UInt32.uint_to_t Prims.int_one))
  
let clear : 'Aa . 'Aa vector -> 'Aa vector =
  fun vec  ->
    Vec
      ((FStar_UInt32.uint_to_t Prims.int_zero),
        (match vec with | Vec (sz,cap,vs) -> cap),
        (match vec with | Vec (sz,cap,vs) -> vs))
  


let assign : 'Aa . 'Aa vector -> uint32_t -> 'Aa -> unit =
  fun vec  ->
    fun i1  ->
      fun v1  ->
        let hh0 = FStar_HyperStack_ST.get ()  in
        (let uu____1299 =
           LowStar_Monotonic_Buffer.msub
             (match vec with | Vec (sz,cap,vs) -> vs) i1 ()
            in
         let h1 = FStar_HyperStack_ST.get ()  in
         LowStar_Monotonic_Buffer.upd' uu____1299
           (FStar_UInt32.uint_to_t Prims.int_zero) v1);
        (let hh1 = FStar_HyperStack_ST.get ()  in ())
  
let (resize_ratio : uint32_t) = FStar_UInt32.uint_to_t (Prims.of_int (2)) 
let (new_capacity : uint32_t -> uint32_t) =
  fun cap  ->
    if FStar_UInt32.gte cap (FStar_UInt32.div max_uint32 resize_ratio)
    then max_uint32
    else FStar_UInt32.mul cap resize_ratio
  
let insert : 'Aa . 'Aa vector -> 'Aa -> 'Aa vector =
  fun vec  ->
    fun v1  ->
      let sz = match vec with | Vec (sz,cap,vs) -> sz  in
      let cap = match vec with | Vec (sz1,cap,vs) -> cap  in
      let vs = match vec with | Vec (sz1,cap1,vs) -> vs  in
      if sz = cap
      then
        let ncap = new_capacity cap  in
        let nvs = LowStar_Monotonic_Buffer.mmalloc () v1 ncap  in
        (LowStar_Monotonic_Buffer.blit vs
           (FStar_UInt32.uint_to_t Prims.int_zero) nvs
           (FStar_UInt32.uint_to_t Prims.int_zero) sz;
         (let h1 = FStar_HyperStack_ST.get ()  in
          LowStar_Monotonic_Buffer.upd' nvs sz v1);
         LowStar_Monotonic_Buffer.free vs;
         Vec
           ((FStar_UInt32.add sz (FStar_UInt32.uint_to_t Prims.int_one)),
             ncap, nvs))
      else
        ((let h1 = FStar_HyperStack_ST.get ()  in
          LowStar_Monotonic_Buffer.upd' vs sz v1);
         Vec
           ((FStar_UInt32.add sz (FStar_UInt32.uint_to_t Prims.int_one)),
             cap, vs))
  
let flush : 'Aa . 'Aa vector -> 'Aa -> uint32_t -> 'Aa vector =
  fun vec  ->
    fun ia  ->
      fun i1  ->
        let fsz =
          FStar_UInt32.sub (match vec with | Vec (sz,cap,vs) -> sz) i1  in
        let asz =
          if (match vec with | Vec (sz,cap,vs) -> sz) = i1
          then FStar_UInt32.uint_to_t Prims.int_one
          else fsz  in
        let vs = match vec with | Vec (sz,cap,vs) -> vs  in
        let fvs = LowStar_Monotonic_Buffer.mmalloc () ia asz  in
        LowStar_Monotonic_Buffer.blit vs i1 fvs
          (FStar_UInt32.uint_to_t Prims.int_zero) fsz;
        LowStar_Monotonic_Buffer.free vs;
        Vec (fsz, asz, fvs)
  
let shrink : 'Aa . 'Aa vector -> uint32_t -> 'Aa vector =
  fun vec  ->
    fun new_size  ->
      Vec
        (new_size, (match vec with | Vec (sz,cap,vs) -> cap),
          (match vec with | Vec (sz,cap,vs) -> vs))
  

let rec fold_left_buffer :
  'Aa 'Ab .
    uint32_t ->
      'Aa LowStar_Buffer.buffer -> ('Ab -> 'Aa -> 'Ab) -> 'Ab -> 'Ab
  =
  fun len  ->
    fun buf1  ->
      fun f  ->
        fun ib  ->
          if len = (FStar_UInt32.uint_to_t Prims.int_zero)
          then ib
          else
            (let uu____2348 =
               LowStar_Monotonic_Buffer.msub buf1
                 (FStar_UInt32.uint_to_t Prims.int_one) ()
                in
             let uu____2409 =
               let uu____2410 =
                 LowStar_Monotonic_Buffer.index buf1
                   (FStar_UInt32.uint_to_t Prims.int_zero)
                  in
               f ib uu____2410  in
             fold_left_buffer
               (FStar_UInt32.sub len (FStar_UInt32.uint_to_t Prims.int_one))
               uu____2348 f uu____2409)
  
let fold_left : 'Aa 'Ab . 'Aa vector -> ('Ab -> 'Aa -> 'Ab) -> 'Ab -> 'Ab =
  fun vec  ->
    fun f  ->
      fun ib  ->
        let uu____2514 =
          LowStar_Monotonic_Buffer.msub
            (match vec with | Vec (sz,cap,vs) -> vs)
            (FStar_UInt32.uint_to_t Prims.int_zero) ()
           in
        fold_left_buffer (match vec with | Vec (sz,cap,vs) -> sz) uu____2514
          f ib
  
type ('Aa,'Aseq,'Ai,'Aj,'Ap) forall_seq = unit
type ('Aa,'Ah,'Abuf,'Ai,'Aj,'Ap) forall_buffer = unit
type ('Aa,'Ah,'Avec,'Ai,'Aj,'Ap) forall_ = unit
type ('Aa,'Ah,'Avec,'Ap) forall_all = unit
type ('Aa,'Aseq,'Ai,'Aj,'Ap) forall2_seq = unit
type ('Aa,'Ah,'Abuf,'Ai,'Aj,'Ap) forall2_buffer = unit
type ('Aa,'Ah,'Avec,'Ai,'Aj,'Ap) forall2 = unit
type ('Aa,'Ah,'Avec,'Ap) forall2_all = unit









