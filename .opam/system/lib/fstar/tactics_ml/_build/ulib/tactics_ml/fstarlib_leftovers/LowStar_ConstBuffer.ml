open Prims


type ('Aq,'Aa) qbuf_cases = Obj.t
type ('Aq,'Aa) q_preorder = Obj.t
type 'Aa qbuf = (unit,Obj.t) Prims.dtuple2

type ('a,'Ac,'Auu____85,'Auu____86) qbuf_pre = Obj.t
let qbuf_mbuf :
  'a . 'a qbuf -> ('a,Obj.t,Obj.t) LowStar_Monotonic_Buffer.mbuffer =
  fun a1  -> (fun c  -> Obj.magic (FStar_Pervasives.dsnd c)) a1 
type 'Aa const_buffer = 'Aa qbuf
let as_qbuf : 'a . 'a const_buffer -> 'a qbuf = fun c  -> c 


type ('a,'Ah,'Ac) live =
  ('a,Obj.t,Obj.t,unit,unit) LowStar_Monotonic_Buffer.live



let of_buffer : 'a . 'a LowStar_Buffer.buffer -> 'a const_buffer =
  fun b  -> Prims.Mkdtuple2 ((), (Obj.magic b)) 
let of_ibuffer : 'a . 'a LowStar_ImmutableBuffer.ibuffer -> 'a const_buffer =
  fun b  -> Prims.Mkdtuple2 ((), (Obj.magic b)) 
let of_qbuf :
  'Auu____441 .
    unit ->
      ('Auu____441,Obj.t,Obj.t) LowStar_Monotonic_Buffer.mbuffer ->
        'Auu____441 const_buffer
  = fun q  -> fun b  -> Prims.Mkdtuple2 ((), (Obj.magic b)) 
let index : 'a . 'a const_buffer -> FStar_UInt32.t -> 'a =
  fun c  ->
    fun i  -> let x = qbuf_mbuf c  in LowStar_Monotonic_Buffer.index x i
  

type ('a,'Ai,'Alen,'Acsub,'Ac) const_sub_buffer = unit
let sub :
  'Aa . 'Aa const_buffer -> FStar_UInt32.t -> unit -> 'Aa const_buffer =
  fun c  ->
    fun i  ->
      fun len  ->
        let uu____775 = c  in
        match uu____775 with
        | Prims.Mkdtuple2 (q,x) ->
            let x1 = Obj.magic x  in
            let y = LowStar_Monotonic_Buffer.msub x1 i ()  in
            Prims.Mkdtuple2 ((), (Obj.magic y))
  
let cast :
  'a . 'a const_buffer -> ('a,Obj.t,Obj.t) LowStar_Monotonic_Buffer.mbuffer =
  fun c  -> qbuf_mbuf c 
let to_buffer : 'a . 'a const_buffer -> 'a LowStar_Buffer.buffer =
  fun a2  -> (fun c  -> Obj.magic (qbuf_mbuf c)) a2 
let to_ibuffer : 'a . 'a const_buffer -> 'a LowStar_ImmutableBuffer.ibuffer =
  fun a3  -> (fun c  -> Obj.magic (qbuf_mbuf c)) a3 
let (test :
  FStar_UInt32.t LowStar_Buffer.buffer ->
    FStar_UInt32.t LowStar_ImmutableBuffer.ibuffer -> FStar_UInt32.t)
  =
  fun x  ->
    fun y  ->
      let c1 = of_buffer x  in
      let c2 = of_ibuffer y  in
      (let h = FStar_HyperStack_ST.get ()  in
       LowStar_Monotonic_Buffer.upd' x
         (FStar_UInt32.uint_to_t Prims.int_zero)
         (FStar_UInt32.uint_to_t Prims.int_one));
      (let a = index c1 (FStar_UInt32.uint_to_t Prims.int_zero)  in
       let a' = index c2 (FStar_UInt32.uint_to_t Prims.int_zero)  in
       let c3 = sub c2 (FStar_UInt32.uint_to_t Prims.int_one) ()  in
       let a'' = index c3 (FStar_UInt32.uint_to_t Prims.int_zero)  in
       FStar_UInt32.add (FStar_UInt32.add a a') a'')
  