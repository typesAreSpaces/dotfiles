open Prims
type 'Aa array = 'Aa FStar_Seq_Base.seq FStar_ST.ref


type ('Aa,'Ah,'As) contains =
  ('Aa FStar_Seq_Base.seq,unit,unit,unit) FStar_Monotonic_Heap.contains
type ('Aa,'Aarr,'Ah) unused_in =
  ('Aa FStar_Seq_Base.seq,unit,unit,unit) FStar_Monotonic_Heap.unused_in



let op_At_Bar : 'Aa . 'Aa array -> 'Aa array -> 'Aa array =
  fun s1  ->
    fun s2  ->
      let s1' = FStar_Ref.op_Bang s1  in
      let s2' = FStar_Ref.op_Bang s2  in
      FStar_ST.alloc (FStar_Seq_Base.append s1' s2')
  
type ('Aa,'As,'Ah0,'Ax,'Ah1) create_post = unit
let of_seq : 'Aa . 'Aa FStar_Seq_Base.seq -> 'Aa array =
  fun s  -> FStar_ST.alloc s 
let to_seq : 'Aa . 'Aa array -> 'Aa FStar_Seq_Base.seq =
  fun s  -> FStar_Ref.op_Bang s 
let of_list : 'Aa . 'Aa Prims.list -> 'Aa array =
  fun l  -> of_seq (FStar_Seq_Properties.of_list l) 
let create : 'Aa . Prims.nat -> 'Aa -> 'Aa array =
  fun n  -> fun init1  -> FStar_ST.alloc (FStar_Seq_Base.create n init1) 
let index : 'Aa . 'Aa array -> Prims.nat -> 'Aa =
  fun x  -> fun n  -> let s = to_seq x  in FStar_Seq_Base.index s n 
let upd : 'Aa . 'Aa array -> Prims.nat -> 'Aa -> unit =
  fun x  ->
    fun n  ->
      fun v  ->
        let s = FStar_Ref.op_Bang x  in
        let s' = FStar_Seq_Base.upd s n v  in FStar_Ref.op_Colon_Equals x s'
  
let length : 'Aa . 'Aa array -> Prims.nat =
  fun x  -> let s = FStar_Ref.op_Bang x  in FStar_Seq_Base.length s 
let op :
  'Aa .
    ('Aa FStar_Seq_Base.seq -> 'Aa FStar_Seq_Base.seq) -> 'Aa array -> unit
  =
  fun f  ->
    fun x  ->
      let s = FStar_Ref.op_Bang x  in
      let s' = f s  in FStar_Ref.op_Colon_Equals x s'
  
let swap : 'Aa . 'Aa array -> Prims.nat -> Prims.nat -> unit =
  fun x  ->
    fun i  ->
      fun j  ->
        let tmpi = index x i  in
        let tmpj = index x j  in upd x j tmpi; upd x i tmpj
  
let rec copy_aux : 'Aa . 'Aa array -> 'Aa array -> Prims.nat -> unit =
  fun s  ->
    fun cpy  ->
      fun ctr  ->
        let uu____672 = let uu____674 = length cpy  in uu____674 - ctr  in
        match uu____672 with
        | _676 when _676 = Prims.int_zero -> ()
        | uu____677 ->
            ((let uu____680 = index s ctr  in upd cpy ctr uu____680);
             copy_aux s cpy (ctr + Prims.int_one))
  
let copy : 'Aa . 'Aa array -> 'Aa array =
  fun s  ->
    let cpy =
      let uu____712 = length s  in
      let uu____713 = index s Prims.int_zero  in create uu____712 uu____713
       in
    copy_aux s cpy Prims.int_zero; cpy
  
let rec blit_aux :
  'Aa .
    'Aa array ->
      Prims.nat -> 'Aa array -> Prims.nat -> Prims.nat -> Prims.nat -> unit
  =
  fun s  ->
    fun s_idx  ->
      fun t  ->
        fun t_idx  ->
          fun len  ->
            fun ctr  ->
              match len - ctr with
              | _788 when _788 = Prims.int_zero -> ()
              | uu____789 ->
                  ((let uu____792 = index s (s_idx + ctr)  in
                    upd t (t_idx + ctr) uu____792);
                   blit_aux s s_idx t t_idx len (ctr + Prims.int_one))
  
let blit :
  'Aa . 'Aa array -> Prims.nat -> 'Aa array -> Prims.nat -> Prims.nat -> unit
  =
  fun s  ->
    fun s_idx  ->
      fun t  ->
        fun t_idx  -> fun len  -> blit_aux s s_idx t t_idx len Prims.int_zero
  
let sub : 'Aa . 'Aa array -> Prims.nat -> Prims.nat -> 'Aa array =
  fun s  ->
    fun idx  ->
      fun len  ->
        let h0 = FStar_ST.get ()  in
        let t =
          let uu____902 = index s Prims.int_zero  in create len uu____902  in
        blit s idx t Prims.int_zero len; (let h1 = FStar_ST.get ()  in t)
  