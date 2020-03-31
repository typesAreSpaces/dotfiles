open Prims
let (is_in : unit -> FStar_Monotonic_HyperHeap.hmap -> Prims.bool) =
  fun r  -> fun h  -> FStar_Map.contains h () 

let (is_heap_color : Prims.int -> Prims.bool) = fun c  -> c <= Prims.int_zero 


type sid = unit





type 'Am map_invariant_predicate = unit
type 'Ah downward_closed_predicate = unit
type ('Atip,'Ah) tip_top_predicate = unit

type ('Ah,'An) rid_ctr_pred_predicate = unit
type 'Am map_invariant = unit
type 'Ah downward_closed = unit
type ('Atip,'Ah) tip_top = unit
type ('Ah,'An) rid_ctr_pred = unit
type ('Atip,'Ah) is_tip = unit
type ('Ah,'Actr,'Atip) is_wf_with_ctr_and_tip = unit
type mem' =
  | HS of Prims.int * FStar_Monotonic_HyperHeap.hmap * unit 
let (uu___is_HS : mem' -> Prims.bool) = fun projectee  -> true 
let (__proj__HS__item__rid_ctr : mem' -> Prims.int) =
  fun projectee  -> match projectee with | HS (rid_ctr,h,tip) -> rid_ctr 
let (__proj__HS__item__h : mem' -> FStar_Monotonic_HyperHeap.hmap) =
  fun projectee  -> match projectee with | HS (rid_ctr,h,tip) -> h 

let (mk_mem : Prims.int -> FStar_Monotonic_HyperHeap.hmap -> unit -> mem') =
  fun rid_ctr  -> fun h  -> fun tip  -> HS (rid_ctr, h, ()) 
let (get_hmap : mem' -> FStar_Monotonic_HyperHeap.hmap) =
  fun m  -> __proj__HS__item__h m 
let (get_rid_ctr : mem' -> Prims.int) = fun m  -> __proj__HS__item__rid_ctr m 


type mem = mem'








let (empty_mem : mem) =
  let empty_map =
    FStar_Map.restrict (FStar_Set.empty ())
      (FStar_Map.const FStar_Monotonic_Heap.emp)
     in
  let h = FStar_Map.upd empty_map () FStar_Monotonic_Heap.emp  in
  mk_mem Prims.int_one h () 

type 'Am poppable = unit
let remove_elt : 'Aa . 'Aa FStar_Set.set -> 'Aa -> 'Aa FStar_Set.set =
  fun s  ->
    fun x  ->
      FStar_Set.intersect s (FStar_Set.complement (FStar_Set.singleton x))
  
type ('Am0,'Am1) popped = unit
let (pop : mem -> mem) =
  fun m0  ->
    let uu____701 = ((get_hmap m0), (), (get_rid_ctr m0))  in
    match uu____701 with
    | (h0,tip0,rid_ctr0) ->
        let dom = remove_elt (FStar_Map.domain h0) ()  in
        let h1 = FStar_Map.restrict dom h0  in mk_mem rid_ctr0 h1 ()
  
type ('Aa,'Arel) mreference' =
  | MkRef of unit * ('Aa,'Arel) FStar_Monotonic_Heap.mref 
let uu___is_MkRef : 'Aa 'Arel . ('Aa,'Arel) mreference' -> Prims.bool =
  fun projectee  -> true 

let __proj__MkRef__item__ref :
  'Aa 'Arel .
    ('Aa,'Arel) mreference' -> ('Aa,'Arel) FStar_Monotonic_Heap.mref
  = fun projectee  -> match projectee with | MkRef (frame,ref) -> ref 
type ('Aa,'Arel) mreference = ('Aa,'Arel) mreference'

let mk_mreference :
  'Aa 'Arel .
    unit -> ('Aa,'Arel) FStar_Monotonic_Heap.mref -> ('Aa,'Arel) mreference
  = fun id1  -> fun r  -> MkRef ((), r) 
let as_ref :
  'Auu____1102 'Auu____1103 .
    ('Auu____1102,'Auu____1103) mreference ->
      ('Auu____1102,'Auu____1103) FStar_Monotonic_Heap.mref
  = fun x  -> __proj__MkRef__item__ref x 



type ('Aa,'Arel) mstackref = ('Aa,'Arel) mreference
type ('Aa,'Arel) mref = ('Aa,'Arel) mreference
type ('Aa,'Arel) mmmstackref = ('Aa,'Arel) mreference
type ('Aa,'Arel) mmmref = ('Aa,'Arel) mreference
type ('Ai,'Aa,'Arel) s_mref = ('Aa,'Arel) mreference
let (live_region : mem -> unit -> Prims.bool) =
  fun m  -> fun i  -> FStar_Map.contains (get_hmap m) () 



type ('Aa,'Arel,'Ar,'Am0,'Am1) fresh_ref = unit
type ('Ai,'Am0,'Am1) fresh_region = unit


let alloc :
  'Aa 'Arel .
    unit -> 'Aa -> Prims.bool -> mem -> (('Aa,'Arel) mreference * mem)
  =
  fun id1  ->
    fun init1  ->
      fun mm  ->
        fun m  ->
          let uu____2054 = ((get_hmap m), (get_rid_ctr m), ())  in
          match uu____2054 with
          | (h,rid_ctr,tip) ->
              let uu____2088 =
                FStar_Monotonic_Heap.alloc (FStar_Map.sel h ()) init1 mm  in
              (match uu____2088 with
               | (r,id_h) ->
                   let h1 = FStar_Map.upd h () id_h  in
                   ((mk_mreference () r), (mk_mem rid_ctr h1 ())))
  
let free : 'Aa 'Arel . ('Aa,'Arel) mreference -> mem -> mem =
  fun r  ->
    fun m  ->
      let uu____2248 = ((get_hmap m), (get_rid_ctr m), ())  in
      match uu____2248 with
      | (h,rid_ctr,tip) ->
          let i_h = FStar_Map.sel h ()  in
          let i_h1 = FStar_Monotonic_Heap.free_mm i_h (as_ref r)  in
          let h1 = FStar_Map.upd h () i_h1  in mk_mem rid_ctr h1 ()
  
let upd_tot : 'Aa 'Arel . mem -> ('Aa,'Arel) mreference -> 'Aa -> mem =
  fun m  ->
    fun r  ->
      fun v  ->
        let uu____2370 = ((get_hmap m), (get_rid_ctr m), ())  in
        match uu____2370 with
        | (h,rid_ctr,tip) ->
            let i_h = FStar_Map.sel h ()  in
            let i_h1 = FStar_Monotonic_Heap.upd_tot i_h (as_ref r) v  in
            let h1 = FStar_Map.upd h () i_h1  in mk_mem rid_ctr h1 ()
  
let sel_tot : 'Aa 'Arel . mem -> ('Aa,'Arel) mreference -> 'Aa =
  fun m  ->
    fun r  ->
      FStar_Monotonic_Heap.sel_tot (FStar_Map.sel (get_hmap m) ()) (as_ref r)
  
type ('Am0,'Am1) fresh_frame = unit
let (hs_push_frame : mem -> mem) =
  fun m  ->
    let uu____2729 = ((get_hmap m), (get_rid_ctr m), ())  in
    match uu____2729 with
    | (h,rid_ctr,tip) ->
        let h1 = FStar_Map.upd h () FStar_Monotonic_Heap.emp  in
        mk_mem (rid_ctr + Prims.int_one) h1 ()
  
let (new_eternal_region :
  mem -> unit -> Prims.int FStar_Pervasives_Native.option -> (unit * mem)) =
  fun m  ->
    fun parent  ->
      fun c  ->
        let uu____2807 = ((get_hmap m), (get_rid_ctr m), ())  in
        match uu____2807 with
        | (h,rid_ctr,tip) ->
            let h1 = FStar_Map.upd h () FStar_Monotonic_Heap.emp  in
            ((), (mk_mem (rid_ctr + Prims.int_one) h1 ()))
  
let (new_freeable_heap_region : mem -> unit -> (unit * mem)) =
  fun m  ->
    fun parent  ->
      let uu____2872 = ((get_hmap m), (get_rid_ctr m), ())  in
      match uu____2872 with
      | (h,rid_ctr,tip) ->
          let h1 = FStar_Map.upd h () FStar_Monotonic_Heap.emp  in
          ((), (mk_mem (rid_ctr + Prims.int_one) h1 ()))
  
let (free_heap_region : mem -> unit -> mem) =
  fun m0  ->
    fun r  ->
      let uu____2932 = ((get_hmap m0), (get_rid_ctr m0))  in
      match uu____2932 with
      | (h0,rid_ctr0) ->
          let dom = remove_elt (FStar_Map.domain h0) ()  in
          let h1 = FStar_Map.restrict dom h0  in
          mk_mem (get_rid_ctr m0) h1 ()
  




type ('As,'Am0,'Am1) modifies = unit
type ('As,'Am0,'Am1) modifies_transitively = unit
type 'Am0 heap_only = unit
let (top_frame : mem -> FStar_Monotonic_Heap.heap) =
  fun m  -> FStar_Map.sel (get_hmap m) () 


type ('Aid,'Ah0,'Ah1) modifies_one = unit
type ('Aid,'As,'Ah0,'Ah1) modifies_ref = unit
type some_ref =
  | Ref of unit * unit * (Obj.t,Obj.t) mreference 
let (uu___is_Ref : some_ref -> Prims.bool) = fun projectee  -> true 
type 'Aprojectee __proj__Ref__item__a = Obj.t
type ('Aprojectee,'Auu____3993,'Auu____3994) __proj__Ref__item__rel = Obj.t
let (__proj__Ref__item___2 : some_ref -> (Obj.t,Obj.t) mreference) =
  fun projectee  -> match projectee with | Ref (a,rel,_2) -> _2 
type some_refs = some_ref Prims.list
let rec (regions_of_some_refs : some_refs -> unit FStar_Set.set) =
  fun rs  ->
    match rs with
    | [] -> FStar_Set.empty ()
    | (Ref (uu____4109,uu____4110,r))::tl1 ->
        FStar_Set.union (FStar_Set.singleton ()) (regions_of_some_refs tl1)
  

type ('Ai,'Ars,'Ah0,'Ah1) modifies_some_refs = Obj.t
let (norm_steps : FStar_Pervasives.norm_step Prims.list) =
  [FStar_Pervasives.iota;
  FStar_Pervasives.zeta;
  FStar_Pervasives.delta;
  FStar_Pervasives.delta_only
    ["FStar.Monotonic.HyperStack.regions_of_some_refs";
    "FStar.Monotonic.HyperStack.refs_in_region";
    "FStar.Monotonic.HyperStack.modifies_some_refs"];
  FStar_Pervasives.primops] 
type ('Ars,'Ah0,'Ah1) mods = unit









type aref =
  | ARef of unit * FStar_Monotonic_Heap.aref 
let (uu___is_ARef : aref -> Prims.bool) = fun projectee  -> true 

let (__proj__ARef__item__aref_aref : aref -> FStar_Monotonic_Heap.aref) =
  fun projectee  ->
    match projectee with | ARef (aref_region,aref_aref) -> aref_aref
  
let (dummy_aref : aref) = ARef ((), FStar_Monotonic_Heap.dummy_aref) 

let aref_of :
  'Auu____4778 'Auu____4779 . ('Auu____4778,'Auu____4779) mreference -> aref
  = fun r  -> ARef ((), (FStar_Monotonic_Heap.aref_of (as_ref r))) 






type ('Aa,'Ah) aref_unused_in = unit


type ('Ah,'Aa,'Av,'Arel) aref_live_at = unit

let (reference_of : mem -> aref -> unit -> unit -> (Obj.t,Obj.t) mreference)
  =
  fun h  ->
    fun a  ->
      fun v  ->
        fun rel  ->
          MkRef
            ((),
              (FStar_Monotonic_Heap.ref_of
                 (FStar_Map.sel (__proj__HS__item__h h) ())
                 (__proj__ARef__item__aref_aref a) () ()))
  








