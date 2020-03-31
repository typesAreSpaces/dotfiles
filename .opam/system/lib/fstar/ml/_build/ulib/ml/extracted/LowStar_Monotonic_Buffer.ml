open Prims
type 'Aa srel = unit
type ('Aa,'Alen,'Arel,'Ai,'Aj,'Asub_rel) compatible_subseq_preorder = unit
type ('Aa,'Alen,'Apre,'As1,'As2) srel_to_lsrel = 'Apre
type ('Aa,'Alen,'Arel,'Ai,'Aj,'Asub_rel) compatible_sub_preorder = unit


type ('Aa,'Arrel,'Arel) mbuffer =
  | Null 
  | Buffer of FStar_UInt32.t *
  (('Aa,unit) FStar_Seq_Properties.lseq,('Aa,unit,'Arrel,unit,unit)
                                          srel_to_lsrel)
  FStar_HyperStack_ST.mreference * FStar_UInt32.t * unit 
let uu___is_Null :
  'Aa 'Arrel 'Arel . ('Aa,'Arrel,'Arel) mbuffer -> Prims.bool =
  fun projectee  -> match projectee with | Null  -> true | uu____590 -> false 
let uu___is_Buffer :
  'Aa 'Arrel 'Arel . ('Aa,'Arrel,'Arel) mbuffer -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Buffer (max_length,content,idx,length1) -> true
    | uu____821 -> false
  
let __proj__Buffer__item__max_length :
  'Aa 'Arrel 'Arel . ('Aa,'Arrel,'Arel) mbuffer -> FStar_UInt32.t =
  fun projectee  ->
    match projectee with
    | Buffer (max_length,content,idx,length1) -> max_length
  
let __proj__Buffer__item__content :
  'Aa 'Arrel 'Arel .
    ('Aa,'Arrel,'Arel) mbuffer ->
      (('Aa,unit) FStar_Seq_Properties.lseq,('Aa,unit,'Arrel,unit,unit)
                                              srel_to_lsrel)
        FStar_HyperStack_ST.mreference
  =
  fun projectee  ->
    match projectee with | Buffer (max_length,content,idx,length1) -> content
  
let __proj__Buffer__item__idx :
  'Aa 'Arrel 'Arel . ('Aa,'Arrel,'Arel) mbuffer -> FStar_UInt32.t =
  fun projectee  ->
    match projectee with | Buffer (max_length,content,idx,length1) -> idx
  


let mnull :
  'Auu____1546 'Auu____1547 'Auu____1548 .
    unit -> ('Auu____1546,'Auu____1547,'Auu____1548) mbuffer
  = fun uu____1585  -> Null 

type ('Auu____1651,'Auu____1652,'Auu____1653,'Ab,'Ah) unused_in = Obj.t
type ('At,'Arrel,'Arel,'Ab) buffer_compatible = Obj.t
type ('Auu____1769,'Arrel,'Arel,'Ah,'Ab) live = Obj.t


















type ('Aa,'Arrel,'Arel,'Ab,'Ai,'Alen,'Asub_rel) compatible_sub = unit












type ubuffer_ =
  {
  b_max_length: Prims.nat ;
  b_offset: Prims.nat ;
  b_length: Prims.nat ;
  b_is_mm: Prims.bool }
let (__proj__Mkubuffer___item__b_max_length : ubuffer_ -> Prims.nat) =
  fun projectee  ->
    match projectee with
    | { b_max_length; b_offset; b_length; b_is_mm;_} -> b_max_length
  
let (__proj__Mkubuffer___item__b_offset : ubuffer_ -> Prims.nat) =
  fun projectee  ->
    match projectee with
    | { b_max_length; b_offset; b_length; b_is_mm;_} -> b_offset
  
let (__proj__Mkubuffer___item__b_length : ubuffer_ -> Prims.nat) =
  fun projectee  ->
    match projectee with
    | { b_max_length; b_offset; b_length; b_is_mm;_} -> b_length
  
let (__proj__Mkubuffer___item__b_is_mm : ubuffer_ -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { b_max_length; b_offset; b_length; b_is_mm;_} -> b_is_mm
  
type ('Aregion,'Aaddr) ubuffer' = ubuffer_
type ('Aregion,'Aaddr) ubuffer = unit

type ('Ar,'Aa,'Ab,'Ah,'Ah') ubuffer_preserved' = unit
type ('Ar,'Aa,'Ab,'Ah,'Ah') ubuffer_preserved = unit











type ('Alarger,'Asmaller) ubuffer_includes' = unit
type ('Ar1,'Ar2,'Aa1,'Aa2,'Alarger,'Asmaller) ubuffer_includes0 = unit
type ('Ar,'Aa,'Alarger,'Asmaller) ubuffer_includes = unit


type ('Ax1,'Ax2) ubuffer_disjoint' = Obj.t
type ('Ar1,'Ar2,'Aa1,'Aa2,'Ab1,'Ab2) ubuffer_disjoint0 = unit
type ('Ar,'Aa,'Ab1,'Ab2) ubuffer_disjoint = unit



type ('Ah1,'Ah2) modifies_0_preserves_mreferences = unit
type ('Ah1,'Ah2) modifies_0_preserves_regions = unit
type ('Ah1,'Ah2) modifies_0_preserves_not_unused_in = unit
type ('Ah1,'Ah2) modifies_0' = unit
type ('Ah1,'Ah2) modifies_0 = unit




type ('Aa,'Arrel,'Arel,'Ab,'Ah1,'Ah2) modifies_1_preserves_mreferences = unit
type ('Aa,'Arrel,'Arel,'Ab,'Ah1,'Ah2) modifies_1_preserves_ubuffers = unit
type ('Aa,'Arrel,'Arel,'Ab,'Afrom,'Ato_3350,'Ah1,'Ah2) modifies_1_from_to_preserves_ubuffers =
  unit
type ('Aa,'Arrel,'Arel,'Ab,'Ah1,'Ah2) modifies_1_preserves_livenesses = unit
type ('Aa,'Arrel,'Arel,'Ab,'Ah1,'Ah2) modifies_1' = unit
type ('Aa,'Arrel,'Arel,'Ab,'Ah1,'Ah2) modifies_1 = unit
type ('Aa,'Arrel,'Arel,'Ab,'Afrom,'Ato_3684,'Ah1,'Ah2) modifies_1_from_to =
  Obj.t











type ('Aa,'Arrel,'Arel,'Ab,'Ah1,'Ah2) modifies_addr_of_preserves_not_unused_in =
  unit
type ('Aa,'Arrel,'Arel,'Ab,'Ah1,'Ah2) modifies_addr_of' = unit
type ('Aa,'Arrel,'Arel,'Ab,'Ah1,'Ah2) modifies_addr_of = unit



let (cls : (unit,unit) ubuffer FStar_ModifiesGen.cls) =
  FStar_ModifiesGen.Cls ((), (), (), (), (), (), (), (), (), ()) 
type loc = (unit,unit) FStar_ModifiesGen.loc

let (loc_none : loc) = FStar_ModifiesGen.loc_none cls 



























type ('As1,'As2) loc_includes =
  (unit,unit,unit,unit) FStar_ModifiesGen.loc_includes






























type ('As1,'As2) loc_disjoint =
  (unit,unit,unit,unit) FStar_ModifiesGen.loc_disjoint












type buf_t =
  (unit,unit,unit,(Obj.t,Obj.t,Obj.t) mbuffer) FStar_Pervasives.dtuple4
let buf : 'Aa 'Arrel 'Arel . ('Aa,'Arrel,'Arel) mbuffer -> buf_t =
  fun b  -> FStar_Pervasives.Mkdtuple4 ((), (), (), (Obj.magic b)) 
type ('Ah,'Al) all_live = Obj.t
type 'Al all_disjoint = Obj.t

type 'Al loc_pairwise_disjoint = Obj.t
type ('As,'Ah1,'Ah2) modifies =
  (unit,unit,unit,unit,unit) FStar_ModifiesGen.modifies






let (address_liveness_insensitive_locs : loc) =
  FStar_ModifiesGen.address_liveness_insensitive_locs cls 
let (region_liveness_insensitive_locs : loc) =
  FStar_ModifiesGen.region_liveness_insensitive_locs cls 



































type ('Ah,'Ara) does_not_contain_addr =
  (unit,unit) FStar_ModifiesGen.does_not_contain_addr








type ('Al,'Ah) loc_in = (unit,unit) loc_includes
type ('Al,'Ah) loc_not_in = (unit,unit) loc_includes












type ('Al,'Ah,'Ah') fresh_loc = unit





type ('Aa1,'Aa2,'Arrel1,'Arel1,'Arrel2,'Arel2,'Ab1,'Ab2) disjoint =
  (unit,unit) loc_disjoint
type ('Aa1,'Aa2,'Arrel1,'Arel1,'Arrel2,'Arel2,'Ab1,'Ab2) includes = unit



type ('Aa,'Arrel,'Arel) mpointer = ('Aa,'Arrel,'Arel) mbuffer
type ('Aa,'Arrel,'Arel) mpointer_or_null = ('Aa,'Arrel,'Arel) mbuffer


let is_null :
  'Auu____28336 'Auu____28337 'Auu____28338 .
    ('Auu____28336,'Auu____28337,'Auu____28338) mbuffer -> Prims.bool
  = fun b  -> uu___is_Null b 
let msub :
  'Aa 'Arrel 'Arel 'Asub_rel .
    ('Aa,'Arrel,'Arel) mbuffer ->
      FStar_UInt32.t -> unit -> ('Aa,'Arrel,'Asub_rel) mbuffer
  =
  fun b  ->
    fun i  ->
      fun len  ->
        match b with
        | Null  -> Null
        | Buffer (max_len,content,i0,len0) ->
            Buffer (max_len, content, (FStar_UInt32.add i0 i), ())
  
let moffset :
  'Aa 'Arrel 'Arel 'Asub_rel .
    ('Aa,'Arrel,'Arel) mbuffer ->
      FStar_UInt32.t -> ('Aa,'Arrel,'Asub_rel) mbuffer
  =
  fun b  ->
    fun i  ->
      match b with
      | Null  -> Null
      | Buffer (max_len,content,i0,len) ->
          Buffer (max_len, content, (FStar_UInt32.add i0 i), ())
  
let index :
  'Auu____28938 'Auu____28939 'Auu____28940 .
    ('Auu____28938,'Auu____28939,'Auu____28940) mbuffer ->
      FStar_UInt32.t -> 'Auu____28938
  =
  fun b  ->
    fun i  ->
      let s = FStar_HyperStack_ST.op_Bang (__proj__Buffer__item__content b)
         in
      FStar_Seq_Base.index s
        ((FStar_UInt32.v (__proj__Buffer__item__idx b)) + (FStar_UInt32.v i))
  





let upd' :
  'Auu____29199 'Auu____29200 'Auu____29201 .
    ('Auu____29199,'Auu____29200,'Auu____29201) mbuffer ->
      FStar_UInt32.t -> 'Auu____29199 -> unit
  =
  fun b  ->
    fun i  ->
      fun v1  ->
        let h = FStar_HyperStack_ST.get ()  in
        let uu____29294 = b  in
        match uu____29294 with
        | Buffer (max_length,content,idx,len) ->
            let s0 = FStar_HyperStack_ST.op_Bang content  in
            let sb0 =
              FStar_Seq_Base.slice s0 (FStar_UInt32.v idx)
                (FStar_UInt32.v max_length)
               in
            let s_upd = FStar_Seq_Base.upd sb0 (FStar_UInt32.v i) v1  in
            let sf =
              FStar_Seq_Properties.replace_subseq s0 (FStar_UInt32.v idx)
                (FStar_UInt32.v max_length) s_upd
               in
            FStar_HyperStack_ST.op_Colon_Equals content sf
  
let upd :
  'Aa 'Arrel 'Arel .
    ('Aa,'Arrel,'Arel) mbuffer -> FStar_UInt32.t -> 'Aa -> unit
  =
  fun b  ->
    fun i  -> fun v1  -> let h = FStar_HyperStack_ST.get ()  in upd' b i v1
  
type ('Aa,'Arrel,'Arel,'Ab) recallable = unit
type ('Auu____29786,'Auu____29787,'Auu____29788,'Ab) region_lifetime_buf =
  unit
type ('Aa,'Arrel,'Arel) rrel_rel_always_compatible = unit



let recall :
  'Auu____29882 'Auu____29883 'Auu____29884 .
    ('Auu____29882,'Auu____29883,'Auu____29884) mbuffer -> unit
  =
  fun b  ->
    if uu___is_Null b
    then ()
    else FStar_HyperStack_ST.recall (__proj__Buffer__item__content b)
  
type 'Aa spred = unit
type ('Aa,'Ap,'Arel) stable_on = unit
type ('Aa,'Arrel,'Arel,'Ab,'Ap,'Ah) spred_as_mempred = unit
type ('Auu____30190,'Arrel,'Arel,'Ab,'Ap) witnessed = Obj.t

let witness_p : 'Aa 'Arrel 'Arel . ('Aa,'Arrel,'Arel) mbuffer -> unit -> unit
  =
  fun b  ->
    fun p  ->
      match b with
      | Null  -> ()
      | Buffer (uu____30334,content,uu____30336,uu____30337) ->
          FStar_HyperStack_ST.witness_p content ()
  
let recall_p :
  'Auu____30518 'Auu____30519 'Auu____30520 .
    ('Auu____30518,'Auu____30519,'Auu____30520) mbuffer -> unit -> unit
  =
  fun b  ->
    fun p  ->
      match b with
      | Null  -> ()
      | Buffer (uu____30608,content,uu____30610,uu____30611) ->
          FStar_HyperStack_ST.recall_p content ()
  

let witnessed_functorial_st :
  'Aa 'Arrel 'Arel1 'Arel2 .
    ('Aa,'Arrel,'Arel1) mbuffer ->
      ('Aa,'Arrel,'Arel2) mbuffer ->
        FStar_UInt32.t -> FStar_UInt32.t -> unit -> unit -> unit
  = fun b1  -> fun b2  -> fun i  -> fun len  -> fun s1  -> fun s2  -> () 
type ('Aa,'Arrel,'Arel,'Ab) freeable = unit
let free :
  'Auu____31417 'Auu____31418 'Auu____31419 .
    ('Auu____31417,'Auu____31418,'Auu____31419) mbuffer -> unit
  = fun b  -> FStar_HyperStack_ST.rfree (__proj__Buffer__item__content b) 



type ('Aa,'Arrel,'Arel,'Alen) lmbuffer = ('Aa,'Arrel,'Arel) mbuffer
type ('Aa,'Arrel,'Arel,'Ab,'Ah0,'Ah1,'As) alloc_post_mem_common = unit
type ('Aa,'Arrel,'Arel,'Alen,'Ar) lmbuffer_or_null =
  ('Aa,'Arrel,'Arel) mbuffer
type ('Aa,'Arrel,'Arel,'Ab,'Ah0,'Ah1,'As) alloc_partial_post_mem_common =
  unit
type ('Ar,'Alen) malloc_pre = unit
let alloc_heap_common :
  'Aa 'Arrel .
    unit ->
      FStar_UInt32.t ->
        'Aa FStar_Seq_Base.seq -> Prims.bool -> ('Aa,'Arrel,'Arrel) mbuffer
  =
  fun r  ->
    fun len  ->
      fun s  ->
        fun mm  ->
          let content =
            if mm
            then FStar_HyperStack_ST.ralloc_mm () s
            else FStar_HyperStack_ST.ralloc () s  in
          let b =
            Buffer
              (len, content, (FStar_UInt32.uint_to_t Prims.int_zero), ())
             in
          b
  
let mgcmalloc :
  'Auu____32324 'Auu____32325 .
    unit ->
      'Auu____32324 ->
        FStar_UInt32.t -> ('Auu____32324,'Auu____32325,'Auu____32325) mbuffer
  =
  fun r  ->
    fun init1  ->
      fun len  ->
        alloc_heap_common () len
          (FStar_Seq_Base.create (FStar_UInt32.v len) init1) false
  
let read_sub_buffer :
  'Aa 'Arrel 'Arel .
    ('Aa,'Arrel,'Arel) mbuffer ->
      FStar_UInt32.t -> FStar_UInt32.t -> 'Aa FStar_Seq_Base.seq
  =
  fun b  ->
    fun idx  ->
      fun len  ->
        let s = FStar_HyperStack_ST.op_Bang (__proj__Buffer__item__content b)
           in
        let s1 =
          FStar_Seq_Base.slice s
            (FStar_UInt32.v (__proj__Buffer__item__idx b))
            (FStar_UInt32.v (__proj__Buffer__item__max_length b))
           in
        FStar_Seq_Base.slice s1 (FStar_UInt32.v idx)
          ((FStar_UInt32.v idx) + (FStar_UInt32.v len))
  
let mgcmalloc_and_blit :
  'Auu____32605 'Auu____32606 .
    unit ->
      unit ->
        unit ->
          ('Auu____32605,Obj.t,Obj.t) mbuffer ->
            FStar_UInt32.t ->
              FStar_UInt32.t ->
                ('Auu____32605,'Auu____32606,'Auu____32606) mbuffer
  =
  fun r  ->
    fun uu____32708  ->
      fun uu____32709  ->
        fun src  ->
          fun id_src  ->
            fun len  ->
              let uu____32749 = read_sub_buffer src id_src len  in
              alloc_heap_common () len uu____32749 false
  
let mgcmalloc_partial :
  'Aa 'Arrel . unit -> 'Aa -> FStar_UInt32.t -> ('Aa,'Arrel,'Arrel) mbuffer =
  fun r  -> fun init1  -> fun len  -> mgcmalloc () init1 len 
let mmalloc :
  'Auu____32842 'Auu____32843 .
    unit ->
      'Auu____32842 ->
        FStar_UInt32.t -> ('Auu____32842,'Auu____32843,'Auu____32843) mbuffer
  =
  fun r  ->
    fun init1  ->
      fun len  ->
        alloc_heap_common () len
          (FStar_Seq_Base.create (FStar_UInt32.v len) init1) true
  
let mmalloc_and_blit :
  'Auu____32926 'Auu____32927 .
    unit ->
      unit ->
        unit ->
          ('Auu____32926,Obj.t,Obj.t) mbuffer ->
            FStar_UInt32.t ->
              FStar_UInt32.t ->
                ('Auu____32926,'Auu____32927,'Auu____32927) mbuffer
  =
  fun r  ->
    fun uu____33029  ->
      fun uu____33030  ->
        fun src  ->
          fun id_src  ->
            fun len  ->
              let uu____33070 = read_sub_buffer src id_src len  in
              alloc_heap_common () len uu____33070 true
  
let mmalloc_partial :
  'Aa 'Arrel . unit -> 'Aa -> FStar_UInt32.t -> ('Aa,'Arrel,'Arrel) mbuffer =
  fun r  -> fun init1  -> fun len  -> mmalloc () init1 len 
let (alloca_pre : FStar_UInt32.t -> Prims.bool) =
  fun len  -> (FStar_UInt32.v len) > Prims.int_zero 
let malloca :
  'Aa 'Arrel . 'Aa -> FStar_UInt32.t -> ('Aa,'Arrel,'Arrel) mbuffer =
  fun init1  ->
    fun len  ->
      let content =
        FStar_HyperStack_ST.salloc
          (FStar_Seq_Base.create (FStar_UInt32.v len) init1)
         in
      Buffer (len, content, (FStar_UInt32.uint_to_t Prims.int_zero), ())
  
let malloca_and_blit :
  'Aa 'Arrel 'Auu____33409 'Auu____33410 .
    ('Aa,'Auu____33409,'Auu____33410) mbuffer ->
      FStar_UInt32.t -> FStar_UInt32.t -> ('Aa,'Arrel,'Arrel) mbuffer
  =
  fun src  ->
    fun id_src  ->
      fun len  ->
        let content =
          let uu____33628 = read_sub_buffer src id_src len  in
          FStar_HyperStack_ST.salloc uu____33628  in
        Buffer (len, content, (FStar_UInt32.uint_to_t Prims.int_zero), ())
  
type ('Aa,'Ainit) alloca_of_list_pre = unit
let malloca_of_list :
  'Aa 'Arrel . 'Aa Prims.list -> ('Aa,'Arrel,'Arrel) mbuffer =
  fun init1  ->
    let len = FStar_UInt32.uint_to_t (FStar_List_Tot_Base.length init1)  in
    let s = FStar_Seq_Properties.seq_of_list init1  in
    let content = FStar_HyperStack_ST.salloc s  in
    Buffer (len, content, (FStar_UInt32.uint_to_t Prims.int_zero), ())
  
type ('Aa,'Ar,'Ainit) gcmalloc_of_list_pre = unit
let mgcmalloc_of_list :
  'Aa 'Arrel . unit -> 'Aa Prims.list -> ('Aa,'Arrel,'Arrel) mbuffer =
  fun r  ->
    fun init1  ->
      let len = FStar_UInt32.uint_to_t (FStar_List_Tot_Base.length init1)  in
      let s = FStar_Seq_Properties.seq_of_list init1  in
      let content = FStar_HyperStack_ST.ralloc () s  in
      Buffer (len, content, (FStar_UInt32.uint_to_t Prims.int_zero), ())
  
let mgcmalloc_of_list_partial :
  'Aa 'Arrel . unit -> 'Aa Prims.list -> ('Aa,'Arrel,'Arrel) mbuffer =
  fun r  -> fun init1  -> mgcmalloc_of_list () init1 
type ('Ah,'Ad,'Alen) alloc_drgn_pre = unit
let mmalloc_drgn :
  'Aa 'Arrel .
    FStar_HyperStack_ST.drgn ->
      'Aa -> FStar_UInt32.t -> ('Aa,'Arrel,'Arrel) mbuffer
  =
  fun d  ->
    fun init1  ->
      fun len  ->
        let content =
          FStar_HyperStack_ST.ralloc_drgn d
            (FStar_Seq_Base.create (FStar_UInt32.v len) init1)
           in
        Buffer (len, content, (FStar_UInt32.uint_to_t Prims.int_zero), ())
  
let mmalloc_drgn_mm :
  'Aa 'Arrel .
    FStar_HyperStack_ST.drgn ->
      'Aa -> FStar_UInt32.t -> ('Aa,'Arrel,'Arrel) mbuffer
  =
  fun d  ->
    fun init1  ->
      fun len  ->
        let content =
          FStar_HyperStack_ST.ralloc_drgn_mm d
            (FStar_Seq_Base.create (FStar_UInt32.v len) init1)
           in
        Buffer (len, content, (FStar_UInt32.uint_to_t Prims.int_zero), ())
  
let mmalloc_drgn_and_blit :
  'Aa 'Arrel 'Auu____34807 'Auu____34808 .
    FStar_HyperStack_ST.drgn ->
      ('Aa,'Auu____34807,'Auu____34808) mbuffer ->
        FStar_UInt32.t -> FStar_UInt32.t -> ('Aa,'Arrel,'Arrel) mbuffer
  =
  fun d  ->
    fun src  ->
      fun id_src  ->
        fun len  ->
          let content =
            let uu____35031 = read_sub_buffer src id_src len  in
            FStar_HyperStack_ST.ralloc_drgn d uu____35031  in
          Buffer (len, content, (FStar_UInt32.uint_to_t Prims.int_zero), ())
  
let blit :
  'Aa 'Arrel1 'Arrel2 'Arel1 'Arel2 .
    ('Aa,'Arrel1,'Arel1) mbuffer ->
      FStar_UInt32.t ->
        ('Aa,'Arrel2,'Arel2) mbuffer ->
          FStar_UInt32.t -> FStar_UInt32.t -> unit
  =
  fun src  ->
    fun idx_src  ->
      fun dst  ->
        fun idx_dst  ->
          fun len  ->
            match (src, dst) with
            | (Buffer
               (uu____35421,uu____35422,uu____35423,uu____35424),Buffer
               (uu____35425,uu____35426,uu____35427,uu____35428)) ->
                if len = (FStar_UInt32.uint_to_t Prims.int_zero)
                then ()
                else
                  (let h = FStar_HyperStack_ST.get ()  in
                   let uu____35684 = src  in
                   match uu____35684 with
                   | Buffer (max_length1,content1,idx1,length1) ->
                       let uu____35814 = dst  in
                       (match uu____35814 with
                        | Buffer (max_length2,content2,idx2,length2) ->
                            let s_full1 =
                              FStar_HyperStack_ST.op_Bang content1  in
                            let s_full2 =
                              FStar_HyperStack_ST.op_Bang content2  in
                            let s1 =
                              FStar_Seq_Base.slice s_full1
                                (FStar_UInt32.v idx1)
                                (FStar_UInt32.v max_length1)
                               in
                            let s2 =
                              FStar_Seq_Base.slice s_full2
                                (FStar_UInt32.v idx2)
                                (FStar_UInt32.v max_length2)
                               in
                            let s_sub_src =
                              FStar_Seq_Base.slice s1
                                (FStar_UInt32.v idx_src)
                                ((FStar_UInt32.v idx_src) +
                                   (FStar_UInt32.v len))
                               in
                            let s2' =
                              FStar_Seq_Properties.replace_subseq s2
                                (FStar_UInt32.v idx_dst)
                                ((FStar_UInt32.v idx_dst) +
                                   (FStar_UInt32.v len)) s_sub_src
                               in
                            let s_full2' =
                              FStar_Seq_Properties.replace_subseq s_full2
                                (FStar_UInt32.v idx2)
                                (FStar_UInt32.v max_length2) s2'
                               in
                            (FStar_HyperStack_ST.op_Colon_Equals content2
                               s_full2';
                             (let h1 = FStar_HyperStack_ST.get ()  in ()))))
            | (uu____36185,uu____36186) -> ()
  
let fill' :
  'At 'Arrel 'Arel .
    ('At,'Arrel,'Arel) mbuffer -> 'At -> FStar_UInt32.t -> unit
  =
  fun b  ->
    fun z  ->
      fun len  ->
        if len = (FStar_UInt32.uint_to_t Prims.int_zero)
        then ()
        else
          (let h = FStar_HyperStack_ST.get ()  in
           let uu____36463 = b  in
           match uu____36463 with
           | Buffer (max_length,content,idx,length1) ->
               let s_full = FStar_HyperStack_ST.op_Bang content  in
               let s =
                 FStar_Seq_Base.slice s_full (FStar_UInt32.v idx)
                   (FStar_UInt32.v max_length)
                  in
               let s_src = FStar_Seq_Base.create (FStar_UInt32.v len) z  in
               let s' =
                 FStar_Seq_Properties.replace_subseq s Prims.int_zero
                   (FStar_UInt32.v len) s_src
                  in
               let s_full' =
                 FStar_Seq_Properties.replace_subseq s_full
                   (FStar_UInt32.v idx)
                   ((FStar_UInt32.v idx) + (FStar_UInt32.v len)) s_src
                  in
               (FStar_HyperStack_ST.op_Colon_Equals content s_full';
                (let h' = FStar_HyperStack_ST.get ()  in ())))
  
let fill :
  'At 'Arrel 'Arel .
    ('At,'Arrel,'Arel) mbuffer -> 'At -> FStar_UInt32.t -> unit
  = fun b  -> fun z  -> fun len  -> fill' b z len 
type ('Aregion,'Aaddr) abuffer' = (unit,unit) ubuffer'
type ('Aregion,'Aaddr) abuffer = unit
let coerce : 'At2 'At1 . 'At1 -> 'At2 =
  fun a1  -> (fun x1  -> Obj.magic x1) a1 
let (cloc_cls : unit FStar_ModifiesGen.cls) = coerce cls 
let (cloc_of_loc : loc -> (unit,unit) FStar_ModifiesGen.loc) =
  fun l  -> coerce l 
let (loc_of_cloc : (unit,unit) FStar_ModifiesGen.loc -> loc) =
  fun l  -> coerce l 








