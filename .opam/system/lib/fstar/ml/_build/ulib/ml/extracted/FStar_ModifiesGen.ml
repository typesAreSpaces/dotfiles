open Prims
type aloc_t = unit
type 'Aaloc cls =
  | Cls of unit * unit * unit * unit * unit * unit * unit * unit * unit *
  unit 
let uu___is_Cls : 'Aaloc . 'Aaloc cls -> Prims.bool = fun projectee  -> true 
type ('Aaloc,'Aprojectee,'Ar,'Aa,'Auu____465,'Auu____466) __proj__Cls__item__aloc_includes =
  Obj.t


type ('Aaloc,'Aprojectee,'Ar,'Aa,'Ax1,'Ax2) __proj__Cls__item__aloc_disjoint =
  Obj.t


type ('Aaloc,'Aprojectee,'Ar,'Aa,'Auu____967,'Auu____968,'Auu____969) __proj__Cls__item__aloc_preserved =
  Obj.t



type ('Aal,'Ac) aloc =
  | ALoc of unit * Prims.nat * 'Aal FStar_Pervasives_Native.option 
let uu___is_ALoc : 'Aal . 'Aal cls -> ('Aal,unit) aloc -> Prims.bool =
  fun c  -> fun projectee  -> true 

let __proj__ALoc__item__addr :
  'Aal . 'Aal cls -> ('Aal,unit) aloc -> Prims.nat =
  fun c  ->
    fun projectee  -> match projectee with | ALoc (region,addr,loc) -> addr
  
let __proj__ALoc__item__loc :
  'Aal . 'Aal cls -> ('Aal,unit) aloc -> 'Aal FStar_Pervasives_Native.option
  =
  fun c  ->
    fun projectee  -> match projectee with | ALoc (region,addr,loc) -> loc
  

type ('Aa,'Ab) i_restricted_g_t = unit
type 'Aregions addrs_dom = unit
type ('Aregions,'Aregion_liveness_tags,'Ar) non_live_addrs_codom = unit
type ('Aregions,'Aregion_liveness_tags,'Anon_live_addrs,'Ar) live_addrs_codom =
  unit
type ('Aal,'Ac) loc' =
  | Loc of unit * unit * unit * unit * unit 
let uu___is_Loc : 'Aal . 'Aal cls -> ('Aal,unit) loc' -> Prims.bool =
  fun c  -> fun projectee  -> true 





type ('Aaloc,'Ac) loc = ('Aaloc,unit) loc'


let loc_none : 'Aa . 'Aa cls -> ('Aa,unit) loc =
  fun c  -> Loc ((), (), (), (), ()) 








type ('At,'At','Ap,'Af1,'Af2) fun_set_equal = unit

type ('Aal,'Ac,'As1,'As2) loc_equal = Obj.t















type ('Aal,'Ac,'Ab0,'Ab) aloc_includes = unit
type ('Aal,'Ac,'As,'Ab) loc_aux_includes_buffer = unit
type ('Aal,'Ac,'As1,'As2) loc_aux_includes = unit











type ('Aal,'Ac,'As1,'As2) loc_includes = unit
















type ('Aal,'Ac,'Ab1,'Ab2) aloc_disjoint = Obj.t

type ('Aal,'Ac,'Al1,'Al2) loc_aux_disjoint = unit





type ('Aal,'Ac,'Al1,'Al2) loc_disjoint_region_liveness_tags = unit
type ('Aal,'Ac,'Al1,'Al2) loc_disjoint_addrs = unit
type ('Aal,'Ac,'Al1,'Al2) loc_disjoint_aux = unit
type ('Aal,'Ac,'Al1,'Al2) loc_disjoint' = unit
type ('Aaloc,'Ac,'As1,'As2) loc_disjoint = unit















let address_liveness_insensitive_locs : 'Aal . 'Aal cls -> ('Aal,unit) loc =
  fun c  -> Loc ((), (), (), (), ()) 


let region_liveness_insensitive_locs : 'Aal . 'Aal cls -> ('Aal,unit) loc =
  fun c  -> Loc ((), (), (), (), ()) 




type ('Aal,'Ac,'As,'Ah1,'Ah2) modifies_preserves_livenesses = unit


type ('Aal,'Ac,'As,'Ah1,'Ah2) modifies_preserves_mreferences = unit

type ('Aal,'Ac,'As,'Ah1,'Ah2) modifies_preserves_alocs = unit

type ('Aal,'Ac,'As,'Ah1,'Ah2) modifies_preserves_regions = unit
type ('Aal,'Ac,'As,'Ah1,'Ah2) modifies_preserves_not_unused_in = unit

type ('Aal,'Ac,'As,'Ah1,'Ah2) modifies' = unit
type ('Aaloc,'Ac,'As,'Ah1,'Ah2) modifies = unit












































type ('Ah,'Ara) does_not_contain_addr' = unit
type ('Ah,'Ara) does_not_contain_addr = unit



















type ('Aal,'Ar,'An) cls_union_aloc =
  | ALOC_FALSE of 'Aal 
  | ALOC_TRUE of 'Aal 
let uu___is_ALOC_FALSE :
  'Aal . unit -> Prims.nat -> ('Aal,unit,unit) cls_union_aloc -> Prims.bool =
  fun r  ->
    fun n  ->
      fun projectee  ->
        match projectee with | ALOC_FALSE _0 -> true | uu____4522 -> false
  
let __proj__ALOC_FALSE__item___0 :
  'Aal . unit -> Prims.nat -> ('Aal,unit,unit) cls_union_aloc -> 'Aal =
  fun r  ->
    fun n  -> fun projectee  -> match projectee with | ALOC_FALSE _0 -> _0
  
let uu___is_ALOC_TRUE :
  'Aal . unit -> Prims.nat -> ('Aal,unit,unit) cls_union_aloc -> Prims.bool =
  fun r  ->
    fun n  ->
      fun projectee  ->
        match projectee with | ALOC_TRUE _0 -> true | uu____4666 -> false
  
let __proj__ALOC_TRUE__item___0 :
  'Aal . unit -> Prims.nat -> ('Aal,unit,unit) cls_union_aloc -> 'Aal =
  fun r  ->
    fun n  -> fun projectee  -> match projectee with | ALOC_TRUE _0 -> _0
  
let bool_of_cls_union_aloc :
  'Aal . unit -> Prims.nat -> ('Aal,unit,unit) cls_union_aloc -> Prims.bool =
  fun r  ->
    fun n  ->
      fun l  ->
        match l with
        | ALOC_FALSE uu____4811 -> false
        | ALOC_TRUE uu____4813 -> true
  
let aloc_of_cls_union_aloc :
  'Aal . unit -> Prims.nat -> ('Aal,unit,unit) cls_union_aloc -> 'Aal =
  fun r  ->
    fun n  -> fun l  -> match l with | ALOC_FALSE x -> x | ALOC_TRUE x -> x
  
let make_cls_union_aloc :
  'Aal .
    Prims.bool ->
      unit -> Prims.nat -> 'Aal -> ('Aal,unit,unit) cls_union_aloc
  =
  fun b  ->
    fun r  -> fun n  -> fun l  -> if b then ALOC_TRUE l else ALOC_FALSE l
  
type ('Aal,'Ac,'Ar,'Aa,'Alarger,'Asmaller) cls_union_aloc_includes = unit
type ('Aal,'Ac,'Ar,'Aa,'Alarger,'Asmaller) cls_union_aloc_disjoint = unit
type ('Aal,'Ac,'Ar,'Aa,'Ax,'Ah,'Ah') cls_union_aloc_preserved = Obj.t
type ('Auu____5142,'Auu____5143,'Auu____5144) aloc_union =
  ('Auu____5142,unit,unit) cls_union_aloc
let cls_union :
  'Aal . (Prims.bool -> 'Aal cls) -> ('Aal,unit,unit) aloc_union cls =
  fun c  -> Cls ((), (), (), (), (), (), (), (), (), ()) 



























type ('Aal,'Ar,'An) raise_aloc = 'Aal FStar_Universe.raise_t
let raise_cls : 'Aal . 'Aal cls -> ('Aal,unit,unit) raise_aloc cls =
  fun c  -> Cls ((), (), (), (), (), (), (), (), (), ()) 
let downgrade_aloc :
  'Aal .
    'Aal cls -> (('Aal,unit,unit) raise_aloc,unit) aloc -> ('Aal,unit) aloc
  =
  fun c  ->
    fun a  ->
      let uu____6353 = a  in
      match uu____6353 with
      | ALoc (region,addr,x) ->
          ALoc
            ((), addr,
              (if FStar_Pervasives_Native.uu___is_None x
               then FStar_Pervasives_Native.None
               else
                 FStar_Pervasives_Native.Some
                   (FStar_Universe.downgrade_val
                      (FStar_Pervasives_Native.__proj__Some__item__v x))))
  
let upgrade_aloc :
  'Aal .
    'Aal cls -> ('Aal,unit) aloc -> (('Aal,unit,unit) raise_aloc,unit) aloc
  =
  fun c  ->
    fun a  ->
      let uu____6504 = a  in
      match uu____6504 with
      | ALoc (region,addr,x) ->
          ALoc
            ((), addr,
              (if FStar_Pervasives_Native.uu___is_None x
               then FStar_Pervasives_Native.None
               else
                 FStar_Pervasives_Native.Some
                   (FStar_Universe.raise_val
                      (FStar_Pervasives_Native.__proj__Some__item__v x))))
  



let raise_loc :
  'Aal .
    'Aal cls -> ('Aal,unit) loc -> (('Aal,unit,unit) raise_aloc,unit) loc
  =
  fun c  ->
    fun l  ->
      let uu____6649 = l  in
      match uu____6649 with
      | Loc (regions,region_liveness_tags,non_live_addrs,live_addrs,aux) ->
          Loc ((), (), (), (), ())
  








let lower_loc :
  'Aal .
    'Aal cls -> (('Aal,unit,unit) raise_aloc,unit) loc -> ('Aal,unit) loc
  =
  fun c  ->
    fun l  ->
      let uu____6815 = l  in
      match uu____6815 with
      | Loc (regions,region_liveness_tags,non_live_addrs,live_addrs,aux) ->
          Loc ((), (), (), (), ())
  





