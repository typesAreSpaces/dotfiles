open Prims
type loc_aux =
  | LocBuffer of unit * Obj.t FStar_Buffer.buffer 
let (uu___is_LocBuffer : loc_aux -> Prims.bool) = fun projectee  -> true 
type 'Aprojectee __proj__LocBuffer__item__t = Obj.t
let (__proj__LocBuffer__item__b : loc_aux -> Obj.t FStar_Buffer.buffer) =
  fun projectee  -> match projectee with | LocBuffer (t,b) -> b 
type ('Al,'Ar,'An) loc_aux_in_addr = Obj.t
type ('Ar,'An) aloc = loc_aux
type ('Aa,'As,'Ab) loc_aux_includes_buffer = Obj.t
type ('As1,'As2) loc_aux_includes = Obj.t





type ('Al,'At,'Ap) loc_aux_disjoint_buffer = Obj.t
type ('Al1,'Al2) loc_aux_disjoint = Obj.t




type ('Al,'Ah1,'Ah2) loc_aux_preserved = Obj.t
let (cls : (unit,unit) aloc FStar_ModifiesGen.cls) =
  FStar_ModifiesGen.Cls ((), (), (), (), (), (), (), (), (), ()) 
type loc = ((unit,unit) aloc,unit) FStar_ModifiesGen.loc
let (loc_none : loc) = FStar_ModifiesGen.loc_none cls 













type ('As1,'As2) loc_includes =
  ((unit,unit) aloc,unit,unit,unit) FStar_ModifiesGen.loc_includes














type ('As1,'As2) loc_disjoint =
  ((unit,unit) aloc,unit,unit,unit) FStar_ModifiesGen.loc_disjoint










type ('As,'Ah1,'Ah2) modifies =
  ((unit,unit) aloc,unit,unit,unit,unit) FStar_ModifiesGen.modifies




let (address_liveness_insensitive_locs : loc) =
  FStar_ModifiesGen.address_liveness_insensitive_locs cls 
let (region_liveness_insensitive_locs : loc) =
  FStar_ModifiesGen.region_liveness_insensitive_locs cls 


































type ('Ah,'Ara) does_not_contain_addr =
  (unit,unit) FStar_ModifiesGen.does_not_contain_addr






type ('Auu____2707,'Auu____2708) cloc_aloc = (unit,unit) aloc
let (cloc_cls : (unit,unit) cloc_aloc FStar_ModifiesGen.cls) = cls 
let (cloc_of_loc : loc -> ((unit,unit) cloc_aloc,unit) FStar_ModifiesGen.loc)
  = fun l  -> l 
let (loc_of_cloc : ((unit,unit) cloc_aloc,unit) FStar_ModifiesGen.loc -> loc)
  = fun l  -> l 








