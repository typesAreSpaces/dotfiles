open Prims
type ('Akey,'Avalue) t =
  {
  mappings: ('Akey,'Avalue) FStar_FunctionalExtensionality.restricted_t ;
  domain: 'Akey FStar_Set.set }
let __proj__Mkt__item__mappings :
  'Akey 'Avalue .
    ('Akey,'Avalue) t ->
      ('Akey,'Avalue) FStar_FunctionalExtensionality.restricted_t
  =
  fun projectee  -> match projectee with | { mappings; domain;_} -> mappings 
let __proj__Mkt__item__domain :
  'Akey 'Avalue . ('Akey,'Avalue) t -> 'Akey FStar_Set.set =
  fun projectee  -> match projectee with | { mappings; domain;_} -> domain 
let sel : 'Akey 'Avalue . ('Akey,'Avalue) t -> 'Akey -> 'Avalue =
  fun m  -> fun k  -> m.mappings k 
let upd :
  'Akey 'Avalue . ('Akey,'Avalue) t -> 'Akey -> 'Avalue -> ('Akey,'Avalue) t
  =
  fun m  ->
    fun k  ->
      fun v  ->
        {
          mappings =
            (FStar_FunctionalExtensionality.on_domain
               (fun x  -> if x = k then v else m.mappings x));
          domain = (FStar_Set.union m.domain (FStar_Set.singleton k))
        }
  
let const : 'Akey 'Avalue . 'Avalue -> ('Akey,'Avalue) t =
  fun v  ->
    {
      mappings =
        (FStar_FunctionalExtensionality.on_domain (fun uu____257  -> v));
      domain = (FStar_Set.complement (FStar_Set.empty ()))
    }
  
let domain : 'Akey 'Avalue . ('Akey,'Avalue) t -> 'Akey FStar_Set.set =
  fun m  -> m.domain 
let contains : 'Akey 'Avalue . ('Akey,'Avalue) t -> 'Akey -> Prims.bool =
  fun m  -> fun k  -> FStar_Set.mem k m.domain 
let concat :
  'Akey 'Avalue . ('Akey,'Avalue) t -> ('Akey,'Avalue) t -> ('Akey,'Avalue) t
  =
  fun m1  ->
    fun m2  ->
      {
        mappings =
          (FStar_FunctionalExtensionality.on_domain
             (fun x  ->
                if FStar_Set.mem x m2.domain
                then m2.mappings x
                else m1.mappings x));
        domain = (FStar_Set.union m1.domain m2.domain)
      }
  
let map_val :
  'Auu____403 'Auu____404 .
    ('Auu____403 -> 'Auu____404) ->
      unit -> (Obj.t,'Auu____403) t -> (Obj.t,'Auu____404) t
  =
  fun f  ->
    fun key  ->
      fun m  ->
        {
          mappings =
            (FStar_FunctionalExtensionality.on_domain
               (fun x  -> f (m.mappings x)));
          domain = (m.domain)
        }
  
let restrict :
  'Akey 'Avalue .
    'Akey FStar_Set.set -> ('Akey,'Avalue) t -> ('Akey,'Avalue) t
  =
  fun s  ->
    fun m  ->
      { mappings = (m.mappings); domain = (FStar_Set.intersect s m.domain) }
  
let const_on :
  'Akey 'Avalue . 'Akey FStar_Set.set -> 'Avalue -> ('Akey,'Avalue) t =
  fun dom  -> fun v  -> restrict dom (const v) 
type ('Akey,'Avalue,'Am1,'Am2) disjoint_dom = unit
type ('Akey,'Avalue,'Am,'Adom) has_dom = unit















type ('Akey,'Avalue,'Am1,'Am2) equal = unit


