open Prims
let rec fold :
  'Aa 'Ab .
    'Aa FStar_OrdSet.cmp ->
      ('Aa -> 'Ab -> 'Ab) -> ('Aa,unit) FStar_OrdSet.ordset -> 'Ab -> 'Ab
  =
  fun f  ->
    fun g  ->
      fun s  ->
        fun x  ->
          if s = (FStar_OrdSet.empty f)
          then x
          else
            (let uu____187 = FStar_OrdSet.choose f s  in
             match uu____187 with
             | FStar_Pervasives_Native.Some e ->
                 let a_rest = fold f g (FStar_OrdSet.remove f e s) x  in
                 g e a_rest)
  
let insert :
  'Aa .
    'Aa FStar_OrdSet.cmp ->
      'Aa -> ('Aa,unit) FStar_OrdSet.ordset -> ('Aa,unit) FStar_OrdSet.ordset
  =
  fun f  ->
    fun x  -> fun s  -> FStar_OrdSet.union f (FStar_OrdSet.singleton f x) s
  
let union' :
  'Aa .
    'Aa FStar_OrdSet.cmp ->
      ('Aa,unit) FStar_OrdSet.ordset ->
        ('Aa,unit) FStar_OrdSet.ordset -> ('Aa,unit) FStar_OrdSet.ordset
  =
  fun f  ->
    fun s1  -> fun s2  -> fold f (fun e  -> fun s  -> insert f e s) s1 s2
  

