open Prims
let rec fold :
  'Ak 'Av 'At .
    'Ak FStar_OrdMap.cmp ->
      ('Ak -> 'Av -> 'At -> 'At) ->
        ('Ak,'Av,unit) FStar_OrdMap.ordmap -> 'At -> 'At
  =
  fun f  ->
    fun g  ->
      fun m  ->
        fun a  ->
          if (FStar_OrdMap.size f m) = Prims.int_zero
          then a
          else
            (let uu____165 = FStar_OrdMap.choose f m  in
             match uu____165 with
             | FStar_Pervasives_Native.Some (k,v) ->
                 fold f g (FStar_OrdMap.remove f k m) (g k v a))
  