open Prims
type 'An fin = Prims.int
type ('An,'Aa) vect = 'Aa Prims.list
type ('An,'Aa) seqn = 'Aa FStar_Seq_Base.seq
type ('Aa,'As) in_ = Prims.nat
let rec find :
  'Aa .
    'Aa FStar_Seq_Base.seq ->
      ('Aa -> Prims.bool) ->
        Prims.nat -> Prims.nat FStar_Pervasives_Native.option
  =
  fun s  ->
    fun p  ->
      fun i  ->
        if p (FStar_Seq_Base.index s i)
        then FStar_Pervasives_Native.Some i
        else
          if (i + Prims.int_one) < (FStar_Seq_Base.length s)
          then find s p (i + Prims.int_one)
          else FStar_Pervasives_Native.None
  
let rec (pigeonhole :
  Prims.nat ->
    unit fin FStar_Seq_Base.seq ->
      ((unit fin,unit) in_ * (unit fin,unit) in_))
  =
  fun a1  ->
    fun a2  ->
      (fun n  ->
         fun s  ->
           if n = Prims.int_zero
           then Obj.magic (Obj.repr (failwith "unreachable"))
           else
             Obj.magic
               (Obj.repr
                  (if n = Prims.int_one
                   then (Prims.int_zero, Prims.int_one)
                   else
                     (let k0 = FStar_Seq_Base.index s Prims.int_zero  in
                      match find s (fun k  -> k = k0) Prims.int_one with
                      | FStar_Pervasives_Native.Some i -> (Prims.int_zero, i)
                      | FStar_Pervasives_Native.None  ->
                          let reduced_s =
                            FStar_Seq_Base.init n
                              (fun i  ->
                                 let k =
                                   FStar_Seq_Base.index s (i + Prims.int_one)
                                    in
                                 if k < k0 then k else k - Prims.int_one)
                             in
                          let uu____255 =
                            pigeonhole (n - Prims.int_one) reduced_s  in
                          (match uu____255 with
                           | (i1,i2) ->
                               ((i1 + Prims.int_one), (i2 + Prims.int_one)))))))
        a1 a2
  