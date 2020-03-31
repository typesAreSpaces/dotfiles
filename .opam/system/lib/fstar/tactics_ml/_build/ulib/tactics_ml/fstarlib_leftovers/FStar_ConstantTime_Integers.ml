open Prims
type sw = FStar_Integers.signed_width
type ('Asl,'Al,'As) secret_int = Obj.t





let (promote : unit -> unit -> sw -> Obj.t -> unit -> Obj.t) =
  fun sl  ->
    fun l0  ->
      fun s  ->
        fun x  ->
          fun l1  -> FStar_IFC.join () () () () (FStar_IFC.hide () () () x)
  
let (addition : unit -> unit -> sw -> Obj.t -> Obj.t -> Obj.t) =
  fun sl  ->
    fun l  ->
      fun s  ->
        fun x  ->
          fun y  ->
            FStar_IFC.join () () () ()
              (FStar_IFC.map () () x
                 (fun a  ->
                    FStar_IFC.join () () () ()
                      (FStar_IFC.map () () y
                         (fun b  ->
                            FStar_IFC.hide () () ()
                              (FStar_Integers.op_Plus s a b)))))
  
let (addition_mod :
  unit -> unit -> FStar_Integers.signed_width -> Obj.t -> Obj.t -> Obj.t) =
  fun sl  ->
    fun l  ->
      fun sw  ->
        fun x  ->
          fun y  ->
            FStar_IFC.join () () () ()
              (FStar_IFC.map () () x
                 (fun a  ->
                    FStar_IFC.join () () () ()
                      (FStar_IFC.map () () y
                         (fun b  ->
                            FStar_IFC.hide () () ()
                              (FStar_Integers.op_Plus_Percent sw a b)))))
  
type qual =
  | Secret of unit * unit * sw 
  | Public of FStar_Integers.signed_width 
let (uu___is_Secret : qual -> Prims.bool) =
  fun projectee  ->
    match projectee with | Secret (sl,l,sw) -> true | uu____537 -> false
  


let (__proj__Secret__item__sw : qual -> sw) =
  fun projectee  -> match projectee with | Secret (sl,l,sw) -> sw 
let (uu___is_Public : qual -> Prims.bool) =
  fun projectee  ->
    match projectee with | Public sw -> true | uu____576 -> false
  
let (__proj__Public__item__sw : qual -> FStar_Integers.signed_width) =
  fun projectee  -> match projectee with | Public sw -> sw 
let (sw_qual : qual -> FStar_Integers.signed_width) =
  fun uu___0_597  ->
    match uu___0_597 with
    | Secret (uu____598,uu____599,sw) -> sw
    | Public sw -> sw
  

type 'Aq t = Obj.t
let (q2s : qual -> FStar_Integers.signed_width) =
  fun q  ->
    match q with | Secret (uu____627,uu____628,s) -> s | Public s -> s
  

let (as_secret : qual -> Obj.t -> Obj.t) = fun q  -> fun x  -> x 
let (as_public : qual -> Obj.t -> Obj.t) = fun q  -> fun x  -> x 
let (op_Plus : qual -> Obj.t -> Obj.t -> Obj.t) =
  fun q  ->
    fun x  ->
      fun y  ->
        match q with
        | Public s ->
            FStar_Integers.op_Plus
              (match q with
               | Secret (uu____796,uu____797,sw) -> sw
               | Public sw -> sw) x y
        | Secret (uu____800,l,s) ->
            addition () ()
              (match q with
               | Secret (uu____809,uu____810,sw) -> sw
               | Public sw -> sw) x y
  
let (op_Plus_Percent : qual -> Obj.t -> Obj.t -> Obj.t) =
  fun q  ->
    fun x  ->
      fun y  ->
        match q with
        | Public s ->
            FStar_Integers.op_Plus_Percent
              (match q with
               | Secret (uu____878,uu____879,sw) -> sw
               | Public sw -> sw) x y
        | Secret (uu____882,l,s) ->
            addition_mod () ()
              (match q with
               | Secret (uu____891,uu____892,sw) -> sw
               | Public sw -> sw) x y
  
let (test : Prims.int -> Prims.int -> Prims.int) = fun x  -> fun y  -> x + y 



let (test2 : Obj.t -> Obj.t -> Obj.t) =
  fun x  ->
    fun y  ->
      addition_mod () () (FStar_Integers.Unsigned FStar_Integers.W32) x y
  
let (test3 : Obj.t -> Obj.t -> Obj.t) =
  fun x  ->
    fun y  ->
      addition_mod () () (FStar_Integers.Unsigned FStar_Integers.W32) x
        (promote () () (FStar_Integers.Unsigned FStar_Integers.W32) y ())
  
let (test4 : Obj.t -> Obj.t -> Obj.t) =
  fun x  ->
    fun y  ->
      addition () () (FStar_Integers.Unsigned FStar_Integers.W32)
        (promote () () (FStar_Integers.Unsigned FStar_Integers.W32) x ()) y
  


type s_uint32 = Obj.t
let (test5 : Obj.t -> Obj.t -> Obj.t) =
  fun x  ->
    fun y  ->
      addition_mod () () (FStar_Integers.Unsigned FStar_Integers.W32) x y
  
let (test6 : Obj.t -> Obj.t -> Obj.t) =
  fun x  ->
    fun y  -> addition () () (FStar_Integers.Unsigned FStar_Integers.W32) x y
  