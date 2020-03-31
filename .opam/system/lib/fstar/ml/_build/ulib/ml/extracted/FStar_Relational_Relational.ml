open Prims
type ('Aa,'Ab) rel =
  | R of 'Aa * 'Ab 
let uu___is_R : 'Aa 'Ab . ('Aa,'Ab) rel -> Prims.bool =
  fun projectee  -> true 
let __proj__R__item__l : 'Aa 'Ab . ('Aa,'Ab) rel -> 'Aa =
  fun projectee  -> match projectee with | R (l,r) -> l 
let __proj__R__item__r : 'Aa 'Ab . ('Aa,'Ab) rel -> 'Ab =
  fun projectee  -> match projectee with | R (l,r) -> r 
type 'At double = ('At,'At) rel
type 'At eq = 'At double
let twice : 'Auu____127 . 'Auu____127 -> ('Auu____127,'Auu____127) rel =
  fun x  -> R (x, x) 
let (tu : (unit,unit) rel) = twice () 
let rel_map1T : 'a 'b . ('a -> 'b) -> 'a double -> 'b double =
  fun f  ->
    fun uu____176  -> match uu____176 with | R (x1,x2) -> R ((f x1), (f x2))
  
let rel_map2Teq :
  'Aa 'Ab 'Ac . ('Aa -> 'Ab -> 'Ac) -> 'Aa double -> 'Ab double -> 'Ac double
  =
  fun f  ->
    fun uu____236  ->
      fun uu____237  ->
        match (uu____236, uu____237) with
        | (R (x1,x2),R (y1,y2)) -> R ((f x1 y1), (f x2 y2))
  
let rel_map2T :
  'a 'b 'c . ('a -> 'b -> 'c) -> 'a double -> 'b double -> 'c double =
  fun f  ->
    fun uu____319  ->
      fun uu____320  ->
        match (uu____319, uu____320) with
        | (R (x1,x2),R (y1,y2)) -> R ((f x1 y1), (f x2 y2))
  

let rel_map3T :
  'a 'b 'c 'd .
    ('a -> 'b -> 'c -> 'd) ->
      'a double -> 'b double -> 'c double -> 'd double
  =
  fun f  ->
    fun uu____440  ->
      fun uu____441  ->
        fun uu____442  ->
          match (uu____440, uu____441, uu____442) with
          | (R (x1,x2),R (y1,y2),R (z1,z2)) -> R ((f x1 y1 z1), (f x2 y2 z2))
  

let (op_Hat_Plus : Prims.int double -> Prims.int double -> Prims.int double)
  = rel_map2T (fun x  -> fun y  -> x + y) 
let (op_Hat_Minus : Prims.int double -> Prims.int double -> Prims.int double)
  = rel_map2T (fun x  -> fun y  -> x - y) 
let (op_Hat_Star : Prims.int double -> Prims.int double -> Prims.int double)
  = rel_map2T (fun x  -> fun y  -> x * y) 
let (op_Hat_Slash :
  Prims.int double -> Prims.nonzero double -> Prims.int double) =
  rel_map2T (fun x  -> fun y  -> x / y) 
let tl_rel : 'Aa . 'Aa Prims.list double -> 'Aa Prims.list double =
  fun uu____648  ->
    match uu____648 with | R (uu____653::xs,uu____655::ys) -> R (xs, ys)
  
let cons_rel :
  'Auu____686 'Auu____687 .
    ('Auu____686,'Auu____687) rel ->
      ('Auu____686 Prims.list,'Auu____687 Prims.list) rel ->
        ('Auu____686 Prims.list,'Auu____687 Prims.list) rel
  =
  fun uu____716  ->
    fun uu____717  ->
      match (uu____716, uu____717) with
      | (R (x,y),R (xs,ys)) -> R ((x :: xs), (y :: ys))
  
let pair_rel :
  'Auu____793 'Auu____794 'Auu____795 'Auu____796 .
    ('Auu____793,'Auu____794) rel ->
      ('Auu____795,'Auu____796) rel ->
        (('Auu____793 * 'Auu____795),('Auu____794 * 'Auu____796)) rel
  =
  fun uu____825  ->
    fun uu____826  ->
      match (uu____825, uu____826) with
      | (R (a,b),R (c,d)) -> R ((a, c), (b, d))
  
let triple_rel :
  'Auu____897 'Auu____898 'Auu____899 'Auu____900 'Auu____901 'Auu____902 .
    ('Auu____897,'Auu____898) rel ->
      ('Auu____899,'Auu____900) rel ->
        ('Auu____901,'Auu____902) rel ->
          (('Auu____897 * 'Auu____899 * 'Auu____901),('Auu____898 *
                                                       'Auu____900 *
                                                       'Auu____902))
            rel
  =
  fun uu____943  ->
    fun uu____944  ->
      fun uu____945  ->
        match (uu____943, uu____944, uu____945) with
        | (R (a,b),R (c,d),R (e,f)) -> R ((a, c, e), (b, d, f))
  
let fst_rel :
  'Auu____1009 'Auu____1010 .
    unit -> ('Auu____1009 * 'Auu____1010) double -> 'Auu____1009 double
  = fun uu____1022  -> rel_map1T FStar_Pervasives_Native.fst 
let snd_rel :
  'Auu____1036 'Auu____1037 .
    unit -> ('Auu____1036 * 'Auu____1037) double -> 'Auu____1037 double
  = fun uu____1049  -> rel_map1T FStar_Pervasives_Native.snd 
let (and_rel : Prims.bool double -> Prims.bool double -> Prims.bool double) =
  rel_map2T (fun x  -> fun y  -> x && y) 
let (or_rel : Prims.bool double -> Prims.bool double -> Prims.bool double) =
  rel_map2T (fun x  -> fun y  -> x || y) 
let (eq_rel : Prims.bool double -> Prims.bool double -> Prims.bool double) =
  rel_map2Teq (fun x  -> fun y  -> x = y) 
let (and_irel : (Prims.bool,Prims.bool) rel -> Prims.bool) =
  fun uu____1157  -> match uu____1157 with | R (a,b) -> a && b 
let (or_irel : (Prims.bool,Prims.bool) rel -> Prims.bool) =
  fun uu____1185  -> match uu____1185 with | R (a,b) -> a || b 
let eq_irel : 'At . ('At,'At) rel -> Prims.bool =
  fun x  -> match x with | R (a,b) -> a = b 
