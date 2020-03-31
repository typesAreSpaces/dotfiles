open Prims
type ('Aa,'Al) lseq = 'Aa FStar_Seq_Base.seq
type ('Aa,'As,'Aj) indexable = unit




let head : 'Aa . 'Aa FStar_Seq_Base.seq -> 'Aa =
  fun s  -> FStar_Seq_Base.index s Prims.int_zero 
let tail : 'Aa . 'Aa FStar_Seq_Base.seq -> 'Aa FStar_Seq_Base.seq =
  fun s  -> FStar_Seq_Base.slice s Prims.int_one (FStar_Seq_Base.length s) 


let last : 'Aa . 'Aa FStar_Seq_Base.seq -> 'Aa =
  fun s  ->
    FStar_Seq_Base.index s ((FStar_Seq_Base.length s) - Prims.int_one)
  
let cons : 'Aa . 'Aa -> 'Aa FStar_Seq_Base.seq -> 'Aa FStar_Seq_Base.seq =
  fun x  ->
    fun s  -> FStar_Seq_Base.append (FStar_Seq_Base.create Prims.int_one x) s
  

let split :
  'Aa .
    'Aa FStar_Seq_Base.seq ->
      Prims.nat -> ('Aa FStar_Seq_Base.seq * 'Aa FStar_Seq_Base.seq)
  =
  fun s  ->
    fun i  ->
      ((FStar_Seq_Base.slice s Prims.int_zero i),
        (FStar_Seq_Base.slice s i (FStar_Seq_Base.length s)))
  

let split_eq :
  'Aa .
    'Aa FStar_Seq_Base.seq ->
      Prims.nat -> ('Aa FStar_Seq_Base.seq * 'Aa FStar_Seq_Base.seq)
  = fun s  -> fun i  -> let x = split s i  in x 
let rec count : 'Aa . 'Aa -> 'Aa FStar_Seq_Base.seq -> Prims.nat =
  fun x  ->
    fun s  ->
      if (FStar_Seq_Base.length s) = Prims.int_zero
      then Prims.int_zero
      else
        if (head s) = x
        then Prims.int_one + (count x (tail s))
        else count x (tail s)
  
let mem : 'Aa . 'Aa -> 'Aa FStar_Seq_Base.seq -> Prims.bool =
  fun x  -> fun l  -> (count x l) > Prims.int_zero 

let rec index_mem : 'Aa . 'Aa -> 'Aa FStar_Seq_Base.seq -> Prims.nat =
  fun x  ->
    fun s  ->
      if (head s) = x
      then Prims.int_zero
      else Prims.int_one + (index_mem x (tail s))
  
let swap :
  'Aa .
    'Aa FStar_Seq_Base.seq ->
      Prims.nat -> Prims.nat -> 'Aa FStar_Seq_Base.seq
  =
  fun s  ->
    fun i  ->
      fun j  ->
        FStar_Seq_Base.upd
          (FStar_Seq_Base.upd s j (FStar_Seq_Base.index s i)) i
          (FStar_Seq_Base.index s j)
  






let rec sorted :
  'Aa . ('Aa -> 'Aa -> Prims.bool) -> 'Aa FStar_Seq_Base.seq -> Prims.bool =
  fun f  ->
    fun s  ->
      if (FStar_Seq_Base.length s) <= Prims.int_one
      then true
      else
        (let hd1 = head s  in
         (f hd1 (FStar_Seq_Base.index s Prims.int_one)) &&
           (sorted f (tail s)))
  






type ('Aa,'Af) total_order = unit
type 'Aa tot_ord = 'Aa -> 'Aa -> Prims.bool

let split_5 :
  'Aa .
    'Aa FStar_Seq_Base.seq ->
      Prims.nat -> Prims.nat -> 'Aa FStar_Seq_Base.seq FStar_Seq_Base.seq
  =
  fun s  ->
    fun i  ->
      fun j  ->
        let frag_lo = FStar_Seq_Base.slice s Prims.int_zero i  in
        let frag_i = FStar_Seq_Base.slice s i (i + Prims.int_one)  in
        let frag_mid = FStar_Seq_Base.slice s (i + Prims.int_one) j  in
        let frag_j = FStar_Seq_Base.slice s j (j + Prims.int_one)  in
        let frag_hi =
          FStar_Seq_Base.slice s (j + Prims.int_one)
            (FStar_Seq_Base.length s)
           in
        FStar_Seq_Base.upd
          (FStar_Seq_Base.upd
             (FStar_Seq_Base.upd
                (FStar_Seq_Base.upd
                   (FStar_Seq_Base.create (Prims.of_int (5)) frag_lo)
                   Prims.int_one frag_i) (Prims.of_int (2)) frag_mid)
             (Prims.of_int (3)) frag_j) (Prims.of_int (4)) frag_hi
  


type ('Aa,'As1,'As2) permutation = unit













let splice :
  'Aa .
    'Aa FStar_Seq_Base.seq ->
      Prims.nat ->
        'Aa FStar_Seq_Base.seq -> Prims.nat -> 'Aa FStar_Seq_Base.seq
  =
  fun s1  ->
    fun i  ->
      fun s2  ->
        fun j  ->
          FStar_Seq_Base.append (FStar_Seq_Base.slice s1 Prims.int_zero i)
            (FStar_Seq_Base.append (FStar_Seq_Base.slice s2 i j)
               (FStar_Seq_Base.slice s1 j (FStar_Seq_Base.length s1)))
  
let replace_subseq :
  'Aa .
    'Aa FStar_Seq_Base.seq ->
      Prims.nat ->
        Prims.nat -> 'Aa FStar_Seq_Base.seq -> 'Aa FStar_Seq_Base.seq
  =
  fun s  ->
    fun i  ->
      fun j  ->
        fun sub  ->
          FStar_Seq_Base.append (FStar_Seq_Base.slice s Prims.int_zero i)
            (FStar_Seq_Base.append sub
               (FStar_Seq_Base.slice s j (FStar_Seq_Base.length s)))
  











let snoc : 'Aa . 'Aa FStar_Seq_Base.seq -> 'Aa -> 'Aa FStar_Seq_Base.seq =
  fun s  ->
    fun x  -> FStar_Seq_Base.append s (FStar_Seq_Base.create Prims.int_one x)
  




let rec find_l :
  'Aa .
    ('Aa -> Prims.bool) ->
      'Aa FStar_Seq_Base.seq -> 'Aa FStar_Pervasives_Native.option
  =
  fun f  ->
    fun l  ->
      if (FStar_Seq_Base.length l) = Prims.int_zero
      then FStar_Pervasives_Native.None
      else
        if f (head l)
        then FStar_Pervasives_Native.Some (head l)
        else find_l f (tail l)
  





let un_snoc : 'Aa . 'Aa FStar_Seq_Base.seq -> ('Aa FStar_Seq_Base.seq * 'Aa)
  =
  fun s  ->
    let uu____1075 = split s ((FStar_Seq_Base.length s) - Prims.int_one)  in
    match uu____1075 with
    | (s',a) -> (s', (FStar_Seq_Base.index a Prims.int_zero))
  

let rec find_r :
  'Aa .
    ('Aa -> Prims.bool) ->
      'Aa FStar_Seq_Base.seq -> 'Aa FStar_Pervasives_Native.option
  =
  fun f  ->
    fun l  ->
      if (FStar_Seq_Base.length l) = Prims.int_zero
      then FStar_Pervasives_Native.None
      else
        (let uu____1151 = un_snoc l  in
         match uu____1151 with
         | (prefix,last1) ->
             if f last1
             then FStar_Pervasives_Native.Some last1
             else find_r f prefix)
  
type 'Ai found = unit
let rec seq_find_aux :
  'Aa .
    ('Aa -> Prims.bool) ->
      'Aa FStar_Seq_Base.seq ->
        Prims.nat -> 'Aa FStar_Pervasives_Native.option
  =
  fun f  ->
    fun l  ->
      fun ctr  ->
        match ctr with
        | _1225 when _1225 = Prims.int_zero -> FStar_Pervasives_Native.None
        | uu____1226 ->
            let i = ctr - Prims.int_one  in
            if f (FStar_Seq_Base.index l i)
            then FStar_Pervasives_Native.Some (FStar_Seq_Base.index l i)
            else seq_find_aux f l i
  
let seq_find :
  'Aa .
    ('Aa -> Prims.bool) ->
      'Aa FStar_Seq_Base.seq -> 'Aa FStar_Pervasives_Native.option
  = fun f  -> fun l  -> seq_find_aux f l (FStar_Seq_Base.length l) 

let for_all :
  'Aa . ('Aa -> Prims.bool) -> 'Aa FStar_Seq_Base.seq -> Prims.bool =
  fun f  ->
    fun l  ->
      FStar_Pervasives_Native.uu___is_None
        (seq_find (fun i  -> Prims.op_Negation (f i)) l)
  

let rec seq_to_list : 'Aa . 'Aa FStar_Seq_Base.seq -> 'Aa Prims.list =
  fun s  ->
    if (FStar_Seq_Base.length s) = Prims.int_zero
    then []
    else (FStar_Seq_Base.index s Prims.int_zero) ::
      (seq_to_list
         (FStar_Seq_Base.slice s Prims.int_one (FStar_Seq_Base.length s)))
  
let rec seq_of_list : 'Aa . 'Aa Prims.list -> 'Aa FStar_Seq_Base.seq =
  fun l  ->
    match l with
    | [] -> FStar_Seq_Base.empty ()
    | hd1::tl1 ->
        FStar_Seq_Base.op_At_Bar (FStar_Seq_Base.create Prims.int_one hd1)
          (seq_of_list tl1)
  



type ('Aa,'Al,'As) createL_post = unit
let createL : 'Aa . 'Aa Prims.list -> 'Aa FStar_Seq_Base.seq =
  fun l  -> let s = seq_of_list l  in s 

type ('Aa,'As,'Ax) contains = unit












type ('Aa,'As_suff,'As) suffix_of = unit














let of_list : 'Aa . 'Aa Prims.list -> 'Aa FStar_Seq_Base.seq =
  fun l  -> seq_of_list l 


type ('Aa,'Ai,'As,'Al) explode_and = Obj.t
type ('Auu____1667,'As,'Al) pointwise_and = Obj.t




let sortWith :
  'Aa .
    ('Aa -> 'Aa -> Prims.int) ->
      'Aa FStar_Seq_Base.seq -> 'Aa FStar_Seq_Base.seq
  =
  fun f  ->
    fun s  -> seq_of_list (FStar_List_Tot_Base.sortWith f (seq_to_list s))
  




let sort_lseq :
  'Aa . Prims.nat -> 'Aa tot_ord -> ('Aa,unit) lseq -> ('Aa,unit) lseq =
  fun n  ->
    fun f  ->
      fun s  ->
        let s' = sortWith (FStar_List_Tot_Base.compare_of_bool f) s  in s'
  