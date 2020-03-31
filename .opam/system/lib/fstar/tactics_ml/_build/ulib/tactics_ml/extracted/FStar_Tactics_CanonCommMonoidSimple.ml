open Prims
let (dump : Prims.string -> (unit,unit) FStar_Tactics_Effect._dm4f_TAC_repr)
  =
  fun m  ->
    fun ps  ->
      match (FStar_Tactics_Builtins.debugging ())
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range
                          "FStar.Tactics.CanonCommMonoidSimple.fst"
                          (Prims.of_int (34)) (Prims.of_int (16))
                          (Prims.of_int (34)) (Prims.of_int (28))))))
      with
      | FStar_Tactics_Result.Success (a,ps') ->
          (match () with
           | () ->
               (if a
                then FStar_Tactics_Builtins.dump m
                else (fun s  -> FStar_Tactics_Result.Success ((), s)))
                 (FStar_Tactics_Types.decr_depth
                    (FStar_Tactics_Types.set_proofstate_range ps'
                       (FStar_Range.prims_to_fstar_range
                          (Prims.mk_range
                             "FStar.Tactics.CanonCommMonoidSimple.fst"
                             (Prims.of_int (34)) (Prims.of_int (13))
                             (Prims.of_int (34)) (Prims.of_int (40)))))))
      | FStar_Tactics_Result.Failed (e,ps') ->
          FStar_Tactics_Result.Failed (e, ps')
  
type atom = Prims.nat
type exp =
  | Unit 
  | Mult of exp * exp 
  | Atom of atom 
let (uu___is_Unit : exp -> Prims.bool) =
  fun projectee  -> match projectee with | Unit  -> true | uu____126 -> false 
let (uu___is_Mult : exp -> Prims.bool) =
  fun projectee  ->
    match projectee with | Mult (_0,_1) -> true | uu____142 -> false
  
let (__proj__Mult__item___0 : exp -> exp) =
  fun projectee  -> match projectee with | Mult (_0,_1) -> _0 
let (__proj__Mult__item___1 : exp -> exp) =
  fun projectee  -> match projectee with | Mult (_0,_1) -> _1 
let (uu___is_Atom : exp -> Prims.bool) =
  fun projectee  ->
    match projectee with | Atom _0 -> true | uu____179 -> false
  
let (__proj__Atom__item___0 : exp -> atom) =
  fun projectee  -> match projectee with | Atom _0 -> _0 
let rec (exp_to_string : exp -> Prims.string) =
  fun e  ->
    match e with
    | Unit  -> "Unit"
    | Atom x -> Prims.strcat "Atom " (Prims.string_of_int x)
    | Mult (e1,e2) ->
        Prims.strcat "Mult ("
          (Prims.strcat (exp_to_string e1)
             (Prims.strcat ") (" (Prims.strcat (exp_to_string e2) ")")))
  
type 'Aa amap = ((atom * 'Aa) Prims.list * 'Aa)
let const : 'Aa . 'Aa -> 'Aa amap = fun xa  -> ([], xa) 
let select : 'Aa . atom -> 'Aa amap -> 'Aa =
  fun x  ->
    fun am  ->
      match FStar_List_Tot_Base.assoc x (FStar_Pervasives_Native.fst am) with
      | FStar_Pervasives_Native.Some a -> a
      | uu____292 -> FStar_Pervasives_Native.snd am
  
let update : 'Aa . atom -> 'Aa -> 'Aa amap -> 'Aa amap =
  fun x  ->
    fun xa  ->
      fun am  ->
        (((x, xa) :: (FStar_Pervasives_Native.fst am)),
          (FStar_Pervasives_Native.snd am))
  
let rec mdenote :
  'Aa . 'Aa FStar_Algebra_CommMonoid.cm -> 'Aa amap -> exp -> 'Aa =
  fun m  ->
    fun am  ->
      fun e  ->
        match e with
        | Unit  -> FStar_Algebra_CommMonoid.__proj__CM__item__unit m
        | Atom x -> select x am
        | Mult (e1,e2) ->
            FStar_Algebra_CommMonoid.__proj__CM__item__mult m
              (mdenote m am e1) (mdenote m am e2)
  
let rec xsdenote :
  'Aa . 'Aa FStar_Algebra_CommMonoid.cm -> 'Aa amap -> atom Prims.list -> 'Aa
  =
  fun m  ->
    fun am  ->
      fun xs  ->
        match xs with
        | [] -> FStar_Algebra_CommMonoid.__proj__CM__item__unit m
        | x::[] -> select x am
        | x::xs' ->
            FStar_Algebra_CommMonoid.__proj__CM__item__mult m (select x am)
              (xsdenote m am xs')
  
let rec (flatten : exp -> atom Prims.list) =
  fun e  ->
    match e with
    | Unit  -> []
    | Atom x -> [x]
    | Mult (e1,e2) -> FStar_List_Tot_Base.op_At (flatten e1) (flatten e2)
  


type permute = atom Prims.list -> atom Prims.list
type 'Ap permute_correct = unit
type 'An swap = Prims.nat
let rec apply_swap_aux :
  'Aa . Prims.nat -> 'Aa Prims.list -> unit swap -> 'Aa Prims.list =
  fun n1  ->
    fun xs  ->
      fun s  ->
        match xs with
        | [] -> xs
        | uu____590::[] -> xs
        | x1::x2::xs' ->
            if n1 = s
            then x2 :: x1 :: xs'
            else x1 :: (apply_swap_aux (n1 + Prims.int_one) (x2 :: xs') s)
  
let apply_swap : 'Aa . unit -> 'Aa Prims.list -> unit swap -> 'Aa Prims.list
  = fun uu____622  -> apply_swap_aux Prims.int_zero 


let rec apply_swaps :
  'Aa . 'Aa Prims.list -> unit swap Prims.list -> 'Aa Prims.list =
  fun xs  ->
    fun ss  ->
      match ss with
      | [] -> xs
      | s::ss' -> apply_swaps ((apply_swap ()) xs s) ss'
  

type 'Ap permute_via_swaps = unit


let (sort : permute) =
  FStar_List_Tot_Base.sortWith (FStar_List_Tot_Base.compare_of_bool (<)) 



let (canon : exp -> atom Prims.list) = fun e  -> sort (flatten e) 



let rec (where_aux :
  Prims.nat ->
    FStar_Reflection_Types.term ->
      FStar_Reflection_Types.term Prims.list ->
        Prims.nat FStar_Pervasives_Native.option)
  =
  fun n1  ->
    fun x  ->
      fun xs  ->
        match xs with
        | [] -> FStar_Pervasives_Native.None
        | x'::xs' ->
            if FStar_Reflection_Basic.term_eq x x'
            then FStar_Pervasives_Native.Some n1
            else where_aux (n1 + Prims.int_one) x xs'
  
let (where :
  FStar_Reflection_Types.term ->
    FStar_Reflection_Types.term Prims.list ->
      Prims.nat FStar_Pervasives_Native.option)
  = where_aux Prims.int_zero 
let rec reification_aux :
  'Aa .
    FStar_Reflection_Types.term Prims.list ->
      'Aa amap ->
        FStar_Reflection_Types.term ->
          FStar_Reflection_Types.term ->
            FStar_Reflection_Types.term ->
              ((exp * FStar_Reflection_Types.term Prims.list * 'Aa amap),
                unit) FStar_Tactics_Effect._dm4f_TAC_repr
  =
  fun ts  ->
    fun am  ->
      fun mult  ->
        fun unit  ->
          fun t  ->
            fun ps  ->
              match () with
              | () ->
                  ((match FStar_Reflection_Derived_Lemmas.collect_app_ref t
                    with
                    | (hd1,tl1) ->
                        (fun ps1  ->
                           match () with
                           | () ->
                               (match match (FStar_Tactics_Builtins.inspect
                                               hd1)
                                              (FStar_Tactics_Types.incr_depth
                                                 (FStar_Tactics_Types.set_proofstate_range
                                                    (FStar_Tactics_Types.incr_depth
                                                       (FStar_Tactics_Types.set_proofstate_range
                                                          (FStar_Tactics_Types.decr_depth
                                                             (FStar_Tactics_Types.set_proofstate_range
                                                                (FStar_Tactics_Types.incr_depth
                                                                   (FStar_Tactics_Types.set_proofstate_range
                                                                    ps1
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                                    (Prims.of_int (244))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (247))
                                                                    (Prims.of_int (57))))))
                                                                (FStar_Range.prims_to_fstar_range
                                                                   (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                                    (Prims.of_int (249))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (259))
                                                                    (Prims.of_int (22))))))
                                                          (FStar_Range.prims_to_fstar_range
                                                             (Prims.mk_range
                                                                "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                                (Prims.of_int (249))
                                                                (Prims.of_int (8))
                                                                (Prims.of_int (249))
                                                                (Prims.of_int (33))))))
                                                    (FStar_Range.prims_to_fstar_range
                                                       (Prims.mk_range
                                                          "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                          (Prims.of_int (249))
                                                          (Prims.of_int (8))
                                                          (Prims.of_int (249))
                                                          (Prims.of_int (18))))))
                                      with
                                      | FStar_Tactics_Result.Success 
                                          (a,ps') ->
                                          (match () with
                                           | () ->
                                               FStar_Tactics_Result.Success
                                                 ((a,
                                                    (FStar_List_Tot_Base.list_unref
                                                       tl1)),
                                                   (FStar_Tactics_Types.decr_depth
                                                      (FStar_Tactics_Types.set_proofstate_range
                                                         ps'
                                                         (FStar_Range.prims_to_fstar_range
                                                            (Prims.mk_range
                                                               "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                               (Prims.of_int (249))
                                                               (Prims.of_int (8))
                                                               (Prims.of_int (249))
                                                               (Prims.of_int (33))))))))
                                      | FStar_Tactics_Result.Failed (e,ps')
                                          ->
                                          FStar_Tactics_Result.Failed
                                            (e, ps')
                                with
                                | FStar_Tactics_Result.Success (a,ps') ->
                                    (match () with
                                     | () ->
                                         ((match a with
                                           | (FStar_Reflection_Data.Tv_FVar
                                              fv,(t1,FStar_Reflection_Data.Q_Explicit
                                                  )::(t2,FStar_Reflection_Data.Q_Explicit
                                                      )::[])
                                               ->
                                               (fun ps2  ->
                                                  match match (FStar_Tactics_Builtins.pack
                                                                 (FStar_Reflection_Data.Tv_FVar
                                                                    fv))
                                                                (FStar_Tactics_Types.incr_depth
                                                                   (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                                    (Prims.of_int (251))
                                                                    (Prims.of_int (7))
                                                                    (Prims.of_int (251))
                                                                    (Prims.of_int (39))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                                    (Prims.of_int (251))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (251))
                                                                    (Prims.of_int (34))))))
                                                        with
                                                        | FStar_Tactics_Result.Success
                                                            (a1,ps'1) ->
                                                            (match () with
                                                             | () ->
                                                                 FStar_Tactics_Result.Success
                                                                   ((FStar_Reflection_Basic.term_eq
                                                                    a1 mult),
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'1
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                                    (Prims.of_int (251))
                                                                    (Prims.of_int (7))
                                                                    (Prims.of_int (251))
                                                                    (Prims.of_int (39))))))))
                                                        | FStar_Tactics_Result.Failed
                                                            (e,ps'1) ->
                                                            FStar_Tactics_Result.Failed
                                                              (e, ps'1)
                                                  with
                                                  | FStar_Tactics_Result.Success
                                                      (a1,ps'1) ->
                                                      (match () with
                                                       | () ->
                                                           (if a1
                                                            then
                                                              (fun ps3  ->
                                                                 match 
                                                                   (reification_aux
                                                                    ts am
                                                                    mult unit
                                                                    t1)
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                                    (Prims.of_int (252))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (252))
                                                                    (Prims.of_int (61))))))
                                                                 with
                                                                 | FStar_Tactics_Result.Success
                                                                    (a2,ps'2)
                                                                    ->
                                                                    (match ()
                                                                    with
                                                                    | 
                                                                    () ->
                                                                    ((match a2
                                                                    with
                                                                    | (e1,ts1,am1)
                                                                    ->
                                                                    (fun ps4 
                                                                    ->
                                                                    match 
                                                                    (reification_aux
                                                                    ts1 am1
                                                                    mult unit
                                                                    t2)
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps4
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                                    (Prims.of_int (253))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (253))
                                                                    (Prims.of_int (61))))))
                                                                    with
                                                                    | 
                                                                    FStar_Tactics_Result.Success
                                                                    (a3,ps'3)
                                                                    ->
                                                                    (match ()
                                                                    with
                                                                    | 
                                                                    () ->
                                                                    FStar_Tactics_Result.Success
                                                                    (((
                                                                    match a3
                                                                    with
                                                                    | 
                                                                    (e2,ts2,am2)
                                                                    ->
                                                                    ((Mult
                                                                    (e1, e2)),
                                                                    ts2, am2))),
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                                    (Prims.of_int (253))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (254))
                                                                    (Prims.of_int (30))))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e,ps'3)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'3))))
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                                    (Prims.of_int (252))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (254))
                                                                    (Prims.of_int (31)))))))
                                                                 | FStar_Tactics_Result.Failed
                                                                    (e,ps'2)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'2))
                                                            else
                                                              (match 
                                                                 where t ts
                                                               with
                                                               | FStar_Pervasives_Native.Some
                                                                   v1 ->
                                                                   (fun s  ->
                                                                    FStar_Tactics_Result.Success
                                                                    (((Atom
                                                                    v1), ts,
                                                                    am), s))
                                                               | FStar_Pervasives_Native.None
                                                                    ->
                                                                   (fun ps3 
                                                                    ->
                                                                    match ()
                                                                    with
                                                                    | 
                                                                    () ->
                                                                    (match 
                                                                    (FStar_Tactics_Builtins.unquote
                                                                    t)
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                                    (Prims.of_int (246))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (246))
                                                                    (Prims.of_int (36))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                                    (Prims.of_int (246))
                                                                    (Prims.of_int (40))
                                                                    (Prims.of_int (247))
                                                                    (Prims.of_int (57))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                                    (Prims.of_int (246))
                                                                    (Prims.of_int (48))
                                                                    (Prims.of_int (246))
                                                                    (Prims.of_int (57))))))
                                                                    with
                                                                    | 
                                                                    FStar_Tactics_Result.Success
                                                                    (a2,ps'2)
                                                                    ->
                                                                    (match ()
                                                                    with
                                                                    | 
                                                                    () ->
                                                                    FStar_Tactics_Result.Success
                                                                    (((Atom
                                                                    (FStar_List_Tot_Base.length
                                                                    ts)),
                                                                    (FStar_List_Tot_Base.op_At
                                                                    ts [t]),
                                                                    (update
                                                                    (FStar_List_Tot_Base.length
                                                                    ts) a2 am)),
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                                    (Prims.of_int (247))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (247))
                                                                    (Prims.of_int (57))))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e,ps'2)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'2)))))
                                                             (FStar_Tactics_Types.decr_depth
                                                                (FStar_Tactics_Types.set_proofstate_range
                                                                   ps'1
                                                                   (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                                    (Prims.of_int (251))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (255))
                                                                    (Prims.of_int (22)))))))
                                                  | FStar_Tactics_Result.Failed
                                                      (e,ps'1) ->
                                                      FStar_Tactics_Result.Failed
                                                        (e, ps'1))
                                           | (uu____2288,uu____2289) ->
                                               if
                                                 FStar_Reflection_Basic.term_eq
                                                   t unit
                                               then
                                                 (fun s  ->
                                                    FStar_Tactics_Result.Success
                                                      ((Unit, ts, am), s))
                                               else
                                                 (match where t ts with
                                                  | FStar_Pervasives_Native.Some
                                                      v1 ->
                                                      (fun s  ->
                                                         FStar_Tactics_Result.Success
                                                           (((Atom v1), ts,
                                                              am), s))
                                                  | FStar_Pervasives_Native.None
                                                       ->
                                                      (fun ps2  ->
                                                         match () with
                                                         | () ->
                                                             (match (FStar_Tactics_Builtins.unquote
                                                                    t)
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                                    (Prims.of_int (246))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (246))
                                                                    (Prims.of_int (36))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                                    (Prims.of_int (246))
                                                                    (Prims.of_int (40))
                                                                    (Prims.of_int (247))
                                                                    (Prims.of_int (57))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                                    (Prims.of_int (246))
                                                                    (Prims.of_int (48))
                                                                    (Prims.of_int (246))
                                                                    (Prims.of_int (57))))))
                                                              with
                                                              | FStar_Tactics_Result.Success
                                                                  (a1,ps'1)
                                                                  ->
                                                                  (match ()
                                                                   with
                                                                   | 
                                                                   () ->
                                                                    FStar_Tactics_Result.Success
                                                                    (((Atom
                                                                    (FStar_List_Tot_Base.length
                                                                    ts)),
                                                                    (FStar_List_Tot_Base.op_At
                                                                    ts [t]),
                                                                    (update
                                                                    (FStar_List_Tot_Base.length
                                                                    ts) a1 am)),
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'1
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                                    (Prims.of_int (247))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (247))
                                                                    (Prims.of_int (57))))))))
                                                              | FStar_Tactics_Result.Failed
                                                                  (e,ps'1) ->
                                                                  FStar_Tactics_Result.Failed
                                                                    (e, ps'1))))))
                                           (FStar_Tactics_Types.decr_depth
                                              (FStar_Tactics_Types.set_proofstate_range
                                                 ps'
                                                 (FStar_Range.prims_to_fstar_range
                                                    (Prims.mk_range
                                                       "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                       (Prims.of_int (249))
                                                       (Prims.of_int (2))
                                                       (Prims.of_int (259))
                                                       (Prims.of_int (22)))))))
                                | FStar_Tactics_Result.Failed (e,ps') ->
                                    FStar_Tactics_Result.Failed (e, ps')))))
                    (FStar_Tactics_Types.decr_depth
                       (FStar_Tactics_Types.set_proofstate_range
                          (FStar_Tactics_Types.incr_depth
                             (FStar_Tactics_Types.set_proofstate_range ps
                                (FStar_Range.prims_to_fstar_range
                                   (Prims.mk_range
                                      "FStar.Tactics.CanonCommMonoidSimple.fst"
                                      (Prims.of_int (242))
                                      (Prims.of_int (15))
                                      (Prims.of_int (242))
                                      (Prims.of_int (32))))))
                          (FStar_Range.prims_to_fstar_range
                             (Prims.mk_range
                                "FStar.Tactics.CanonCommMonoidSimple.fst"
                                (Prims.of_int (242)) (Prims.of_int (2))
                                (Prims.of_int (259)) (Prims.of_int (22))))))
  
let reification :
  'Aa .
    'Aa FStar_Algebra_CommMonoid.cm ->
      FStar_Reflection_Types.term Prims.list ->
        'Aa amap ->
          FStar_Reflection_Types.term ->
            ((exp * FStar_Reflection_Types.term Prims.list * 'Aa amap),
              unit) FStar_Tactics_Effect._dm4f_TAC_repr
  =
  fun m  ->
    fun ts  ->
      fun am  ->
        fun t  ->
          fun ps  ->
            match match () with
                  | () ->
                      (FStar_Tactics_Derived.norm_term
                         [FStar_Pervasives.delta;
                         FStar_Pervasives.zeta;
                         FStar_Pervasives.iota]
                         (Obj.magic
                            (failwith
                               "Cannot evaluate open quotation at runtime")))
                        (FStar_Tactics_Types.decr_depth
                           (FStar_Tactics_Types.set_proofstate_range
                              (FStar_Tactics_Types.incr_depth
                                 (FStar_Tactics_Types.set_proofstate_range
                                    (FStar_Tactics_Types.incr_depth
                                       (FStar_Tactics_Types.set_proofstate_range
                                          ps
                                          (FStar_Range.prims_to_fstar_range
                                             (Prims.mk_range
                                                "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                (Prims.of_int (263))
                                                (Prims.of_int (13))
                                                (Prims.of_int (263))
                                                (Prims.of_int (61))))))
                                    (FStar_Range.prims_to_fstar_range
                                       (Prims.mk_range
                                          "FStar.Tactics.CanonCommMonoidSimple.fst"
                                          (Prims.of_int (263))
                                          (Prims.of_int (41))
                                          (Prims.of_int (263))
                                          (Prims.of_int (61))))))
                              (FStar_Range.prims_to_fstar_range
                                 (Prims.mk_range
                                    "FStar.Tactics.CanonCommMonoidSimple.fst"
                                    (Prims.of_int (263)) (Prims.of_int (13))
                                    (Prims.of_int (263)) (Prims.of_int (61))))))
            with
            | FStar_Tactics_Result.Success (a,ps') ->
                (match () with
                 | () ->
                     (match match () with
                            | () ->
                                (FStar_Tactics_Derived.norm_term
                                   [FStar_Pervasives.delta;
                                   FStar_Pervasives.zeta;
                                   FStar_Pervasives.iota]
                                   (Obj.magic
                                      (failwith
                                         "Cannot evaluate open quotation at runtime")))
                                  (FStar_Tactics_Types.decr_depth
                                     (FStar_Tactics_Types.set_proofstate_range
                                        (FStar_Tactics_Types.incr_depth
                                           (FStar_Tactics_Types.set_proofstate_range
                                              (FStar_Tactics_Types.incr_depth
                                                 (FStar_Tactics_Types.set_proofstate_range
                                                    (FStar_Tactics_Types.decr_depth
                                                       (FStar_Tactics_Types.set_proofstate_range
                                                          ps'
                                                          (FStar_Range.prims_to_fstar_range
                                                             (Prims.mk_range
                                                                "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                                (Prims.of_int (264))
                                                                (Prims.of_int (2))
                                                                (Prims.of_int (266))
                                                                (Prims.of_int (35))))))
                                                    (FStar_Range.prims_to_fstar_range
                                                       (Prims.mk_range
                                                          "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                          (Prims.of_int (264))
                                                          (Prims.of_int (13))
                                                          (Prims.of_int (264))
                                                          (Prims.of_int (61))))))
                                              (FStar_Range.prims_to_fstar_range
                                                 (Prims.mk_range
                                                    "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                    (Prims.of_int (264))
                                                    (Prims.of_int (41))
                                                    (Prims.of_int (264))
                                                    (Prims.of_int (61))))))
                                        (FStar_Range.prims_to_fstar_range
                                           (Prims.mk_range
                                              "FStar.Tactics.CanonCommMonoidSimple.fst"
                                              (Prims.of_int (264))
                                              (Prims.of_int (13))
                                              (Prims.of_int (264))
                                              (Prims.of_int (61))))))
                      with
                      | FStar_Tactics_Result.Success (a1,ps'1) ->
                          (match () with
                           | () ->
                               (match (FStar_Tactics_Derived.norm_term
                                         [FStar_Pervasives.delta;
                                         FStar_Pervasives.zeta;
                                         FStar_Pervasives.iota] t)
                                        (FStar_Tactics_Types.incr_depth
                                           (FStar_Tactics_Types.set_proofstate_range
                                              (FStar_Tactics_Types.decr_depth
                                                 (FStar_Tactics_Types.set_proofstate_range
                                                    ps'1
                                                    (FStar_Range.prims_to_fstar_range
                                                       (Prims.mk_range
                                                          "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                          (Prims.of_int (265))
                                                          (Prims.of_int (2))
                                                          (Prims.of_int (266))
                                                          (Prims.of_int (35))))))
                                              (FStar_Range.prims_to_fstar_range
                                                 (Prims.mk_range
                                                    "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                    (Prims.of_int (265))
                                                    (Prims.of_int (13))
                                                    (Prims.of_int (265))
                                                    (Prims.of_int (42))))))
                                with
                                | FStar_Tactics_Result.Success (a2,ps'2) ->
                                    (match () with
                                     | () ->
                                         (reification_aux ts am a a1 a2)
                                           (FStar_Tactics_Types.decr_depth
                                              (FStar_Tactics_Types.set_proofstate_range
                                                 ps'2
                                                 (FStar_Range.prims_to_fstar_range
                                                    (Prims.mk_range
                                                       "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                       (Prims.of_int (266))
                                                       (Prims.of_int (2))
                                                       (Prims.of_int (266))
                                                       (Prims.of_int (35)))))))
                                | FStar_Tactics_Result.Failed (e,ps'2) ->
                                    FStar_Tactics_Result.Failed (e, ps'2)))
                      | FStar_Tactics_Result.Failed (e,ps'1) ->
                          FStar_Tactics_Result.Failed (e, ps'1)))
            | FStar_Tactics_Result.Failed (e,ps') ->
                FStar_Tactics_Result.Failed (e, ps')
  
let canon_monoid :
  'Aa .
    'Aa FStar_Algebra_CommMonoid.cm ->
      (unit,unit) FStar_Tactics_Effect._dm4f_TAC_repr
  =
  fun m  ->
    fun ps  ->
      match (FStar_Tactics_Builtins.norm [])
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range
                          "FStar.Tactics.CanonCommMonoidSimple.fst"
                          (Prims.of_int (269)) (Prims.of_int (2))
                          (Prims.of_int (269)) (Prims.of_int (9))))))
      with
      | FStar_Tactics_Result.Success (a,ps') ->
          (match () with
           | () ->
               (match match (FStar_Tactics_Derived.cur_goal ())
                              (FStar_Tactics_Types.incr_depth
                                 (FStar_Tactics_Types.set_proofstate_range
                                    (FStar_Tactics_Types.incr_depth
                                       (FStar_Tactics_Types.set_proofstate_range
                                          (FStar_Tactics_Types.decr_depth
                                             (FStar_Tactics_Types.set_proofstate_range
                                                ps'
                                                (FStar_Range.prims_to_fstar_range
                                                   (Prims.mk_range
                                                      "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                      (Prims.of_int (270))
                                                      (Prims.of_int (2))
                                                      (Prims.of_int (293))
                                                      (Prims.of_int (42))))))
                                          (FStar_Range.prims_to_fstar_range
                                             (Prims.mk_range
                                                "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                (Prims.of_int (270))
                                                (Prims.of_int (8))
                                                (Prims.of_int (270))
                                                (Prims.of_int (37))))))
                                    (FStar_Range.prims_to_fstar_range
                                       (Prims.mk_range
                                          "FStar.Tactics.CanonCommMonoidSimple.fst"
                                          (Prims.of_int (270))
                                          (Prims.of_int (24))
                                          (Prims.of_int (270))
                                          (Prims.of_int (37))))))
                      with
                      | FStar_Tactics_Result.Success (a1,ps'1) ->
                          (match () with
                           | () ->
                               (FStar_Reflection_Formula.term_as_formula a1)
                                 (FStar_Tactics_Types.decr_depth
                                    (FStar_Tactics_Types.set_proofstate_range
                                       ps'1
                                       (FStar_Range.prims_to_fstar_range
                                          (Prims.mk_range
                                             "FStar.Tactics.CanonCommMonoidSimple.fst"
                                             (Prims.of_int (270))
                                             (Prims.of_int (8))
                                             (Prims.of_int (270))
                                             (Prims.of_int (37)))))))
                      | FStar_Tactics_Result.Failed (e,ps'1) ->
                          FStar_Tactics_Result.Failed (e, ps'1)
                with
                | FStar_Tactics_Result.Success (a1,ps'1) ->
                    (match () with
                     | () ->
                         ((match a1 with
                           | FStar_Reflection_Formula.Comp
                               (FStar_Reflection_Formula.Eq
                                (FStar_Pervasives_Native.Some t),t1,t2)
                               ->
                               (fun ps1  ->
                                  match match () with
                                        | () ->
                                            FStar_Tactics_Result.Success
                                              ((FStar_Reflection_Basic.term_eq
                                                  t
                                                  (Obj.magic
                                                     (failwith
                                                        "Cannot evaluate open quotation at runtime"))),
                                                (FStar_Tactics_Types.decr_depth
                                                   (FStar_Tactics_Types.set_proofstate_range
                                                      (FStar_Tactics_Types.incr_depth
                                                         (FStar_Tactics_Types.set_proofstate_range
                                                            (FStar_Tactics_Types.incr_depth
                                                               (FStar_Tactics_Types.set_proofstate_range
                                                                  ps1
                                                                  (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                                    (Prims.of_int (274))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (274))
                                                                    (Prims.of_int (28))))))
                                                            (FStar_Range.prims_to_fstar_range
                                                               (Prims.mk_range
                                                                  "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                                  (Prims.of_int (274))
                                                                  (Prims.of_int (19))
                                                                  (Prims.of_int (274))
                                                                  (Prims.of_int (28))))))
                                                      (FStar_Range.prims_to_fstar_range
                                                         (Prims.mk_range
                                                            "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                            (Prims.of_int (274))
                                                            (Prims.of_int (9))
                                                            (Prims.of_int (274))
                                                            (Prims.of_int (28)))))))
                                  with
                                  | FStar_Tactics_Result.Success (a2,ps'2) ->
                                      (match () with
                                       | () ->
                                           (if a2
                                            then
                                              (fun ps2  ->
                                                 match (reification m []
                                                          (const
                                                             (FStar_Algebra_CommMonoid.__proj__CM__item__unit
                                                                m)) t1)
                                                         (FStar_Tactics_Types.incr_depth
                                                            (FStar_Tactics_Types.set_proofstate_range
                                                               ps2
                                                               (FStar_Range.prims_to_fstar_range
                                                                  (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                                    (Prims.of_int (275))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (275))
                                                                    (Prims.of_int (67))))))
                                                 with
                                                 | FStar_Tactics_Result.Success
                                                     (a3,ps'3) ->
                                                     (match () with
                                                      | () ->
                                                          ((match a3 with
                                                            | (r1,ts,am) ->
                                                                (fun ps3  ->
                                                                   match 
                                                                    (reification
                                                                    m ts am
                                                                    t2)
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                                    (Prims.of_int (276))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (276))
                                                                    (Prims.of_int (48))))))
                                                                   with
                                                                   | 
                                                                   FStar_Tactics_Result.Success
                                                                    (a4,ps'4)
                                                                    ->
                                                                    (match ()
                                                                    with
                                                                    | 
                                                                    () ->
                                                                    ((match a4
                                                                    with
                                                                    | (r2,uu____3420,am1)
                                                                    ->
                                                                    (fun ps4 
                                                                    ->
                                                                    match 
                                                                    match 
                                                                    match 
                                                                    match ()
                                                                    with
                                                                    | 
                                                                    () ->
                                                                    FStar_Tactics_Result.Success
                                                                    ((FStar_Reflection_Basic.term_to_string
                                                                    (Obj.magic
                                                                    (failwith
                                                                    "Cannot evaluate open quotation at runtime"))),
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps4
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                                    (Prims.of_int (277))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (277))
                                                                    (Prims.of_int (50))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                                    (Prims.of_int (277))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (277))
                                                                    (Prims.of_int (50))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                                    (Prims.of_int (277))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (277))
                                                                    (Prims.of_int (49))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                                    (Prims.of_int (277))
                                                                    (Prims.of_int (39))
                                                                    (Prims.of_int (277))
                                                                    (Prims.of_int (49))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                                    (Prims.of_int (277))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (277))
                                                                    (Prims.of_int (49)))))))
                                                                    with
                                                                    | 
                                                                    FStar_Tactics_Result.Success
                                                                    (a5,ps'5)
                                                                    ->
                                                                    (match ()
                                                                    with
                                                                    | 
                                                                    () ->
                                                                    FStar_Tactics_Result.Success
                                                                    ((Prims.strcat
                                                                    "am =" a5),
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'5
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (352))
                                                                    (Prims.of_int (45))
                                                                    (Prims.of_int (352))
                                                                    (Prims.of_int (57))))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e,ps'5)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'5)
                                                                    with
                                                                    | 
                                                                    FStar_Tactics_Result.Success
                                                                    (a5,ps'5)
                                                                    ->
                                                                    (match ()
                                                                    with
                                                                    | 
                                                                    () ->
                                                                    (dump a5)
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'5
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                                    (Prims.of_int (277))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (277))
                                                                    (Prims.of_int (50)))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e,ps'5)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'5)
                                                                    with
                                                                    | 
                                                                    FStar_Tactics_Result.Success
                                                                    (a5,ps'5)
                                                                    ->
                                                                    (match ()
                                                                    with
                                                                    | 
                                                                    () ->
                                                                    (match 
                                                                    match ()
                                                                    with
                                                                    | 
                                                                    () ->
                                                                    (FStar_Tactics_Derived.change_sq
                                                                    (Obj.magic
                                                                    (failwith
                                                                    "Cannot evaluate open quotation at runtime")))
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'5
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                                    (Prims.of_int (278))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (290))
                                                                    (Prims.of_int (22))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                                    (Prims.of_int (278))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (278))
                                                                    (Prims.of_int (62))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                                    (Prims.of_int (278))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (278))
                                                                    (Prims.of_int (62))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                                    (Prims.of_int (278))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (278))
                                                                    (Prims.of_int (62))))))
                                                                    with
                                                                    | 
                                                                    FStar_Tactics_Result.Success
                                                                    (a6,ps'6)
                                                                    ->
                                                                    (match ()
                                                                    with
                                                                    | 
                                                                    () ->
                                                                    (match 
                                                                    (FStar_Tactics_Derived.apply
                                                                    (FStar_Reflection_Basic.pack_ln
                                                                    (FStar_Reflection_Data.Tv_FVar
                                                                    (FStar_Reflection_Basic.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "CanonCommMonoidSimple";
                                                                    "monoid_reflect"]))))
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'6
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                                    (Prims.of_int (284))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (290))
                                                                    (Prims.of_int (22))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                                    (Prims.of_int (284))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (284))
                                                                    (Prims.of_int (31))))))
                                                                    with
                                                                    | 
                                                                    FStar_Tactics_Result.Success
                                                                    (a7,ps'7)
                                                                    ->
                                                                    (match ()
                                                                    with
                                                                    | 
                                                                    () ->
                                                                    (FStar_Tactics_Builtins.norm
                                                                    [
                                                                    FStar_Pervasives.delta_only
                                                                    ["FStar.Tactics.CanonCommMonoidSimple.canon";
                                                                    "FStar.Tactics.CanonCommMonoidSimple.xsdenote";
                                                                    "FStar.Tactics.CanonCommMonoidSimple.flatten";
                                                                    "FStar.Tactics.CanonCommMonoidSimple.sort";
                                                                    "FStar.Tactics.CanonCommMonoidSimple.select";
                                                                    "FStar.List.Tot.Base.assoc";
                                                                    "FStar.Pervasives.Native.fst";
                                                                    "FStar.Pervasives.Native.__proj__Mktuple2__item___1";
                                                                    "FStar.List.Tot.Base.op_At";
                                                                    "FStar.List.Tot.Base.append";
                                                                    "FStar.List.Tot.Base.sortWith";
                                                                    "FStar.List.Tot.Base.partition";
                                                                    "FStar.List.Tot.Base.bool_of_compare";
                                                                    "FStar.List.Tot.Base.compare_of_bool"];
                                                                    FStar_Pervasives.primops])
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'7
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                                    (Prims.of_int (286))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (290))
                                                                    (Prims.of_int (22)))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e,ps'7)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'7)))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e,ps'6)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'6)))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e,ps'5)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'5))))
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'4
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                                    (Prims.of_int (276))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (290))
                                                                    (Prims.of_int (22)))))))
                                                                   | 
                                                                   FStar_Tactics_Result.Failed
                                                                    (e,ps'4)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'4))))
                                                            (FStar_Tactics_Types.decr_depth
                                                               (FStar_Tactics_Types.set_proofstate_range
                                                                  ps'3
                                                                  (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                                    (Prims.of_int (275))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (290))
                                                                    (Prims.of_int (22)))))))
                                                 | FStar_Tactics_Result.Failed
                                                     (e,ps'3) ->
                                                     FStar_Tactics_Result.Failed
                                                       (e, ps'3))
                                            else
                                              FStar_Tactics_Derived.fail
                                                "Goal should be an equality at the right monoid type")
                                             (FStar_Tactics_Types.decr_depth
                                                (FStar_Tactics_Types.set_proofstate_range
                                                   ps'2
                                                   (FStar_Range.prims_to_fstar_range
                                                      (Prims.mk_range
                                                         "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                         (Prims.of_int (274))
                                                         (Prims.of_int (6))
                                                         (Prims.of_int (292))
                                                         (Prims.of_int (69)))))))
                                  | FStar_Tactics_Result.Failed (e,ps'2) ->
                                      FStar_Tactics_Result.Failed (e, ps'2))
                           | uu____3564 ->
                               FStar_Tactics_Derived.fail
                                 "Goal should be an equality"))
                           (FStar_Tactics_Types.decr_depth
                              (FStar_Tactics_Types.set_proofstate_range ps'1
                                 (FStar_Range.prims_to_fstar_range
                                    (Prims.mk_range
                                       "FStar.Tactics.CanonCommMonoidSimple.fst"
                                       (Prims.of_int (270))
                                       (Prims.of_int (2))
                                       (Prims.of_int (293))
                                       (Prims.of_int (42)))))))
                | FStar_Tactics_Result.Failed (e,ps'1) ->
                    FStar_Tactics_Result.Failed (e, ps'1)))
      | FStar_Tactics_Result.Failed (e,ps') ->
          FStar_Tactics_Result.Failed (e, ps')
  

