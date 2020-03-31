open Prims
let (dump : Prims.string -> (unit,unit) FStar_Tactics_Effect._dm4f_TAC_repr)
  =
  fun m  ->
    fun ps  ->
      match (FStar_Tactics_Builtins.debugging ())
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.CanonCommMonoid.fst"
                          (Prims.of_int (32)) (Prims.of_int (24))
                          (Prims.of_int (32)) (Prims.of_int (36))))))
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
                          (Prims.mk_range "FStar.Tactics.CanonCommMonoid.fst"
                             (Prims.of_int (32)) (Prims.of_int (21))
                             (Prims.of_int (32)) (Prims.of_int (48)))))))
      | FStar_Tactics_Result.Failed (e,ps') ->
          FStar_Tactics_Result.Failed (e, ps')
  
type var = Prims.nat
type exp =
  | Unit 
  | Var of var 
  | Mult of exp * exp 
let (uu___is_Unit : exp -> Prims.bool) =
  fun projectee  -> match projectee with | Unit  -> true | uu____126 -> false 
let (uu___is_Var : exp -> Prims.bool) =
  fun projectee  ->
    match projectee with | Var _0 -> true | uu____141 -> false
  
let (__proj__Var__item___0 : exp -> var) =
  fun projectee  -> match projectee with | Var _0 -> _0 
let (uu___is_Mult : exp -> Prims.bool) =
  fun projectee  ->
    match projectee with | Mult (_0,_1) -> true | uu____168 -> false
  
let (__proj__Mult__item___0 : exp -> exp) =
  fun projectee  -> match projectee with | Mult (_0,_1) -> _0 
let (__proj__Mult__item___1 : exp -> exp) =
  fun projectee  -> match projectee with | Mult (_0,_1) -> _1 
let rec (exp_to_string : exp -> Prims.string) =
  fun e  ->
    match e with
    | Unit  -> "Unit"
    | Var x -> Prims.strcat "Var " (Prims.string_of_int x)
    | Mult (e1,e2) ->
        Prims.strcat "Mult ("
          (Prims.strcat (exp_to_string e1)
             (Prims.strcat ") (" (Prims.strcat (exp_to_string e2) ")")))
  
type ('Aa,'Ab) vmap = ((var * ('Aa * 'Ab)) Prims.list * ('Aa * 'Ab))
let const : 'Aa 'Ab . 'Aa -> 'Ab -> ('Aa,'Ab) vmap =
  fun xa  -> fun xb  -> ([], (xa, xb)) 
let select : 'Aa 'Ab . var -> ('Aa,'Ab) vmap -> 'Aa =
  fun x  ->
    fun vm  ->
      match FStar_List_Tot_Base.assoc x (FStar_Pervasives_Native.fst vm) with
      | FStar_Pervasives_Native.Some (a,uu____351) -> a
      | uu____356 ->
          FStar_Pervasives_Native.fst (FStar_Pervasives_Native.snd vm)
  
let select_extra : 'Aa 'Ab . var -> ('Aa,'Ab) vmap -> 'Ab =
  fun x  ->
    fun vm  ->
      match FStar_List_Tot_Base.assoc x (FStar_Pervasives_Native.fst vm) with
      | FStar_Pervasives_Native.Some (uu____436,b) -> b
      | uu____442 ->
          FStar_Pervasives_Native.snd (FStar_Pervasives_Native.snd vm)
  
let update : 'Aa 'Ab . var -> 'Aa -> 'Ab -> ('Aa,'Ab) vmap -> ('Aa,'Ab) vmap
  =
  fun x  ->
    fun xa  ->
      fun xb  ->
        fun vm  ->
          (((x, (xa, xb)) :: (FStar_Pervasives_Native.fst vm)),
            (FStar_Pervasives_Native.snd vm))
  
let rec mdenote :
  'Aa 'Ab . 'Aa FStar_Algebra_CommMonoid.cm -> ('Aa,'Ab) vmap -> exp -> 'Aa =
  fun m  ->
    fun vm  ->
      fun e  ->
        match e with
        | Unit  -> FStar_Algebra_CommMonoid.__proj__CM__item__unit m
        | Var x -> select x vm
        | Mult (e1,e2) ->
            FStar_Algebra_CommMonoid.__proj__CM__item__mult m
              (mdenote m vm e1) (mdenote m vm e2)
  
let rec xsdenote :
  'Aa 'Ab .
    'Aa FStar_Algebra_CommMonoid.cm ->
      ('Aa,'Ab) vmap -> var Prims.list -> 'Aa
  =
  fun m  ->
    fun vm  ->
      fun xs  ->
        match xs with
        | [] -> FStar_Algebra_CommMonoid.__proj__CM__item__unit m
        | x::[] -> select x vm
        | x::xs' ->
            FStar_Algebra_CommMonoid.__proj__CM__item__mult m (select x vm)
              (xsdenote m vm xs')
  
let rec (flatten : exp -> var Prims.list) =
  fun e  ->
    match e with
    | Unit  -> []
    | Var x -> [x]
    | Mult (e1,e2) -> FStar_List_Tot_Base.op_At (flatten e1) (flatten e2)
  


type 'Ab permute =
  unit -> (Obj.t,'Ab) vmap -> var Prims.list -> var Prims.list
type ('Ab,'Ap) permute_correct = unit



type ('Ab,'Ap) permute_via_swaps = unit


let (sort : unit permute) =
  fun a  ->
    fun vm  ->
      FStar_List_Tot_Base.sortWith (FStar_List_Tot_Base.compare_of_bool (<))
  
let sortWith : 'Ab . (Prims.nat -> Prims.nat -> Prims.int) -> 'Ab permute =
  fun f  -> fun a  -> fun vm  -> FStar_List_Tot_Base.sortWith f 






let canon : 'Aa 'Ab . ('Aa,'Ab) vmap -> 'Ab permute -> exp -> var Prims.list
  = fun vm  -> fun p  -> fun e  -> p () (Obj.magic vm) (flatten e) 


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
  'Aa 'Ab .
    (FStar_Reflection_Types.term ->
       ('Aa,unit) FStar_Tactics_Effect._dm4f_TAC_repr)
      ->
      FStar_Reflection_Types.term Prims.list ->
        ('Aa,'Ab) vmap ->
          (FStar_Reflection_Types.term ->
             ('Ab,unit) FStar_Tactics_Effect._dm4f_TAC_repr)
            ->
            FStar_Reflection_Types.term ->
              FStar_Reflection_Types.term ->
                FStar_Reflection_Types.term ->
                  ((exp * FStar_Reflection_Types.term Prims.list * ('Aa,
                     'Ab) vmap),unit)
                    FStar_Tactics_Effect._dm4f_TAC_repr
  =
  fun unquotea  ->
    fun ts  ->
      fun vm  ->
        fun f  ->
          fun mult  ->
            fun unit  ->
              fun t  ->
                fun ps  ->
                  match () with
                  | () ->
                      ((match FStar_Reflection_Derived_Lemmas.collect_app_ref
                                t
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
                                                                    (
                                                                    FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps1
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (245))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (248))
                                                                    (Prims.of_int (62))))))
                                                                    (
                                                                    FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (250))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (260))
                                                                    (Prims.of_int (21))))))
                                                              (FStar_Range.prims_to_fstar_range
                                                                 (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (250))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (250))
                                                                    (Prims.of_int (33))))))
                                                        (FStar_Range.prims_to_fstar_range
                                                           (Prims.mk_range
                                                              "FStar.Tactics.CanonCommMonoid.fst"
                                                              (Prims.of_int (250))
                                                              (Prims.of_int (8))
                                                              (Prims.of_int (250))
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
                                                                   "FStar.Tactics.CanonCommMonoid.fst"
                                                                   (Prims.of_int (250))
                                                                   (Prims.of_int (8))
                                                                   (Prims.of_int (250))
                                                                   (Prims.of_int (33))))))))
                                          | FStar_Tactics_Result.Failed
                                              (e,ps') ->
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
                                                                    (
                                                                    FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (252))
                                                                    (Prims.of_int (7))
                                                                    (Prims.of_int (252))
                                                                    (Prims.of_int (39))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (252))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (252))
                                                                    (Prims.of_int (34))))))
                                                            with
                                                            | FStar_Tactics_Result.Success
                                                                (a1,ps'1) ->
                                                                (match ()
                                                                 with
                                                                 | () ->
                                                                    FStar_Tactics_Result.Success
                                                                    ((FStar_Reflection_Basic.term_eq
                                                                    a1 mult),
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'1
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (252))
                                                                    (Prims.of_int (7))
                                                                    (Prims.of_int (252))
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
                                                                  (fun ps3 
                                                                    ->
                                                                    match 
                                                                    (reification_aux
                                                                    unquotea
                                                                    ts vm f
                                                                    mult unit
                                                                    t1)
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (253))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (253))
                                                                    (Prims.of_int (72))))))
                                                                    with
                                                                    | 
                                                                    FStar_Tactics_Result.Success
                                                                    (a2,ps'2)
                                                                    ->
                                                                    (match ()
                                                                    with
                                                                    | 
                                                                    () ->
                                                                    ((match a2
                                                                    with
                                                                    | (e1,ts1,vm1)
                                                                    ->
                                                                    (fun ps4 
                                                                    ->
                                                                    match 
                                                                    (reification_aux
                                                                    unquotea
                                                                    ts1 vm1 f
                                                                    mult unit
                                                                    t2)
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps4
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (254))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (254))
                                                                    (Prims.of_int (72))))))
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
                                                                    (e2,ts2,vm2)
                                                                    ->
                                                                    ((Mult
                                                                    (e1, e2)),
                                                                    ts2, vm2))),
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (254))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (255))
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
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (253))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (255))
                                                                    (Prims.of_int (31)))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e,ps'2)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'2))
                                                                else
                                                                  (match 
                                                                    where t
                                                                    ts
                                                                   with
                                                                   | 
                                                                   FStar_Pervasives_Native.Some
                                                                    v1 ->
                                                                    (fun s 
                                                                    ->
                                                                    FStar_Tactics_Result.Success
                                                                    (((Var v1),
                                                                    ts, vm),
                                                                    s))
                                                                   | 
                                                                   FStar_Pervasives_Native.None
                                                                     ->
                                                                    (fun ps3 
                                                                    ->
                                                                    match ()
                                                                    with
                                                                    | 
                                                                    () ->
                                                                    (match 
                                                                    (unquotea
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
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (247))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (247))
                                                                    (Prims.of_int (36))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (247))
                                                                    (Prims.of_int (40))
                                                                    (Prims.of_int (248))
                                                                    (Prims.of_int (62))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (247))
                                                                    (Prims.of_int (48))
                                                                    (Prims.of_int (247))
                                                                    (Prims.of_int (58))))))
                                                                    with
                                                                    | 
                                                                    FStar_Tactics_Result.Success
                                                                    (a2,ps'2)
                                                                    ->
                                                                    (match ()
                                                                    with
                                                                    | 
                                                                    () ->
                                                                    (match 
                                                                    match 
                                                                    (f t)
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (248))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (248))
                                                                    (Prims.of_int (62))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (248))
                                                                    (Prims.of_int (37))
                                                                    (Prims.of_int (248))
                                                                    (Prims.of_int (61))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (248))
                                                                    (Prims.of_int (53))
                                                                    (Prims.of_int (248))
                                                                    (Prims.of_int (58))))))
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
                                                                    ((update
                                                                    (FStar_List_Tot_Base.length
                                                                    ts) a2 a3
                                                                    vm),
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (248))
                                                                    (Prims.of_int (37))
                                                                    (Prims.of_int (248))
                                                                    (Prims.of_int (61))))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e,ps'3)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'3)
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
                                                                    (((Var
                                                                    (FStar_List_Tot_Base.length
                                                                    ts)),
                                                                    (FStar_List_Tot_Base.op_At
                                                                    ts [t]),
                                                                    a3),
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (248))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (248))
                                                                    (Prims.of_int (62))))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e,ps'3)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'3)))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e,ps'2)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'2)))))
                                                                 (FStar_Tactics_Types.decr_depth
                                                                    (
                                                                    FStar_Tactics_Types.set_proofstate_range
                                                                    ps'1
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (252))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (256))
                                                                    (Prims.of_int (21)))))))
                                                      | FStar_Tactics_Result.Failed
                                                          (e,ps'1) ->
                                                          FStar_Tactics_Result.Failed
                                                            (e, ps'1))
                                               | (uu____2917,uu____2918) ->
                                                   if
                                                     FStar_Reflection_Basic.term_eq
                                                       t unit
                                                   then
                                                     (fun s  ->
                                                        FStar_Tactics_Result.Success
                                                          ((Unit, ts, vm), s))
                                                   else
                                                     (match where t ts with
                                                      | FStar_Pervasives_Native.Some
                                                          v1 ->
                                                          (fun s  ->
                                                             FStar_Tactics_Result.Success
                                                               (((Var v1),
                                                                  ts, vm), s))
                                                      | FStar_Pervasives_Native.None
                                                           ->
                                                          (fun ps2  ->
                                                             match () with
                                                             | () ->
                                                                 (match 
                                                                    (unquotea
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
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (247))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (247))
                                                                    (Prims.of_int (36))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (247))
                                                                    (Prims.of_int (40))
                                                                    (Prims.of_int (248))
                                                                    (Prims.of_int (62))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (247))
                                                                    (Prims.of_int (48))
                                                                    (Prims.of_int (247))
                                                                    (Prims.of_int (58))))))
                                                                  with
                                                                  | FStar_Tactics_Result.Success
                                                                    (a1,ps'1)
                                                                    ->
                                                                    (match ()
                                                                    with
                                                                    | 
                                                                    () ->
                                                                    (match 
                                                                    match 
                                                                    (f t)
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'1
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (248))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (248))
                                                                    (Prims.of_int (62))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (248))
                                                                    (Prims.of_int (37))
                                                                    (Prims.of_int (248))
                                                                    (Prims.of_int (61))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (248))
                                                                    (Prims.of_int (53))
                                                                    (Prims.of_int (248))
                                                                    (Prims.of_int (58))))))
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
                                                                    ((update
                                                                    (FStar_List_Tot_Base.length
                                                                    ts) a1 a2
                                                                    vm),
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (248))
                                                                    (Prims.of_int (37))
                                                                    (Prims.of_int (248))
                                                                    (Prims.of_int (61))))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e,ps'2)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'2)
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
                                                                    (((Var
                                                                    (FStar_List_Tot_Base.length
                                                                    ts)),
                                                                    (FStar_List_Tot_Base.op_At
                                                                    ts [t]),
                                                                    a2),
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (248))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (248))
                                                                    (Prims.of_int (62))))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e,ps'2)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'2)))
                                                                  | FStar_Tactics_Result.Failed
                                                                    (e,ps'1)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'1))))))
                                               (FStar_Tactics_Types.decr_depth
                                                  (FStar_Tactics_Types.set_proofstate_range
                                                     ps'
                                                     (FStar_Range.prims_to_fstar_range
                                                        (Prims.mk_range
                                                           "FStar.Tactics.CanonCommMonoid.fst"
                                                           (Prims.of_int (250))
                                                           (Prims.of_int (2))
                                                           (Prims.of_int (260))
                                                           (Prims.of_int (21)))))))
                                    | FStar_Tactics_Result.Failed (e,ps') ->
                                        FStar_Tactics_Result.Failed (e, ps')))))
                        (FStar_Tactics_Types.decr_depth
                           (FStar_Tactics_Types.set_proofstate_range
                              (FStar_Tactics_Types.incr_depth
                                 (FStar_Tactics_Types.set_proofstate_range ps
                                    (FStar_Range.prims_to_fstar_range
                                       (Prims.mk_range
                                          "FStar.Tactics.CanonCommMonoid.fst"
                                          (Prims.of_int (243))
                                          (Prims.of_int (15))
                                          (Prims.of_int (243))
                                          (Prims.of_int (32))))))
                              (FStar_Range.prims_to_fstar_range
                                 (Prims.mk_range
                                    "FStar.Tactics.CanonCommMonoid.fst"
                                    (Prims.of_int (243)) (Prims.of_int (2))
                                    (Prims.of_int (260)) (Prims.of_int (21))))))
  
let reification :
  'Ab .
    (FStar_Reflection_Types.term ->
       ('Ab,unit) FStar_Tactics_Effect._dm4f_TAC_repr)
      ->
      'Ab ->
        unit ->
          (FStar_Reflection_Types.term ->
             (Obj.t,unit) FStar_Tactics_Effect._dm4f_TAC_repr)
            ->
            (Obj.t ->
               (FStar_Reflection_Types.term,unit)
                 FStar_Tactics_Effect._dm4f_TAC_repr)
              ->
              FStar_Reflection_Types.term ->
                FStar_Reflection_Types.term ->
                  Obj.t ->
                    FStar_Reflection_Types.term Prims.list ->
                      ((exp Prims.list * (Obj.t,'Ab) vmap),unit)
                        FStar_Tactics_Effect._dm4f_TAC_repr
  =
  fun f  ->
    fun def  ->
      fun a  ->
        fun unquotea  ->
          fun quotea  ->
            fun tmult  ->
              fun tunit  ->
                fun munit  ->
                  fun ts  ->
                    fun ps  ->
                      match (FStar_Tactics_Derived.norm_term
                               [FStar_Pervasives.delta;
                               FStar_Pervasives.zeta;
                               FStar_Pervasives.iota] tmult)
                              (FStar_Tactics_Types.incr_depth
                                 (FStar_Tactics_Types.set_proofstate_range ps
                                    (FStar_Range.prims_to_fstar_range
                                       (Prims.mk_range
                                          "FStar.Tactics.CanonCommMonoid.fst"
                                          (Prims.of_int (267))
                                          (Prims.of_int (20))
                                          (Prims.of_int (267))
                                          (Prims.of_int (53))))))
                      with
                      | FStar_Tactics_Result.Success (a,ps') ->
                          (match () with
                           | () ->
                               (match (FStar_Tactics_Derived.norm_term
                                         [FStar_Pervasives.delta;
                                         FStar_Pervasives.zeta;
                                         FStar_Pervasives.iota] tunit)
                                        (FStar_Tactics_Types.incr_depth
                                           (FStar_Tactics_Types.set_proofstate_range
                                              (FStar_Tactics_Types.decr_depth
                                                 (FStar_Tactics_Types.set_proofstate_range
                                                    ps'
                                                    (FStar_Range.prims_to_fstar_range
                                                       (Prims.mk_range
                                                          "FStar.Tactics.CanonCommMonoid.fst"
                                                          (Prims.of_int (268))
                                                          (Prims.of_int (2))
                                                          (Prims.of_int (279))
                                                          (Prims.of_int (21))))))
                                              (FStar_Range.prims_to_fstar_range
                                                 (Prims.mk_range
                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                    (Prims.of_int (268))
                                                    (Prims.of_int (20))
                                                    (Prims.of_int (268))
                                                    (Prims.of_int (53))))))
                                with
                                | FStar_Tactics_Result.Success (a1,ps'1) ->
                                    (match () with
                                     | () ->
                                         (match (FStar_Tactics_Util.map
                                                   (FStar_Tactics_Derived.norm_term
                                                      [FStar_Pervasives.delta;
                                                      FStar_Pervasives.zeta;
                                                      FStar_Pervasives.iota])
                                                   ts)
                                                  (FStar_Tactics_Types.incr_depth
                                                     (FStar_Tactics_Types.set_proofstate_range
                                                        (FStar_Tactics_Types.decr_depth
                                                           (FStar_Tactics_Types.set_proofstate_range
                                                              ps'1
                                                              (FStar_Range.prims_to_fstar_range
                                                                 (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (269))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (279))
                                                                    (Prims.of_int (21))))))
                                                        (FStar_Range.prims_to_fstar_range
                                                           (Prims.mk_range
                                                              "FStar.Tactics.CanonCommMonoid.fst"
                                                              (Prims.of_int (269))
                                                              (Prims.of_int (13))
                                                              (Prims.of_int (269))
                                                              (Prims.of_int (62))))))
                                          with
                                          | FStar_Tactics_Result.Success
                                              (a2,ps'2) ->
                                              (match () with
                                               | () ->
                                                   (match (FStar_Tactics_Util.fold_left
                                                             (fun uu____3765 
                                                                ->
                                                                fun t  ->
                                                                  match uu____3765
                                                                  with
                                                                  | (es,vs,vm)
                                                                    ->
                                                                    (fun ps1 
                                                                    ->
                                                                    match 
                                                                    (reification_aux
                                                                    unquotea
                                                                    vs vm f a
                                                                    a1 t)
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps1
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (276))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (276))
                                                                    (Prims.of_int (70))))))
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
                                                                    (e,vs1,vm1)
                                                                    ->
                                                                    ((e ::
                                                                    es), vs1,
                                                                    vm1))),
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (276))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (276))
                                                                    (Prims.of_int (20))))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e,ps'3)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'3)))
                                                             ([], [],
                                                               (const munit
                                                                  def)) a2)
                                                            (FStar_Tactics_Types.incr_depth
                                                               (FStar_Tactics_Types.set_proofstate_range
                                                                  (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (273))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (279))
                                                                    (Prims.of_int (21))))))
                                                                  (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (274))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (278))
                                                                    (Prims.of_int (33))))))
                                                    with
                                                    | FStar_Tactics_Result.Success
                                                        (a3,ps'3) ->
                                                        (match () with
                                                         | () ->
                                                             FStar_Tactics_Result.Success
                                                               (((match a3
                                                                  with
                                                                  | (es,uu____4108,vm)
                                                                    ->
                                                                    ((FStar_List_Tot_Base.rev
                                                                    es), vm))),
                                                                 (FStar_Tactics_Types.decr_depth
                                                                    (
                                                                    FStar_Tactics_Types.set_proofstate_range
                                                                    ps'3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (273))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (279))
                                                                    (Prims.of_int (21))))))))
                                                    | FStar_Tactics_Result.Failed
                                                        (e,ps'3) ->
                                                        FStar_Tactics_Result.Failed
                                                          (e, ps'3)))
                                          | FStar_Tactics_Result.Failed
                                              (e,ps'2) ->
                                              FStar_Tactics_Result.Failed
                                                (e, ps'2)))
                                | FStar_Tactics_Result.Failed (e,ps'1) ->
                                    FStar_Tactics_Result.Failed (e, ps'1)))
                      | FStar_Tactics_Result.Failed (e,ps') ->
                          FStar_Tactics_Result.Failed (e, ps')
  
let rec (term_mem :
  FStar_Reflection_Types.term ->
    FStar_Reflection_Types.term Prims.list -> Prims.bool)
  =
  fun x  ->
    fun uu___0_4214  ->
      match uu___0_4214 with
      | [] -> false
      | hd1::tl1 ->
          if FStar_Reflection_Basic.term_eq hd1 x
          then true
          else term_mem x tl1
  
let (unfold_topdown :
  FStar_Reflection_Types.term Prims.list ->
    (unit,unit) FStar_Tactics_Effect._dm4f_TAC_repr)
  =
  fun ts  ->
    fun ps  ->
      match () with
      | () ->
          (match () with
           | () ->
               (FStar_Tactics_Builtins.topdown_rewrite
                  (fun s  ->
                     fun s1  ->
                       FStar_Tactics_Result.Success
                         (((term_mem s ts), Prims.int_zero), s1))
                  (fun uu____4390  ->
                     fun ps1  ->
                       match (FStar_Tactics_Builtins.norm
                                [FStar_Pervasives.delta])
                               (FStar_Tactics_Types.incr_depth
                                  (FStar_Tactics_Types.set_proofstate_range
                                     ps1
                                     (FStar_Range.prims_to_fstar_range
                                        (Prims.mk_range
                                           "FStar.Tactics.CanonCommMonoid.fst"
                                           (Prims.of_int (291))
                                           (Prims.of_int (4))
                                           (Prims.of_int (291))
                                           (Prims.of_int (16))))))
                       with
                       | FStar_Tactics_Result.Success (a,ps') ->
                           (match () with
                            | () ->
                                (FStar_Tactics_Builtins.trefl ())
                                  (FStar_Tactics_Types.decr_depth
                                     (FStar_Tactics_Types.set_proofstate_range
                                        ps'
                                        (FStar_Range.prims_to_fstar_range
                                           (Prims.mk_range
                                              "FStar.Tactics.CanonCommMonoid.fst"
                                              (Prims.of_int (292))
                                              (Prims.of_int (4))
                                              (Prims.of_int (292))
                                              (Prims.of_int (11)))))))
                       | FStar_Tactics_Result.Failed (e,ps') ->
                           FStar_Tactics_Result.Failed (e, ps')))
                 (FStar_Tactics_Types.decr_depth
                    (FStar_Tactics_Types.set_proofstate_range
                       (FStar_Tactics_Types.incr_depth
                          (FStar_Tactics_Types.set_proofstate_range
                             (FStar_Tactics_Types.decr_depth
                                (FStar_Tactics_Types.set_proofstate_range
                                   (FStar_Tactics_Types.incr_depth
                                      (FStar_Tactics_Types.set_proofstate_range
                                         ps
                                         (FStar_Range.prims_to_fstar_range
                                            (Prims.mk_range
                                               "FStar.Tactics.CanonCommMonoid.fst"
                                               (Prims.of_int (288))
                                               (Prims.of_int (4))
                                               (Prims.of_int (288))
                                               (Prims.of_int (22))))))
                                   (FStar_Range.prims_to_fstar_range
                                      (Prims.mk_range
                                         "FStar.Tactics.CanonCommMonoid.fst"
                                         (Prims.of_int (290))
                                         (Prims.of_int (2))
                                         (Prims.of_int (294))
                                         (Prims.of_int (40))))))
                             (FStar_Range.prims_to_fstar_range
                                (Prims.mk_range
                                   "FStar.Tactics.CanonCommMonoid.fst"
                                   (Prims.of_int (291)) (Prims.of_int (4))
                                   (Prims.of_int (292)) (Prims.of_int (11))))))
                       (FStar_Range.prims_to_fstar_range
                          (Prims.mk_range "FStar.Tactics.CanonCommMonoid.fst"
                             (Prims.of_int (294)) (Prims.of_int (2))
                             (Prims.of_int (294)) (Prims.of_int (40)))))))
  
let rec quote_list :
  'Aa .
    FStar_Reflection_Types.term ->
      ('Aa ->
         (FStar_Reflection_Types.term,unit)
           FStar_Tactics_Effect._dm4f_TAC_repr)
        ->
        'Aa Prims.list ->
          (FStar_Reflection_Types.term,unit)
            FStar_Tactics_Effect._dm4f_TAC_repr
  =
  fun ta  ->
    fun quotea  ->
      fun xs  ->
        match xs with
        | [] ->
            (fun s  ->
               FStar_Tactics_Result.Success
                 ((FStar_Reflection_Derived.mk_app
                     (FStar_Reflection_Basic.pack_ln
                        (FStar_Reflection_Data.Tv_FVar
                           (FStar_Reflection_Basic.pack_fv ["Prims"; "Nil"])))
                     [(ta, FStar_Reflection_Data.Q_Implicit)]), s))
        | x::xs' ->
            (fun ps  ->
               match match match match (quotea x)
                                         (FStar_Tactics_Types.incr_depth
                                            (FStar_Tactics_Types.set_proofstate_range
                                               (FStar_Tactics_Types.incr_depth
                                                  (FStar_Tactics_Types.set_proofstate_range
                                                     (FStar_Tactics_Types.incr_depth
                                                        (FStar_Tactics_Types.set_proofstate_range
                                                           (FStar_Tactics_Types.incr_depth
                                                              (FStar_Tactics_Types.set_proofstate_range
                                                                 ps
                                                                 (FStar_Range.prims_to_fstar_range
                                                                    (
                                                                    Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (300))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (302))
                                                                    (Prims.of_int (69))))))
                                                           (FStar_Range.prims_to_fstar_range
                                                              (Prims.mk_range
                                                                 "FStar.Tactics.CanonCommMonoid.fst"
                                                                 (Prims.of_int (300))
                                                                 (Prims.of_int (29))
                                                                 (Prims.of_int (302))
                                                                 (Prims.of_int (69))))))
                                                     (FStar_Range.prims_to_fstar_range
                                                        (Prims.mk_range
                                                           "FStar.Tactics.CanonCommMonoid.fst"
                                                           (Prims.of_int (301))
                                                           (Prims.of_int (30))
                                                           (Prims.of_int (301))
                                                           (Prims.of_int (52))))))
                                               (FStar_Range.prims_to_fstar_range
                                                  (Prims.mk_range
                                                     "FStar.Tactics.CanonCommMonoid.fst"
                                                     (Prims.of_int (301))
                                                     (Prims.of_int (31))
                                                     (Prims.of_int (301))
                                                     (Prims.of_int (39))))))
                                 with
                                 | FStar_Tactics_Result.Success (a,ps') ->
                                     (match () with
                                      | () ->
                                          FStar_Tactics_Result.Success
                                            ((a,
                                               FStar_Reflection_Data.Q_Explicit),
                                              (FStar_Tactics_Types.decr_depth
                                                 (FStar_Tactics_Types.set_proofstate_range
                                                    ps'
                                                    (FStar_Range.prims_to_fstar_range
                                                       (Prims.mk_range
                                                          "FStar.Tactics.CanonCommMonoid.fst"
                                                          (Prims.of_int (301))
                                                          (Prims.of_int (30))
                                                          (Prims.of_int (301))
                                                          (Prims.of_int (52))))))))
                                 | FStar_Tactics_Result.Failed (e,ps') ->
                                     FStar_Tactics_Result.Failed (e, ps')
                           with
                           | FStar_Tactics_Result.Success (a,ps') ->
                               (match () with
                                | () ->
                                    (match match match (quote_list ta quotea
                                                          xs')
                                                         (FStar_Tactics_Types.incr_depth
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
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (300))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (302))
                                                                    (Prims.of_int (69))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (300))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (302))
                                                                    (Prims.of_int (69))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (302))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (302))
                                                                    (Prims.of_int (68))))))
                                                               (FStar_Range.prims_to_fstar_range
                                                                  (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (302))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (302))
                                                                    (Prims.of_int (55))))))
                                                 with
                                                 | FStar_Tactics_Result.Success
                                                     (a1,ps'1) ->
                                                     (match () with
                                                      | () ->
                                                          FStar_Tactics_Result.Success
                                                            ((a1,
                                                               FStar_Reflection_Data.Q_Explicit),
                                                              (FStar_Tactics_Types.decr_depth
                                                                 (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'1
                                                                    (
                                                                    FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (302))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (302))
                                                                    (Prims.of_int (68))))))))
                                                 | FStar_Tactics_Result.Failed
                                                     (e,ps'1) ->
                                                     FStar_Tactics_Result.Failed
                                                       (e, ps'1)
                                           with
                                           | FStar_Tactics_Result.Success
                                               (a1,ps'1) ->
                                               (match () with
                                                | () ->
                                                    FStar_Tactics_Result.Success
                                                      ([a1],
                                                        (FStar_Tactics_Types.decr_depth
                                                           (FStar_Tactics_Types.set_proofstate_range
                                                              ps'1
                                                              (FStar_Range.prims_to_fstar_range
                                                                 (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (300))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (302))
                                                                    (Prims.of_int (69))))))))
                                           | FStar_Tactics_Result.Failed
                                               (e,ps'1) ->
                                               FStar_Tactics_Result.Failed
                                                 (e, ps'1)
                                     with
                                     | FStar_Tactics_Result.Success (a1,ps'1)
                                         ->
                                         (match () with
                                          | () ->
                                              FStar_Tactics_Result.Success
                                                ((a :: a1),
                                                  (FStar_Tactics_Types.decr_depth
                                                     (FStar_Tactics_Types.set_proofstate_range
                                                        ps'1
                                                        (FStar_Range.prims_to_fstar_range
                                                           (Prims.mk_range
                                                              "FStar.Tactics.CanonCommMonoid.fst"
                                                              (Prims.of_int (300))
                                                              (Prims.of_int (29))
                                                              (Prims.of_int (302))
                                                              (Prims.of_int (69))))))))
                                     | FStar_Tactics_Result.Failed (e,ps'1)
                                         ->
                                         FStar_Tactics_Result.Failed
                                           (e, ps'1)))
                           | FStar_Tactics_Result.Failed (e,ps') ->
                               FStar_Tactics_Result.Failed (e, ps')
                     with
                     | FStar_Tactics_Result.Success (a,ps') ->
                         (match () with
                          | () ->
                              FStar_Tactics_Result.Success
                                (((ta, FStar_Reflection_Data.Q_Implicit) ::
                                  a),
                                  (FStar_Tactics_Types.decr_depth
                                     (FStar_Tactics_Types.set_proofstate_range
                                        ps'
                                        (FStar_Range.prims_to_fstar_range
                                           (Prims.mk_range
                                              "FStar.Tactics.CanonCommMonoid.fst"
                                              (Prims.of_int (300))
                                              (Prims.of_int (29))
                                              (Prims.of_int (302))
                                              (Prims.of_int (69))))))))
                     | FStar_Tactics_Result.Failed (e,ps') ->
                         FStar_Tactics_Result.Failed (e, ps')
               with
               | FStar_Tactics_Result.Success (a,ps') ->
                   (match () with
                    | () ->
                        FStar_Tactics_Result.Success
                          ((FStar_Reflection_Derived.mk_app
                              (FStar_Reflection_Basic.pack_ln
                                 (FStar_Reflection_Data.Tv_FVar
                                    (FStar_Reflection_Basic.pack_fv
                                       ["Prims"; "Cons"]))) a),
                            (FStar_Tactics_Types.decr_depth
                               (FStar_Tactics_Types.set_proofstate_range ps'
                                  (FStar_Range.prims_to_fstar_range
                                     (Prims.mk_range
                                        "FStar.Tactics.CanonCommMonoid.fst"
                                        (Prims.of_int (300))
                                        (Prims.of_int (14))
                                        (Prims.of_int (302))
                                        (Prims.of_int (69))))))))
               | FStar_Tactics_Result.Failed (e,ps') ->
                   FStar_Tactics_Result.Failed (e, ps'))
  
let quote_vm :
  'Aa 'Ab .
    FStar_Reflection_Types.term ->
      FStar_Reflection_Types.term ->
        ('Aa ->
           (FStar_Reflection_Types.term,unit)
             FStar_Tactics_Effect._dm4f_TAC_repr)
          ->
          ('Ab ->
             (FStar_Reflection_Types.term,unit)
               FStar_Tactics_Effect._dm4f_TAC_repr)
            ->
            ('Aa,'Ab) vmap ->
              (FStar_Reflection_Types.term,unit)
                FStar_Tactics_Effect._dm4f_TAC_repr
  =
  fun ta  ->
    fun tb  ->
      fun quotea  ->
        fun quoteb  ->
          fun vm  ->
            fun ps  ->
              match () with
              | () ->
                  (match () with
                   | () ->
                       (match () with
                        | () ->
                            (match () with
                             | () ->
                                 (match (quote_list
                                           (FStar_Reflection_Derived.mk_e_app
                                              (FStar_Reflection_Basic.pack_ln
                                                 (FStar_Reflection_Data.Tv_FVar
                                                    (FStar_Reflection_Basic.pack_fv
                                                       ["FStar";
                                                       "Pervasives";
                                                       "Native";
                                                       "tuple2"])))
                                              [FStar_Reflection_Basic.pack_ln
                                                 (FStar_Reflection_Data.Tv_FVar
                                                    (FStar_Reflection_Basic.pack_fv
                                                       ["Prims"; "nat"]));
                                              FStar_Reflection_Derived.mk_e_app
                                                (FStar_Reflection_Basic.pack_ln
                                                   (FStar_Reflection_Data.Tv_FVar
                                                      (FStar_Reflection_Basic.pack_fv
                                                         ["FStar";
                                                         "Pervasives";
                                                         "Native";
                                                         "tuple2"])))
                                                [ta; tb]])
                                           (fun p  ->
                                              fun ps1  ->
                                                match match match match 
                                                                    match 
                                                                    (FStar_Tactics_Builtins.pack
                                                                    (FStar_Reflection_Data.Tv_Const
                                                                    (FStar_Reflection_Data.C_Int
                                                                    (FStar_Pervasives_Native.fst
                                                                    p))))
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps1
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (311))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (313))
                                                                    (Prims.of_int (39))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (311))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (313))
                                                                    (Prims.of_int (39))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (311))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (313))
                                                                    (Prims.of_int (39))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (312))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (312))
                                                                    (Prims.of_int (51))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (312))
                                                                    (Prims.of_int (7))
                                                                    (Prims.of_int (312))
                                                                    (Prims.of_int (38))))))
                                                                    with
                                                                    | 
                                                                    FStar_Tactics_Result.Success
                                                                    (a,ps')
                                                                    ->
                                                                    (match ()
                                                                    with
                                                                    | 
                                                                    () ->
                                                                    FStar_Tactics_Result.Success
                                                                    ((a,
                                                                    FStar_Reflection_Data.Q_Explicit),
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (312))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (312))
                                                                    (Prims.of_int (51))))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e,ps')
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps')
                                                                  with
                                                                  | FStar_Tactics_Result.Success
                                                                    (a,ps')
                                                                    ->
                                                                    (match ()
                                                                    with
                                                                    | 
                                                                    () ->
                                                                    (match 
                                                                    match 
                                                                    match 
                                                                    match 
                                                                    match 
                                                                    match 
                                                                    match 
                                                                    match 
                                                                    (quotea
                                                                    (FStar_Pervasives_Native.fst
                                                                    (FStar_Pervasives_Native.snd
                                                                    p)))
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
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
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (311))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (313))
                                                                    (Prims.of_int (39))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (311))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (313))
                                                                    (Prims.of_int (39))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (313))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (313))
                                                                    (Prims.of_int (38))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (313))
                                                                    (Prims.of_int (7))
                                                                    (Prims.of_int (313))
                                                                    (Prims.of_int (25))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (307))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (308))
                                                                    (Prims.of_int (70))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (307))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (308))
                                                                    (Prims.of_int (70))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (307))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (308))
                                                                    (Prims.of_int (70))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (308))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (308))
                                                                    (Prims.of_int (39))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (308))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (308))
                                                                    (Prims.of_int (26))))))
                                                                    with
                                                                    | 
                                                                    FStar_Tactics_Result.Success
                                                                    (a1,ps'1)
                                                                    ->
                                                                    (match ()
                                                                    with
                                                                    | 
                                                                    () ->
                                                                    FStar_Tactics_Result.Success
                                                                    ((a1,
                                                                    FStar_Reflection_Data.Q_Explicit),
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'1
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (308))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (308))
                                                                    (Prims.of_int (39))))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e,ps'1)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'1)
                                                                    with
                                                                    | 
                                                                    FStar_Tactics_Result.Success
                                                                    (a1,ps'1)
                                                                    ->
                                                                    (match ()
                                                                    with
                                                                    | 
                                                                    () ->
                                                                    (match 
                                                                    match 
                                                                    match 
                                                                    (quoteb
                                                                    (FStar_Pervasives_Native.snd
                                                                    (FStar_Pervasives_Native.snd
                                                                    p)))
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'1
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (307))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (308))
                                                                    (Prims.of_int (70))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (307))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (308))
                                                                    (Prims.of_int (70))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (308))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (308))
                                                                    (Prims.of_int (69))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (308))
                                                                    (Prims.of_int (42))
                                                                    (Prims.of_int (308))
                                                                    (Prims.of_int (56))))))
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
                                                                    ((a2,
                                                                    FStar_Reflection_Data.Q_Explicit),
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (308))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (308))
                                                                    (Prims.of_int (69))))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e,ps'2)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'2)
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
                                                                    ([a2],
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (307))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (308))
                                                                    (Prims.of_int (70))))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e,ps'2)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'2)
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
                                                                    ((a1 ::
                                                                    a2),
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (307))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (308))
                                                                    (Prims.of_int (70))))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e,ps'2)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'2)))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e,ps'1)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'1)
                                                                    with
                                                                    | 
                                                                    FStar_Tactics_Result.Success
                                                                    (a1,ps'1)
                                                                    ->
                                                                    (match ()
                                                                    with
                                                                    | 
                                                                    () ->
                                                                    FStar_Tactics_Result.Success
                                                                    (((tb,
                                                                    FStar_Reflection_Data.Q_Implicit)
                                                                    :: a1),
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'1
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (307))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (308))
                                                                    (Prims.of_int (70))))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e,ps'1)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'1)
                                                                    with
                                                                    | 
                                                                    FStar_Tactics_Result.Success
                                                                    (a1,ps'1)
                                                                    ->
                                                                    (match ()
                                                                    with
                                                                    | 
                                                                    () ->
                                                                    FStar_Tactics_Result.Success
                                                                    (((ta,
                                                                    FStar_Reflection_Data.Q_Implicit)
                                                                    :: a1),
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'1
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (307))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (308))
                                                                    (Prims.of_int (70))))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e,ps'1)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'1)
                                                                    with
                                                                    | 
                                                                    FStar_Tactics_Result.Success
                                                                    (a1,ps'1)
                                                                    ->
                                                                    (match ()
                                                                    with
                                                                    | 
                                                                    () ->
                                                                    FStar_Tactics_Result.Success
                                                                    ((FStar_Reflection_Derived.mk_app
                                                                    (FStar_Reflection_Basic.pack_ln
                                                                    (FStar_Reflection_Data.Tv_FVar
                                                                    (FStar_Reflection_Basic.pack_fv
                                                                    ["FStar";
                                                                    "Pervasives";
                                                                    "Native";
                                                                    "Mktuple2"])))
                                                                    a1),
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'1
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (307))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (308))
                                                                    (Prims.of_int (70))))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e,ps'1)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'1)
                                                                    with
                                                                    | 
                                                                    FStar_Tactics_Result.Success
                                                                    (a1,ps'1)
                                                                    ->
                                                                    (match ()
                                                                    with
                                                                    | 
                                                                    () ->
                                                                    FStar_Tactics_Result.Success
                                                                    ((a1,
                                                                    FStar_Reflection_Data.Q_Explicit),
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'1
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (313))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (313))
                                                                    (Prims.of_int (38))))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e,ps'1)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'1)
                                                                    with
                                                                    | 
                                                                    FStar_Tactics_Result.Success
                                                                    (a1,ps'1)
                                                                    ->
                                                                    (match ()
                                                                    with
                                                                    | 
                                                                    () ->
                                                                    FStar_Tactics_Result.Success
                                                                    ([a1],
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'1
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (311))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (313))
                                                                    (Prims.of_int (39))))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e,ps'1)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'1)
                                                                    with
                                                                    | 
                                                                    FStar_Tactics_Result.Success
                                                                    (a1,ps'1)
                                                                    ->
                                                                    (match ()
                                                                    with
                                                                    | 
                                                                    () ->
                                                                    FStar_Tactics_Result.Success
                                                                    ((a ::
                                                                    a1),
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'1
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (311))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (313))
                                                                    (Prims.of_int (39))))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e,ps'1)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'1)))
                                                                  | FStar_Tactics_Result.Failed
                                                                    (e,ps')
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps')
                                                            with
                                                            | FStar_Tactics_Result.Success
                                                                (a,ps') ->
                                                                (match ()
                                                                 with
                                                                 | () ->
                                                                    FStar_Tactics_Result.Success
                                                                    ((((FStar_Reflection_Derived.mk_e_app
                                                                    (FStar_Reflection_Basic.pack_ln
                                                                    (FStar_Reflection_Data.Tv_FVar
                                                                    (FStar_Reflection_Basic.pack_fv
                                                                    ["FStar";
                                                                    "Pervasives";
                                                                    "Native";
                                                                    "tuple2"])))
                                                                    [ta; tb]),
                                                                    FStar_Reflection_Data.Q_Implicit)
                                                                    :: a),
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (311))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (313))
                                                                    (Prims.of_int (39))))))))
                                                            | FStar_Tactics_Result.Failed
                                                                (e,ps') ->
                                                                FStar_Tactics_Result.Failed
                                                                  (e, ps')
                                                      with
                                                      | FStar_Tactics_Result.Success
                                                          (a,ps') ->
                                                          (match () with
                                                           | () ->
                                                               FStar_Tactics_Result.Success
                                                                 ((((FStar_Reflection_Basic.pack_ln
                                                                    (FStar_Reflection_Data.Tv_FVar
                                                                    (FStar_Reflection_Basic.pack_fv
                                                                    ["Prims";
                                                                    "nat"]))),
                                                                    FStar_Reflection_Data.Q_Implicit)
                                                                   :: a),
                                                                   (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (311))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (313))
                                                                    (Prims.of_int (39))))))))
                                                      | FStar_Tactics_Result.Failed
                                                          (e,ps') ->
                                                          FStar_Tactics_Result.Failed
                                                            (e, ps')
                                                with
                                                | FStar_Tactics_Result.Success
                                                    (a,ps') ->
                                                    (match () with
                                                     | () ->
                                                         FStar_Tactics_Result.Success
                                                           ((FStar_Reflection_Derived.mk_app
                                                               (FStar_Reflection_Basic.pack_ln
                                                                  (FStar_Reflection_Data.Tv_FVar
                                                                    (FStar_Reflection_Basic.pack_fv
                                                                    ["FStar";
                                                                    "Pervasives";
                                                                    "Native";
                                                                    "Mktuple2"])))
                                                               a),
                                                             (FStar_Tactics_Types.decr_depth
                                                                (FStar_Tactics_Types.set_proofstate_range
                                                                   ps'
                                                                   (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (311))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (313))
                                                                    (Prims.of_int (39))))))))
                                                | FStar_Tactics_Result.Failed
                                                    (e,ps') ->
                                                    FStar_Tactics_Result.Failed
                                                      (e, ps'))
                                           (FStar_Pervasives_Native.fst vm))
                                          (FStar_Tactics_Types.incr_depth
                                             (FStar_Tactics_Types.set_proofstate_range
                                                (FStar_Tactics_Types.decr_depth
                                                   (FStar_Tactics_Types.set_proofstate_range
                                                      (FStar_Tactics_Types.incr_depth
                                                         (FStar_Tactics_Types.set_proofstate_range
                                                            (FStar_Tactics_Types.decr_depth
                                                               (FStar_Tactics_Types.set_proofstate_range
                                                                  (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (307))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (308))
                                                                    (Prims.of_int (70))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (309))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (322))
                                                                    (Prims.of_int (63))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (309))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (309))
                                                                    (Prims.of_int (45))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (310))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (322))
                                                                    (Prims.of_int (63))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (311))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (313))
                                                                    (Prims.of_int (39))))))
                                                                  (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (314))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (322))
                                                                    (Prims.of_int (63))))))
                                                            (FStar_Range.prims_to_fstar_range
                                                               (Prims.mk_range
                                                                  "FStar.Tactics.CanonCommMonoid.fst"
                                                                  (Prims.of_int (314))
                                                                  (Prims.of_int (16))
                                                                  (Prims.of_int (314))
                                                                  (Prims.of_int (55))))))
                                                      (FStar_Range.prims_to_fstar_range
                                                         (Prims.mk_range
                                                            "FStar.Tactics.CanonCommMonoid.fst"
                                                            (Prims.of_int (315))
                                                            (Prims.of_int (2))
                                                            (Prims.of_int (322))
                                                            (Prims.of_int (63))))))
                                                (FStar_Range.prims_to_fstar_range
                                                   (Prims.mk_range
                                                      "FStar.Tactics.CanonCommMonoid.fst"
                                                      (Prims.of_int (315))
                                                      (Prims.of_int (14))
                                                      (Prims.of_int (315))
                                                      (Prims.of_int (57))))))
                                  with
                                  | FStar_Tactics_Result.Success (a,ps') ->
                                      (match () with
                                       | () ->
                                           (match match match match match 
                                                                    match 
                                                                    (quotea
                                                                    (FStar_Pervasives_Native.fst
                                                                    (FStar_Pervasives_Native.snd
                                                                    vm)))
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
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
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (317))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (322))
                                                                    (Prims.of_int (63))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (317))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (317))
                                                                    (Prims.of_int (33))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (307))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (308))
                                                                    (Prims.of_int (70))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (307))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (308))
                                                                    (Prims.of_int (70))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (307))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (308))
                                                                    (Prims.of_int (70))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (308))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (308))
                                                                    (Prims.of_int (39))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (308))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (308))
                                                                    (Prims.of_int (26))))))
                                                                    with
                                                                    | 
                                                                    FStar_Tactics_Result.Success
                                                                    (a1,ps'1)
                                                                    ->
                                                                    (match ()
                                                                    with
                                                                    | 
                                                                    () ->
                                                                    FStar_Tactics_Result.Success
                                                                    ((a1,
                                                                    FStar_Reflection_Data.Q_Explicit),
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'1
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (308))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (308))
                                                                    (Prims.of_int (39))))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e,ps'1)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'1)
                                                                    with
                                                                    | 
                                                                    FStar_Tactics_Result.Success
                                                                    (a1,ps'1)
                                                                    ->
                                                                    (match ()
                                                                    with
                                                                    | 
                                                                    () ->
                                                                    (match 
                                                                    match 
                                                                    match 
                                                                    (quoteb
                                                                    (FStar_Pervasives_Native.snd
                                                                    (FStar_Pervasives_Native.snd
                                                                    vm)))
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'1
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (307))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (308))
                                                                    (Prims.of_int (70))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (307))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (308))
                                                                    (Prims.of_int (70))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (308))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (308))
                                                                    (Prims.of_int (69))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (308))
                                                                    (Prims.of_int (42))
                                                                    (Prims.of_int (308))
                                                                    (Prims.of_int (56))))))
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
                                                                    ((a2,
                                                                    FStar_Reflection_Data.Q_Explicit),
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (308))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (308))
                                                                    (Prims.of_int (69))))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e,ps'2)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'2)
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
                                                                    ([a2],
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (307))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (308))
                                                                    (Prims.of_int (70))))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e,ps'2)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'2)
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
                                                                    ((a1 ::
                                                                    a2),
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (307))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (308))
                                                                    (Prims.of_int (70))))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e,ps'2)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'2)))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e,ps'1)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'1)
                                                              with
                                                              | FStar_Tactics_Result.Success
                                                                  (a1,ps'1)
                                                                  ->
                                                                  (match ()
                                                                   with
                                                                   | 
                                                                   () ->
                                                                    FStar_Tactics_Result.Success
                                                                    (((tb,
                                                                    FStar_Reflection_Data.Q_Implicit)
                                                                    :: a1),
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'1
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (307))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (308))
                                                                    (Prims.of_int (70))))))))
                                                              | FStar_Tactics_Result.Failed
                                                                  (e,ps'1) ->
                                                                  FStar_Tactics_Result.Failed
                                                                    (e, ps'1)
                                                        with
                                                        | FStar_Tactics_Result.Success
                                                            (a1,ps'1) ->
                                                            (match () with
                                                             | () ->
                                                                 FStar_Tactics_Result.Success
                                                                   (((ta,
                                                                    FStar_Reflection_Data.Q_Implicit)
                                                                    :: a1),
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'1
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (307))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (308))
                                                                    (Prims.of_int (70))))))))
                                                        | FStar_Tactics_Result.Failed
                                                            (e,ps'1) ->
                                                            FStar_Tactics_Result.Failed
                                                              (e, ps'1)
                                                  with
                                                  | FStar_Tactics_Result.Success
                                                      (a1,ps'1) ->
                                                      (match () with
                                                       | () ->
                                                           FStar_Tactics_Result.Success
                                                             ((FStar_Reflection_Derived.mk_app
                                                                 (FStar_Reflection_Basic.pack_ln
                                                                    (
                                                                    FStar_Reflection_Data.Tv_FVar
                                                                    (FStar_Reflection_Basic.pack_fv
                                                                    ["FStar";
                                                                    "Pervasives";
                                                                    "Native";
                                                                    "Mktuple2"])))
                                                                 a1),
                                                               (FStar_Tactics_Types.decr_depth
                                                                  (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'1
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (307))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (308))
                                                                    (Prims.of_int (70))))))))
                                                  | FStar_Tactics_Result.Failed
                                                      (e,ps'1) ->
                                                      FStar_Tactics_Result.Failed
                                                        (e, ps'1)
                                            with
                                            | FStar_Tactics_Result.Success
                                                (a1,ps'1) ->
                                                (match () with
                                                 | () ->
                                                     FStar_Tactics_Result.Success
                                                       ((FStar_Reflection_Derived.mk_app
                                                           (FStar_Reflection_Basic.pack_ln
                                                              (FStar_Reflection_Data.Tv_FVar
                                                                 (FStar_Reflection_Basic.pack_fv
                                                                    ["FStar";
                                                                    "Pervasives";
                                                                    "Native";
                                                                    "Mktuple2"])))
                                                           [((FStar_Reflection_Derived.mk_e_app
                                                                (FStar_Reflection_Basic.pack_ln
                                                                   (FStar_Reflection_Data.Tv_FVar
                                                                    (FStar_Reflection_Basic.pack_fv
                                                                    ["Prims";
                                                                    "list"])))
                                                                [FStar_Reflection_Derived.mk_e_app
                                                                   (FStar_Reflection_Basic.pack_ln
                                                                    (FStar_Reflection_Data.Tv_FVar
                                                                    (FStar_Reflection_Basic.pack_fv
                                                                    ["FStar";
                                                                    "Pervasives";
                                                                    "Native";
                                                                    "tuple2"])))
                                                                   [FStar_Reflection_Basic.pack_ln
                                                                    (FStar_Reflection_Data.Tv_FVar
                                                                    (FStar_Reflection_Basic.pack_fv
                                                                    ["Prims";
                                                                    "nat"]));
                                                                   FStar_Reflection_Derived.mk_e_app
                                                                    (FStar_Reflection_Basic.pack_ln
                                                                    (FStar_Reflection_Data.Tv_FVar
                                                                    (FStar_Reflection_Basic.pack_fv
                                                                    ["FStar";
                                                                    "Pervasives";
                                                                    "Native";
                                                                    "tuple2"])))
                                                                    [ta; tb]]]),
                                                              FStar_Reflection_Data.Q_Implicit);
                                                           ((FStar_Reflection_Derived.mk_e_app
                                                               (FStar_Reflection_Basic.pack_ln
                                                                  (FStar_Reflection_Data.Tv_FVar
                                                                    (FStar_Reflection_Basic.pack_fv
                                                                    ["FStar";
                                                                    "Pervasives";
                                                                    "Native";
                                                                    "tuple2"])))
                                                               [ta; tb]),
                                                             FStar_Reflection_Data.Q_Implicit);
                                                           (a,
                                                             FStar_Reflection_Data.Q_Explicit);
                                                           (a1,
                                                             FStar_Reflection_Data.Q_Explicit)]),
                                                         (FStar_Tactics_Types.decr_depth
                                                            (FStar_Tactics_Types.set_proofstate_range
                                                               ps'1
                                                               (FStar_Range.prims_to_fstar_range
                                                                  (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (321))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (322))
                                                                    (Prims.of_int (63))))))))
                                            | FStar_Tactics_Result.Failed
                                                (e,ps'1) ->
                                                FStar_Tactics_Result.Failed
                                                  (e, ps'1)))
                                  | FStar_Tactics_Result.Failed (e,ps') ->
                                      FStar_Tactics_Result.Failed (e, ps')))))
  
let rec (quote_exp :
  exp ->
    (FStar_Reflection_Types.term,unit) FStar_Tactics_Effect._dm4f_TAC_repr)
  =
  fun e  ->
    match e with
    | Unit  ->
        (fun s  ->
           FStar_Tactics_Result.Success
             ((FStar_Reflection_Basic.pack_ln
                 (FStar_Reflection_Data.Tv_FVar
                    (FStar_Reflection_Basic.pack_fv
                       ["FStar"; "Tactics"; "CanonCommMonoid"; "Unit"]))), s))
    | Var x ->
        (fun ps  ->
           match match (FStar_Tactics_Builtins.pack
                          (FStar_Reflection_Data.Tv_Const
                             (FStar_Reflection_Data.C_Int x)))
                         (FStar_Tactics_Types.incr_depth
                            (FStar_Tactics_Types.set_proofstate_range
                               (FStar_Tactics_Types.incr_depth
                                  (FStar_Tactics_Types.set_proofstate_range
                                     ps
                                     (FStar_Range.prims_to_fstar_range
                                        (Prims.mk_range
                                           "FStar.Tactics.CanonCommMonoid.fst"
                                           (Prims.of_int (327))
                                           (Prims.of_int (29))
                                           (Prims.of_int (327))
                                           (Prims.of_int (56))))))
                               (FStar_Range.prims_to_fstar_range
                                  (Prims.mk_range
                                     "FStar.Tactics.CanonCommMonoid.fst"
                                     (Prims.of_int (327)) (Prims.of_int (30))
                                     (Prims.of_int (327)) (Prims.of_int (55))))))
                 with
                 | FStar_Tactics_Result.Success (a,ps') ->
                     (match () with
                      | () ->
                          FStar_Tactics_Result.Success
                            ([a],
                              (FStar_Tactics_Types.decr_depth
                                 (FStar_Tactics_Types.set_proofstate_range
                                    ps'
                                    (FStar_Range.prims_to_fstar_range
                                       (Prims.mk_range
                                          "FStar.Tactics.CanonCommMonoid.fst"
                                          (Prims.of_int (327))
                                          (Prims.of_int (29))
                                          (Prims.of_int (327))
                                          (Prims.of_int (56))))))))
                 | FStar_Tactics_Result.Failed (e1,ps') ->
                     FStar_Tactics_Result.Failed (e1, ps')
           with
           | FStar_Tactics_Result.Success (a,ps') ->
               (match () with
                | () ->
                    FStar_Tactics_Result.Success
                      ((FStar_Reflection_Derived.mk_e_app
                          (FStar_Reflection_Basic.pack_ln
                             (FStar_Reflection_Data.Tv_FVar
                                (FStar_Reflection_Basic.pack_fv
                                   ["FStar";
                                   "Tactics";
                                   "CanonCommMonoid";
                                   "Var"]))) a),
                        (FStar_Tactics_Types.decr_depth
                           (FStar_Tactics_Types.set_proofstate_range ps'
                              (FStar_Range.prims_to_fstar_range
                                 (Prims.mk_range
                                    "FStar.Tactics.CanonCommMonoid.fst"
                                    (Prims.of_int (327)) (Prims.of_int (13))
                                    (Prims.of_int (327)) (Prims.of_int (56))))))))
           | FStar_Tactics_Result.Failed (e1,ps') ->
               FStar_Tactics_Result.Failed (e1, ps'))
    | Mult (e1,e2) ->
        (fun ps  ->
           match match (quote_exp e1)
                         (FStar_Tactics_Types.incr_depth
                            (FStar_Tactics_Types.set_proofstate_range
                               (FStar_Tactics_Types.incr_depth
                                  (FStar_Tactics_Types.set_proofstate_range
                                     ps
                                     (FStar_Range.prims_to_fstar_range
                                        (Prims.mk_range
                                           "FStar.Tactics.CanonCommMonoid.fst"
                                           (Prims.of_int (328))
                                           (Prims.of_int (35))
                                           (Prims.of_int (328))
                                           (Prims.of_int (63))))))
                               (FStar_Range.prims_to_fstar_range
                                  (Prims.mk_range
                                     "FStar.Tactics.CanonCommMonoid.fst"
                                     (Prims.of_int (328)) (Prims.of_int (36))
                                     (Prims.of_int (328)) (Prims.of_int (48))))))
                 with
                 | FStar_Tactics_Result.Success (a,ps') ->
                     (match () with
                      | () ->
                          (match match (quote_exp e2)
                                         (FStar_Tactics_Types.incr_depth
                                            (FStar_Tactics_Types.set_proofstate_range
                                               (FStar_Tactics_Types.incr_depth
                                                  (FStar_Tactics_Types.set_proofstate_range
                                                     (FStar_Tactics_Types.decr_depth
                                                        (FStar_Tactics_Types.set_proofstate_range
                                                           ps'
                                                           (FStar_Range.prims_to_fstar_range
                                                              (Prims.mk_range
                                                                 "FStar.Tactics.CanonCommMonoid.fst"
                                                                 (Prims.of_int (328))
                                                                 (Prims.of_int (35))
                                                                 (Prims.of_int (328))
                                                                 (Prims.of_int (63))))))
                                                     (FStar_Range.prims_to_fstar_range
                                                        (Prims.mk_range
                                                           "FStar.Tactics.CanonCommMonoid.fst"
                                                           (Prims.of_int (328))
                                                           (Prims.of_int (35))
                                                           (Prims.of_int (328))
                                                           (Prims.of_int (63))))))
                                               (FStar_Range.prims_to_fstar_range
                                                  (Prims.mk_range
                                                     "FStar.Tactics.CanonCommMonoid.fst"
                                                     (Prims.of_int (328))
                                                     (Prims.of_int (50))
                                                     (Prims.of_int (328))
                                                     (Prims.of_int (62))))))
                                 with
                                 | FStar_Tactics_Result.Success (a1,ps'1) ->
                                     (match () with
                                      | () ->
                                          FStar_Tactics_Result.Success
                                            ([a1],
                                              (FStar_Tactics_Types.decr_depth
                                                 (FStar_Tactics_Types.set_proofstate_range
                                                    ps'1
                                                    (FStar_Range.prims_to_fstar_range
                                                       (Prims.mk_range
                                                          "FStar.Tactics.CanonCommMonoid.fst"
                                                          (Prims.of_int (328))
                                                          (Prims.of_int (35))
                                                          (Prims.of_int (328))
                                                          (Prims.of_int (63))))))))
                                 | FStar_Tactics_Result.Failed (e3,ps'1) ->
                                     FStar_Tactics_Result.Failed (e3, ps'1)
                           with
                           | FStar_Tactics_Result.Success (a1,ps'1) ->
                               (match () with
                                | () ->
                                    FStar_Tactics_Result.Success
                                      ((a :: a1),
                                        (FStar_Tactics_Types.decr_depth
                                           (FStar_Tactics_Types.set_proofstate_range
                                              ps'1
                                              (FStar_Range.prims_to_fstar_range
                                                 (Prims.mk_range
                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                    (Prims.of_int (328))
                                                    (Prims.of_int (35))
                                                    (Prims.of_int (328))
                                                    (Prims.of_int (63))))))))
                           | FStar_Tactics_Result.Failed (e3,ps'1) ->
                               FStar_Tactics_Result.Failed (e3, ps'1)))
                 | FStar_Tactics_Result.Failed (e3,ps') ->
                     FStar_Tactics_Result.Failed (e3, ps')
           with
           | FStar_Tactics_Result.Success (a,ps') ->
               (match () with
                | () ->
                    FStar_Tactics_Result.Success
                      ((FStar_Reflection_Derived.mk_e_app
                          (FStar_Reflection_Basic.pack_ln
                             (FStar_Reflection_Data.Tv_FVar
                                (FStar_Reflection_Basic.pack_fv
                                   ["FStar";
                                   "Tactics";
                                   "CanonCommMonoid";
                                   "Mult"]))) a),
                        (FStar_Tactics_Types.decr_depth
                           (FStar_Tactics_Types.set_proofstate_range ps'
                              (FStar_Range.prims_to_fstar_range
                                 (Prims.mk_range
                                    "FStar.Tactics.CanonCommMonoid.fst"
                                    (Prims.of_int (328)) (Prims.of_int (18))
                                    (Prims.of_int (328)) (Prims.of_int (63))))))))
           | FStar_Tactics_Result.Failed (e3,ps') ->
               FStar_Tactics_Result.Failed (e3, ps'))
  
let canon_monoid_aux :
  'Aa 'Ab .
    FStar_Reflection_Types.term ->
      (FStar_Reflection_Types.term ->
         ('Aa,unit) FStar_Tactics_Effect._dm4f_TAC_repr)
        ->
        ('Aa ->
           (FStar_Reflection_Types.term,unit)
             FStar_Tactics_Effect._dm4f_TAC_repr)
          ->
          FStar_Reflection_Types.term ->
            FStar_Reflection_Types.term ->
              FStar_Reflection_Types.term ->
                'Aa ->
                  FStar_Reflection_Types.term ->
                    ('Ab ->
                       (FStar_Reflection_Types.term,unit)
                         FStar_Tactics_Effect._dm4f_TAC_repr)
                      ->
                      (FStar_Reflection_Types.term ->
                         ('Ab,unit) FStar_Tactics_Effect._dm4f_TAC_repr)
                        ->
                        'Ab ->
                          FStar_Reflection_Types.term ->
                            FStar_Reflection_Types.term ->
                              (unit,unit) FStar_Tactics_Effect._dm4f_TAC_repr
  =
  fun ta  ->
    fun unquotea  ->
      fun quotea  ->
        fun tm  ->
          fun tmult  ->
            fun tunit  ->
              fun munit  ->
                fun tb  ->
                  fun quoteb  ->
                    fun f  ->
                      fun def  ->
                        fun tp  ->
                          fun tpc  ->
                            fun ps  ->
                              match (FStar_Tactics_Builtins.norm [])
                                      (FStar_Tactics_Types.incr_depth
                                         (FStar_Tactics_Types.set_proofstate_range
                                            ps
                                            (FStar_Range.prims_to_fstar_range
                                               (Prims.mk_range
                                                  "FStar.Tactics.CanonCommMonoid.fst"
                                                  (Prims.of_int (335))
                                                  (Prims.of_int (2))
                                                  (Prims.of_int (335))
                                                  (Prims.of_int (9))))))
                              with
                              | FStar_Tactics_Result.Success (a,ps') ->
                                  (match () with
                                   | () ->
                                       (match match (FStar_Tactics_Derived.cur_goal
                                                       ())
                                                      (FStar_Tactics_Types.incr_depth
                                                         (FStar_Tactics_Types.set_proofstate_range
                                                            (FStar_Tactics_Types.incr_depth
                                                               (FStar_Tactics_Types.set_proofstate_range
                                                                  (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (336))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (407))
                                                                    (Prims.of_int (42))))))
                                                                  (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (336))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (336))
                                                                    (Prims.of_int (37))))))
                                                            (FStar_Range.prims_to_fstar_range
                                                               (Prims.mk_range
                                                                  "FStar.Tactics.CanonCommMonoid.fst"
                                                                  (Prims.of_int (336))
                                                                  (Prims.of_int (24))
                                                                  (Prims.of_int (336))
                                                                  (Prims.of_int (37))))))
                                              with
                                              | FStar_Tactics_Result.Success
                                                  (a1,ps'1) ->
                                                  (match () with
                                                   | () ->
                                                       (FStar_Reflection_Formula.term_as_formula
                                                          a1)
                                                         (FStar_Tactics_Types.decr_depth
                                                            (FStar_Tactics_Types.set_proofstate_range
                                                               ps'1
                                                               (FStar_Range.prims_to_fstar_range
                                                                  (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (336))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (336))
                                                                    (Prims.of_int (37)))))))
                                              | FStar_Tactics_Result.Failed
                                                  (e,ps'1) ->
                                                  FStar_Tactics_Result.Failed
                                                    (e, ps'1)
                                        with
                                        | FStar_Tactics_Result.Success
                                            (a1,ps'1) ->
                                            (match () with
                                             | () ->
                                                 ((match a1 with
                                                   | FStar_Reflection_Formula.Comp
                                                       (FStar_Reflection_Formula.Eq
                                                        (FStar_Pervasives_Native.Some
                                                        t),t1,t2)
                                                       ->
                                                       if
                                                         FStar_Reflection_Basic.term_eq
                                                           t ta
                                                       then
                                                         (fun ps1  ->
                                                            match Obj.magic
                                                                    (
                                                                    (reification
                                                                    f def ()
                                                                    (fun a1 
                                                                    ->
                                                                    (Obj.magic
                                                                    unquotea)
                                                                    a1)
                                                                    (fun a2 
                                                                    ->
                                                                    (Obj.magic
                                                                    quotea)
                                                                    a2) tmult
                                                                    tunit
                                                                    (Obj.magic
                                                                    munit)
                                                                    [t1; t2])
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps1
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (341))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (341))
                                                                    (Prims.of_int (75)))))))
                                                            with
                                                            | FStar_Tactics_Result.Success
                                                                (a2,ps'2) ->
                                                                (match ()
                                                                 with
                                                                 | () ->
                                                                    ((match a2
                                                                    with
                                                                    | (r1::r2::[],vm)
                                                                    ->
                                                                    (fun ps2 
                                                                    ->
                                                                    match 
                                                                    (quote_vm
                                                                    ta tb
                                                                    quotea
                                                                    quoteb vm)
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (349))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (349))
                                                                    (Prims.of_int (51))))))
                                                                    with
                                                                    | 
                                                                    FStar_Tactics_Result.Success
                                                                    (a3,ps'3)
                                                                    ->
                                                                    (match ()
                                                                    with
                                                                    | 
                                                                    () ->
                                                                    (match 
                                                                    (quote_exp
                                                                    r1)
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (350))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (402))
                                                                    (Prims.of_int (36))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (350))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (350))
                                                                    (Prims.of_int (32))))))
                                                                    with
                                                                    | 
                                                                    FStar_Tactics_Result.Success
                                                                    (a4,ps'4)
                                                                    ->
                                                                    (match ()
                                                                    with
                                                                    | 
                                                                    () ->
                                                                    (match 
                                                                    (quote_exp
                                                                    r2)
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'4
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (351))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (402))
                                                                    (Prims.of_int (36))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (351))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (351))
                                                                    (Prims.of_int (32))))))
                                                                    with
                                                                    | 
                                                                    FStar_Tactics_Result.Success
                                                                    (a5,ps'5)
                                                                    ->
                                                                    (match ()
                                                                    with
                                                                    | 
                                                                    () ->
                                                                    (match ()
                                                                    with
                                                                    | 
                                                                    () ->
                                                                    (match 
                                                                    (FStar_Tactics_Derived.change_sq
                                                                    (FStar_Reflection_Derived.mk_app
                                                                    (FStar_Reflection_Basic.pack_ln
                                                                    (FStar_Reflection_Data.Tv_FVar
                                                                    (FStar_Reflection_Basic.pack_fv
                                                                    ["Prims";
                                                                    "eq2"])))
                                                                    [
                                                                    (ta,
                                                                    FStar_Reflection_Data.Q_Implicit);
                                                                    ((FStar_Reflection_Derived.mk_app
                                                                    (FStar_Reflection_Basic.pack_ln
                                                                    (FStar_Reflection_Data.Tv_FVar
                                                                    (FStar_Reflection_Basic.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "CanonCommMonoid";
                                                                    "mdenote"])))
                                                                    [
                                                                    (ta,
                                                                    FStar_Reflection_Data.Q_Implicit);
                                                                    (tb,
                                                                    FStar_Reflection_Data.Q_Implicit);
                                                                    (tm,
                                                                    FStar_Reflection_Data.Q_Explicit);
                                                                    (a3,
                                                                    FStar_Reflection_Data.Q_Explicit);
                                                                    (a4,
                                                                    FStar_Reflection_Data.Q_Explicit)]),
                                                                    FStar_Reflection_Data.Q_Explicit);
                                                                    ((FStar_Reflection_Derived.mk_app
                                                                    (FStar_Reflection_Basic.pack_ln
                                                                    (FStar_Reflection_Data.Tv_FVar
                                                                    (FStar_Reflection_Basic.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "CanonCommMonoid";
                                                                    "mdenote"])))
                                                                    [
                                                                    (ta,
                                                                    FStar_Reflection_Data.Q_Implicit);
                                                                    (tb,
                                                                    FStar_Reflection_Data.Q_Implicit);
                                                                    (tm,
                                                                    FStar_Reflection_Data.Q_Explicit);
                                                                    (a3,
                                                                    FStar_Reflection_Data.Q_Explicit);
                                                                    (a5,
                                                                    FStar_Reflection_Data.Q_Explicit)]),
                                                                    FStar_Reflection_Data.Q_Explicit)]))
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'5
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (352))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (402))
                                                                    (Prims.of_int (36))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (352))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (357))
                                                                    (Prims.of_int (83))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (358))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (402))
                                                                    (Prims.of_int (36))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (358))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (358))
                                                                    (Prims.of_int (23))))))
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
                                                                    (FStar_Tactics_Derived.mapply
                                                                    (FStar_Reflection_Derived.mk_app
                                                                    (FStar_Reflection_Basic.pack_ln
                                                                    (FStar_Reflection_Data.Tv_FVar
                                                                    (FStar_Reflection_Basic.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "CanonCommMonoid";
                                                                    "monoid_reflect"])))
                                                                    [
                                                                    (ta,
                                                                    FStar_Reflection_Data.Q_Implicit);
                                                                    (tb,
                                                                    FStar_Reflection_Data.Q_Implicit);
                                                                    (tp,
                                                                    FStar_Reflection_Data.Q_Explicit);
                                                                    (tpc,
                                                                    FStar_Reflection_Data.Q_Explicit)]))
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'6
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (366))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (402))
                                                                    (Prims.of_int (36))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (366))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (369))
                                                                    (Prims.of_int (63))))))
                                                                    with
                                                                    | 
                                                                    FStar_Tactics_Result.Success
                                                                    (a7,ps'7)
                                                                    ->
                                                                    (match ()
                                                                    with
                                                                    | 
                                                                    () ->
                                                                    (match 
                                                                    (unfold_topdown
                                                                    [
                                                                    FStar_Reflection_Basic.pack_ln
                                                                    (FStar_Reflection_Data.Tv_FVar
                                                                    (FStar_Reflection_Basic.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "CanonCommMonoid";
                                                                    "canon"]));
                                                                    FStar_Reflection_Basic.pack_ln
                                                                    (FStar_Reflection_Data.Tv_FVar
                                                                    (FStar_Reflection_Basic.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "CanonCommMonoid";
                                                                    "xsdenote"]));
                                                                    tp])
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'7
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (371))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (402))
                                                                    (Prims.of_int (36))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (371))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (371))
                                                                    (Prims.of_int (52))))))
                                                                    with
                                                                    | 
                                                                    FStar_Tactics_Result.Success
                                                                    (a8,ps'8)
                                                                    ->
                                                                    (match ()
                                                                    with
                                                                    | 
                                                                    () ->
                                                                    (FStar_Tactics_Builtins.norm
                                                                    [
                                                                    FStar_Pervasives.delta_only
                                                                    ["FStar.Tactics.CanonCommMonoid.canon";
                                                                    "FStar.Tactics.CanonCommMonoid.xsdenote";
                                                                    "FStar.Tactics.CanonCommMonoid.flatten";
                                                                    "FStar.Tactics.CanonCommMonoid.select";
                                                                    "FStar.Tactics.CanonCommMonoid.select_extra";
                                                                    "FStar.Tactics.CanonCommMonoid.quote_list";
                                                                    "FStar.Tactics.CanonCommMonoid.quote_vm";
                                                                    "FStar.Tactics.CanonCommMonoid.quote_exp";
                                                                    "FStar.Tactics.CanonCommMonoid.const_compare";
                                                                    "FStar.Tactics.CanonCommMonoid.special_compare";
                                                                    "FStar.List.Tot.Base.assoc";
                                                                    "FStar.Pervasives.Native.fst";
                                                                    "FStar.Pervasives.Native.snd";
                                                                    "FStar.Pervasives.Native.__proj__Mktuple2__item___1";
                                                                    "FStar.Pervasives.Native.__proj__Mktuple2__item___2";
                                                                    "FStar.List.Tot.Base.op_At";
                                                                    "FStar.List.Tot.Base.append";
                                                                    "SL.AutoTactic.compare_b";
                                                                    "SL.AutoTactic.compare_v";
                                                                    "FStar.Order.int_of_order";
                                                                    "FStar.Reflection.Derived.compare_term";
                                                                    "FStar.List.Tot.Base.sortWith";
                                                                    "FStar.List.Tot.Base.partition";
                                                                    "FStar.List.Tot.Base.bool_of_compare";
                                                                    "FStar.List.Tot.Base.compare_of_bool"];
                                                                    FStar_Pervasives.zeta;
                                                                    FStar_Pervasives.iota;
                                                                    FStar_Pervasives.primops])
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'8
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (375))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (402))
                                                                    (Prims.of_int (36)))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e,ps'8)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'8)))
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
                                                                    (e, ps'6))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e,ps'5)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'5)))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e,ps'4)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'4)))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e,ps'3)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'3))
                                                                    | uu____7634
                                                                    ->
                                                                    FStar_Tactics_Derived.fail
                                                                    "Unexpected"))
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (341))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (405))
                                                                    (Prims.of_int (32)))))))
                                                            | FStar_Tactics_Result.Failed
                                                                (e,ps'2) ->
                                                                FStar_Tactics_Result.Failed
                                                                  (e, ps'2))
                                                       else
                                                         FStar_Tactics_Derived.fail
                                                           "Goal should be an equality at the right monoid type"
                                                   | uu____7661 ->
                                                       FStar_Tactics_Derived.fail
                                                         "Goal should be an equality"))
                                                   (FStar_Tactics_Types.decr_depth
                                                      (FStar_Tactics_Types.set_proofstate_range
                                                         ps'1
                                                         (FStar_Range.prims_to_fstar_range
                                                            (Prims.mk_range
                                                               "FStar.Tactics.CanonCommMonoid.fst"
                                                               (Prims.of_int (336))
                                                               (Prims.of_int (2))
                                                               (Prims.of_int (407))
                                                               (Prims.of_int (42)))))))
                                        | FStar_Tactics_Result.Failed
                                            (e,ps'1) ->
                                            FStar_Tactics_Result.Failed
                                              (e, ps'1)))
                              | FStar_Tactics_Result.Failed (e,ps') ->
                                  FStar_Tactics_Result.Failed (e, ps')
  
let canon_monoid_with :
  'Ab .
    (FStar_Reflection_Types.term ->
       ('Ab,unit) FStar_Tactics_Effect._dm4f_TAC_repr)
      ->
      'Ab ->
        'Ab permute ->
          unit ->
            unit ->
              Obj.t FStar_Algebra_CommMonoid.cm ->
                (unit,unit) FStar_Tactics_Effect._dm4f_TAC_repr
  =
  fun f  ->
    fun def  ->
      fun p  ->
        fun pc  ->
          fun a  ->
            fun m  ->
              fun ps  ->
                match () with
                | () ->
                    (match () with
                     | () ->
                         (match () with
                          | () ->
                              (match () with
                               | () ->
                                   (match () with
                                    | () ->
                                        (match () with
                                         | () ->
                                             (match () with
                                              | () ->
                                                  (canon_monoid_aux
                                                     (Obj.magic
                                                        (failwith
                                                           "Cannot evaluate open quotation at runtime"))
                                                     FStar_Tactics_Builtins.unquote
                                                     (fun x  ->
                                                        fun s  ->
                                                          FStar_Tactics_Result.Success
                                                            ((Obj.magic
                                                                (failwith
                                                                   "Cannot evaluate open quotation at runtime")),
                                                              s))
                                                     (Obj.magic
                                                        (failwith
                                                           "Cannot evaluate open quotation at runtime"))
                                                     (Obj.magic
                                                        (failwith
                                                           "Cannot evaluate open quotation at runtime"))
                                                     (Obj.magic
                                                        (failwith
                                                           "Cannot evaluate open quotation at runtime"))
                                                     (FStar_Algebra_CommMonoid.__proj__CM__item__unit
                                                        m)
                                                     (Obj.magic
                                                        (failwith
                                                           "Cannot evaluate open quotation at runtime"))
                                                     (fun x  ->
                                                        fun s  ->
                                                          FStar_Tactics_Result.Success
                                                            ((Obj.magic
                                                                (failwith
                                                                   "Cannot evaluate open quotation at runtime")),
                                                              s)) f def
                                                     (Obj.magic
                                                        (failwith
                                                           "Cannot evaluate open quotation at runtime"))
                                                     (Obj.magic
                                                        (failwith
                                                           "Cannot evaluate open quotation at runtime")))
                                                    (FStar_Tactics_Types.decr_depth
                                                       (FStar_Tactics_Types.set_proofstate_range
                                                          (FStar_Tactics_Types.incr_depth
                                                             (FStar_Tactics_Types.set_proofstate_range
                                                                (FStar_Tactics_Types.decr_depth
                                                                   (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (413))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (413))
                                                                    (Prims.of_int (13))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (412))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (415))
                                                                    (Prims.of_int (63))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (414))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (414))
                                                                    (Prims.of_int (13))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (412))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (415))
                                                                    (Prims.of_int (63))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (414))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (414))
                                                                    (Prims.of_int (34))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (412))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (415))
                                                                    (Prims.of_int (63))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (414))
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (414))
                                                                    (Prims.of_int (55))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (412))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (415))
                                                                    (Prims.of_int (63))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (415))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (415))
                                                                    (Prims.of_int (13))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (412))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (415))
                                                                    (Prims.of_int (63))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (415))
                                                                    (Prims.of_int (43))
                                                                    (Prims.of_int (415))
                                                                    (Prims.of_int (52))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (412))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (415))
                                                                    (Prims.of_int (63))))))
                                                                (FStar_Range.prims_to_fstar_range
                                                                   (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (415))
                                                                    (Prims.of_int (53))
                                                                    (Prims.of_int (415))
                                                                    (Prims.of_int (63))))))
                                                          (FStar_Range.prims_to_fstar_range
                                                             (Prims.mk_range
                                                                "FStar.Tactics.CanonCommMonoid.fst"
                                                                (Prims.of_int (412))
                                                                (Prims.of_int (2))
                                                                (Prims.of_int (415))
                                                                (Prims.of_int (63))))))))))))
  
let canon_monoid :
  'Aa .
    'Aa FStar_Algebra_CommMonoid.cm ->
      (unit,unit) FStar_Tactics_Effect._dm4f_TAC_repr
  =
  fun cm  ->
    canon_monoid_with
      (fun uu____8030  -> fun s  -> FStar_Tactics_Result.Success ((), s)) ()
      (fun a  -> sort ()) () () (Obj.magic cm)
  

let (is_const :
  FStar_Reflection_Types.term ->
    (Prims.bool,unit) FStar_Tactics_Effect._dm4f_TAC_repr)
  =
  fun t  ->
    fun ps  ->
      match (FStar_Tactics_Builtins.inspect t)
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.CanonCommMonoid.fst"
                          (Prims.of_int (433)) (Prims.of_int (45))
                          (Prims.of_int (433)) (Prims.of_int (56))))))
      with
      | FStar_Tactics_Result.Success (a,ps') ->
          (match () with
           | () ->
               FStar_Tactics_Result.Success
                 ((FStar_Reflection_Data.uu___is_Tv_Const a),
                   (FStar_Tactics_Types.decr_depth
                      (FStar_Tactics_Types.set_proofstate_range ps'
                         (FStar_Range.prims_to_fstar_range
                            (Prims.mk_range
                               "FStar.Tactics.CanonCommMonoid.fst"
                               (Prims.of_int (433)) (Prims.of_int (35))
                               (Prims.of_int (433)) (Prims.of_int (56))))))))
      | FStar_Tactics_Result.Failed (e,ps') ->
          FStar_Tactics_Result.Failed (e, ps')
  
let const_compare : 'Aa . ('Aa,Prims.bool) vmap -> var -> var -> Prims.int =
  fun vm  ->
    fun x  ->
      fun y  ->
        match ((select_extra x vm), (select_extra y vm)) with
        | (false ,false ) -> FStar_List_Tot_Base.compare_of_bool (<) x y
        | (true ,true ) -> FStar_List_Tot_Base.compare_of_bool (<) x y
        | (false ,true ) -> Prims.int_one
        | (true ,false ) -> (Prims.of_int (-1))
  
let const_last :
  'Aa . ('Aa,Prims.bool) vmap -> var Prims.list -> var Prims.list =
  fun vm  -> fun xs  -> FStar_List_Tot_Base.sortWith (const_compare vm) xs 
let canon_monoid_const :
  'Aa .
    'Aa FStar_Algebra_CommMonoid.cm ->
      (unit,unit) FStar_Tactics_Effect._dm4f_TAC_repr
  =
  fun cm  ->
    canon_monoid_with is_const false (fun a  -> const_last) () ()
      (Obj.magic cm)
  

let (is_special :
  FStar_Reflection_Types.term Prims.list ->
    FStar_Reflection_Types.term ->
      (Prims.bool,unit) FStar_Tactics_Effect._dm4f_TAC_repr)
  =
  fun ts  ->
    fun t  -> fun s  -> FStar_Tactics_Result.Success ((term_mem t ts), s)
  
let special_compare : 'Aa . ('Aa,Prims.bool) vmap -> var -> var -> Prims.int
  =
  fun vm  ->
    fun x  ->
      fun y  ->
        match ((select_extra x vm), (select_extra y vm)) with
        | (false ,false ) -> Prims.int_zero
        | (true ,true ) -> FStar_List_Tot_Base.compare_of_bool (<) x y
        | (false ,true ) -> (Prims.of_int (-1))
        | (true ,false ) -> Prims.int_one
  
let special_first :
  'Aa . ('Aa,Prims.bool) vmap -> var Prims.list -> var Prims.list =
  fun vm  -> fun xs  -> FStar_List_Tot_Base.sortWith (special_compare vm) xs 

let canon_monoid_special :
  'Auu____8467 .
    FStar_Reflection_Types.term Prims.list ->
      'Auu____8467 FStar_Algebra_CommMonoid.cm ->
        (unit,unit) FStar_Tactics_Effect._dm4f_TAC_repr
  =
  fun a3  ->
    fun a4  ->
      (fun ts  ->
         Obj.magic
           (canon_monoid_with (is_special ts) false (fun a  -> special_first)
              () ())) a3 a4
  
