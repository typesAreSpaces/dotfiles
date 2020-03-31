open Prims
let (dump : Prims.string -> (unit,unit) FStar_Tactics_Effect._dm4f_TAC_repr)
  =
  fun m  ->
    fun ps  ->
      match (FStar_Tactics_Builtins.debugging ())
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.CanonMonoid.fst"
                          (Prims.of_int (24)) (Prims.of_int (16))
                          (Prims.of_int (24)) (Prims.of_int (28))))))
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
                          (Prims.mk_range "FStar.Tactics.CanonMonoid.fst"
                             (Prims.of_int (24)) (Prims.of_int (13))
                             (Prims.of_int (24)) (Prims.of_int (40)))))))
      | FStar_Tactics_Result.Failed (e,ps') ->
          FStar_Tactics_Result.Failed (e, ps')
  
type 'Aa exp =
  | Unit 
  | Var of 'Aa 
  | Mult of 'Aa exp * 'Aa exp 
let uu___is_Unit : 'Aa . 'Aa exp -> Prims.bool =
  fun projectee  -> match projectee with | Unit  -> true | uu____146 -> false 
let uu___is_Var : 'Aa . 'Aa exp -> Prims.bool =
  fun projectee  ->
    match projectee with | Var _0 -> true | uu____172 -> false
  
let __proj__Var__item___0 : 'Aa . 'Aa exp -> 'Aa =
  fun projectee  -> match projectee with | Var _0 -> _0 
let uu___is_Mult : 'Aa . 'Aa exp -> Prims.bool =
  fun projectee  ->
    match projectee with | Mult (_0,_1) -> true | uu____223 -> false
  
let __proj__Mult__item___0 : 'Aa . 'Aa exp -> 'Aa exp =
  fun projectee  -> match projectee with | Mult (_0,_1) -> _0 
let __proj__Mult__item___1 : 'Aa . 'Aa exp -> 'Aa exp =
  fun projectee  -> match projectee with | Mult (_0,_1) -> _1 
let rec exp_to_string :
  'Aa . ('Aa -> Prims.string) -> 'Aa exp -> Prims.string =
  fun a_to_string  ->
    fun e  ->
      match e with
      | Unit  -> "Unit"
      | Var x -> Prims.strcat "Var " (a_to_string x)
      | Mult (e1,e2) ->
          Prims.strcat "Mult ("
            (Prims.strcat (exp_to_string a_to_string e1)
               (Prims.strcat ") ("
                  (Prims.strcat (exp_to_string a_to_string e2) ")")))
  
let rec mdenote : 'Aa . 'Aa FStar_Algebra_Monoid.monoid -> 'Aa exp -> 'Aa =
  fun m  ->
    fun e  ->
      match e with
      | Unit  -> FStar_Algebra_Monoid.__proj__Monoid__item__unit m
      | Var x -> x
      | Mult (e1,e2) ->
          FStar_Algebra_Monoid.__proj__Monoid__item__mult m (mdenote m e1)
            (mdenote m e2)
  
let rec mldenote :
  'Aa . 'Aa FStar_Algebra_Monoid.monoid -> 'Aa Prims.list -> 'Aa =
  fun m  ->
    fun xs  ->
      match xs with
      | [] -> FStar_Algebra_Monoid.__proj__Monoid__item__unit m
      | x::[] -> x
      | x::xs' ->
          FStar_Algebra_Monoid.__proj__Monoid__item__mult m x
            (mldenote m xs')
  
let rec flatten : 'Aa . 'Aa exp -> 'Aa Prims.list =
  fun e  ->
    match e with
    | Unit  -> []
    | Var x -> [x]
    | Mult (e1,e2) -> FStar_List_Tot_Base.op_At (flatten e1) (flatten e2)
  



let rec reification_aux :
  'Aa .
    FStar_Reflection_Types.term ->
      FStar_Reflection_Types.term ->
        FStar_Reflection_Types.term ->
          ('Aa exp,unit) FStar_Tactics_Effect._dm4f_TAC_repr
  =
  fun mult  ->
    fun unit  ->
      fun me  ->
        fun ps  ->
          match () with
          | () ->
              ((match FStar_Reflection_Derived_Lemmas.collect_app_ref me with
                | (hd1,tl1) ->
                    (fun ps1  ->
                       match () with
                       | () ->
                           (match match (FStar_Tactics_Builtins.inspect hd1)
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
                                                                    "FStar.Tactics.CanonMonoid.fst"
                                                                    (Prims.of_int (85))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (85))
                                                                    (Prims.of_int (24))))))
                                                            (FStar_Range.prims_to_fstar_range
                                                               (Prims.mk_range
                                                                  "FStar.Tactics.CanonMonoid.fst"
                                                                  (Prims.of_int (86))
                                                                  (Prims.of_int (2))
                                                                  (Prims.of_int (94))
                                                                  (Prims.of_int (25))))))
                                                      (FStar_Range.prims_to_fstar_range
                                                         (Prims.mk_range
                                                            "FStar.Tactics.CanonMonoid.fst"
                                                            (Prims.of_int (86))
                                                            (Prims.of_int (8))
                                                            (Prims.of_int (86))
                                                            (Prims.of_int (22))))))
                                                (FStar_Range.prims_to_fstar_range
                                                   (Prims.mk_range
                                                      "FStar.Tactics.CanonMonoid.fst"
                                                      (Prims.of_int (86))
                                                      (Prims.of_int (8))
                                                      (Prims.of_int (86))
                                                      (Prims.of_int (18))))))
                                  with
                                  | FStar_Tactics_Result.Success (a,ps') ->
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
                                                           "FStar.Tactics.CanonMonoid.fst"
                                                           (Prims.of_int (86))
                                                           (Prims.of_int (8))
                                                           (Prims.of_int (86))
                                                           (Prims.of_int (22))))))))
                                  | FStar_Tactics_Result.Failed (e,ps') ->
                                      FStar_Tactics_Result.Failed (e, ps')
                            with
                            | FStar_Tactics_Result.Success (a,ps') ->
                                (match () with
                                 | () ->
                                     ((match a with
                                       | (FStar_Reflection_Data.Tv_FVar
                                          fv,(me1,FStar_Reflection_Data.Q_Explicit
                                              )::(me2,FStar_Reflection_Data.Q_Explicit
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
                                                                    "FStar.Tactics.CanonMonoid.fst"
                                                                    (Prims.of_int (88))
                                                                    (Prims.of_int (7))
                                                                    (Prims.of_int (88))
                                                                    (Prims.of_int (39))))))
                                                                  (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonMonoid.fst"
                                                                    (Prims.of_int (88))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (88))
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
                                                                    (
                                                                    FStar_Tactics_Types.set_proofstate_range
                                                                    ps'1
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonMonoid.fst"
                                                                    (Prims.of_int (88))
                                                                    (Prims.of_int (7))
                                                                    (Prims.of_int (88))
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
                                                             match (reification_aux
                                                                    mult unit
                                                                    me1)
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonMonoid.fst"
                                                                    (Prims.of_int (89))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (89))
                                                                    (Prims.of_int (45))))))
                                                             with
                                                             | FStar_Tactics_Result.Success
                                                                 (a2,ps'2) ->
                                                                 (match ()
                                                                  with
                                                                  | () ->
                                                                    (match 
                                                                    (reification_aux
                                                                    mult unit
                                                                    me2)
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonMonoid.fst"
                                                                    (Prims.of_int (89))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (89))
                                                                    (Prims.of_int (77))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonMonoid.fst"
                                                                    (Prims.of_int (89))
                                                                    (Prims.of_int (46))
                                                                    (Prims.of_int (89))
                                                                    (Prims.of_int (77))))))
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
                                                                    ((Mult
                                                                    (a2, a3)),
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonMonoid.fst"
                                                                    (Prims.of_int (89))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (89))
                                                                    (Prims.of_int (77))))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e,ps'3)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'3)))
                                                             | FStar_Tactics_Result.Failed
                                                                 (e,ps'2) ->
                                                                 FStar_Tactics_Result.Failed
                                                                   (e, ps'2))
                                                        else
                                                          (fun ps3  ->
                                                             match (FStar_Tactics_Builtins.unquote
                                                                    me)
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonMonoid.fst"
                                                                    (Prims.of_int (90))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (90))
                                                                    (Prims.of_int (25))))))
                                                             with
                                                             | FStar_Tactics_Result.Success
                                                                 (a2,ps'2) ->
                                                                 (match ()
                                                                  with
                                                                  | () ->
                                                                    FStar_Tactics_Result.Success
                                                                    ((Var a2),
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonMonoid.fst"
                                                                    (Prims.of_int (90))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (90))
                                                                    (Prims.of_int (25))))))))
                                                             | FStar_Tactics_Result.Failed
                                                                 (e,ps'2) ->
                                                                 FStar_Tactics_Result.Failed
                                                                   (e, ps'2)))
                                                         (FStar_Tactics_Types.decr_depth
                                                            (FStar_Tactics_Types.set_proofstate_range
                                                               ps'1
                                                               (FStar_Range.prims_to_fstar_range
                                                                  (Prims.mk_range
                                                                    "FStar.Tactics.CanonMonoid.fst"
                                                                    (Prims.of_int (88))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (90))
                                                                    (Prims.of_int (25)))))))
                                              | FStar_Tactics_Result.Failed
                                                  (e,ps'1) ->
                                                  FStar_Tactics_Result.Failed
                                                    (e, ps'1))
                                       | (uu____1195,uu____1196) ->
                                           if
                                             FStar_Reflection_Basic.term_eq
                                               me unit
                                           then
                                             (fun s  ->
                                                FStar_Tactics_Result.Success
                                                  (Unit, s))
                                           else
                                             (fun ps2  ->
                                                match (FStar_Tactics_Builtins.unquote
                                                         me)
                                                        (FStar_Tactics_Types.incr_depth
                                                           (FStar_Tactics_Types.set_proofstate_range
                                                              ps2
                                                              (FStar_Range.prims_to_fstar_range
                                                                 (Prims.mk_range
                                                                    "FStar.Tactics.CanonMonoid.fst"
                                                                    (Prims.of_int (94))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (94))
                                                                    (Prims.of_int (25))))))
                                                with
                                                | FStar_Tactics_Result.Success
                                                    (a1,ps'1) ->
                                                    (match () with
                                                     | () ->
                                                         FStar_Tactics_Result.Success
                                                           ((Var a1),
                                                             (FStar_Tactics_Types.decr_depth
                                                                (FStar_Tactics_Types.set_proofstate_range
                                                                   ps'1
                                                                   (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonMonoid.fst"
                                                                    (Prims.of_int (94))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (94))
                                                                    (Prims.of_int (25))))))))
                                                | FStar_Tactics_Result.Failed
                                                    (e,ps'1) ->
                                                    FStar_Tactics_Result.Failed
                                                      (e, ps'1))))
                                       (FStar_Tactics_Types.decr_depth
                                          (FStar_Tactics_Types.set_proofstate_range
                                             ps'
                                             (FStar_Range.prims_to_fstar_range
                                                (Prims.mk_range
                                                   "FStar.Tactics.CanonMonoid.fst"
                                                   (Prims.of_int (86))
                                                   (Prims.of_int (2))
                                                   (Prims.of_int (94))
                                                   (Prims.of_int (25)))))))
                            | FStar_Tactics_Result.Failed (e,ps') ->
                                FStar_Tactics_Result.Failed (e, ps')))))
                (FStar_Tactics_Types.decr_depth
                   (FStar_Tactics_Types.set_proofstate_range
                      (FStar_Tactics_Types.incr_depth
                         (FStar_Tactics_Types.set_proofstate_range ps
                            (FStar_Range.prims_to_fstar_range
                               (Prims.mk_range
                                  "FStar.Tactics.CanonMonoid.fst"
                                  (Prims.of_int (84)) (Prims.of_int (15))
                                  (Prims.of_int (84)) (Prims.of_int (33))))))
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range "FStar.Tactics.CanonMonoid.fst"
                            (Prims.of_int (84)) (Prims.of_int (2))
                            (Prims.of_int (94)) (Prims.of_int (25))))))
  
let reification :
  'Aa .
    'Aa FStar_Algebra_Monoid.monoid ->
      FStar_Reflection_Types.term ->
        ('Aa exp,unit) FStar_Tactics_Effect._dm4f_TAC_repr
  =
  fun m  ->
    fun me  ->
      fun ps  ->
        match match () with
              | () ->
                  (FStar_Tactics_Derived.norm_term
                     [FStar_Pervasives.delta;
                     FStar_Pervasives.zeta;
                     FStar_Pervasives.iota]
                     (Obj.magic
                        (failwith "Cannot evaluate open quotation at runtime")))
                    (FStar_Tactics_Types.decr_depth
                       (FStar_Tactics_Types.set_proofstate_range
                          (FStar_Tactics_Types.incr_depth
                             (FStar_Tactics_Types.set_proofstate_range
                                (FStar_Tactics_Types.incr_depth
                                   (FStar_Tactics_Types.set_proofstate_range
                                      ps
                                      (FStar_Range.prims_to_fstar_range
                                         (Prims.mk_range
                                            "FStar.Tactics.CanonMonoid.fst"
                                            (Prims.of_int (97))
                                            (Prims.of_int (15))
                                            (Prims.of_int (97))
                                            (Prims.of_int (67))))))
                                (FStar_Range.prims_to_fstar_range
                                   (Prims.mk_range
                                      "FStar.Tactics.CanonMonoid.fst"
                                      (Prims.of_int (97)) (Prims.of_int (43))
                                      (Prims.of_int (97)) (Prims.of_int (67))))))
                          (FStar_Range.prims_to_fstar_range
                             (Prims.mk_range "FStar.Tactics.CanonMonoid.fst"
                                (Prims.of_int (97)) (Prims.of_int (15))
                                (Prims.of_int (97)) (Prims.of_int (67))))))
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
                                                            "FStar.Tactics.CanonMonoid.fst"
                                                            (Prims.of_int (98))
                                                            (Prims.of_int (4))
                                                            (Prims.of_int (103))
                                                            (Prims.of_int (32))))))
                                                (FStar_Range.prims_to_fstar_range
                                                   (Prims.mk_range
                                                      "FStar.Tactics.CanonMonoid.fst"
                                                      (Prims.of_int (98))
                                                      (Prims.of_int (15))
                                                      (Prims.of_int (98))
                                                      (Prims.of_int (67))))))
                                          (FStar_Range.prims_to_fstar_range
                                             (Prims.mk_range
                                                "FStar.Tactics.CanonMonoid.fst"
                                                (Prims.of_int (98))
                                                (Prims.of_int (43))
                                                (Prims.of_int (98))
                                                (Prims.of_int (67))))))
                                    (FStar_Range.prims_to_fstar_range
                                       (Prims.mk_range
                                          "FStar.Tactics.CanonMonoid.fst"
                                          (Prims.of_int (98))
                                          (Prims.of_int (15))
                                          (Prims.of_int (98))
                                          (Prims.of_int (67))))))
                  with
                  | FStar_Tactics_Result.Success (a1,ps'1) ->
                      (match () with
                       | () ->
                           (match (FStar_Tactics_Derived.norm_term
                                     [FStar_Pervasives.delta;
                                     FStar_Pervasives.zeta;
                                     FStar_Pervasives.iota] me)
                                    (FStar_Tactics_Types.incr_depth
                                       (FStar_Tactics_Types.set_proofstate_range
                                          (FStar_Tactics_Types.decr_depth
                                             (FStar_Tactics_Types.set_proofstate_range
                                                ps'1
                                                (FStar_Range.prims_to_fstar_range
                                                   (Prims.mk_range
                                                      "FStar.Tactics.CanonMonoid.fst"
                                                      (Prims.of_int (99))
                                                      (Prims.of_int (4))
                                                      (Prims.of_int (103))
                                                      (Prims.of_int (32))))))
                                          (FStar_Range.prims_to_fstar_range
                                             (Prims.mk_range
                                                "FStar.Tactics.CanonMonoid.fst"
                                                (Prims.of_int (99))
                                                (Prims.of_int (15))
                                                (Prims.of_int (99))
                                                (Prims.of_int (45))))))
                            with
                            | FStar_Tactics_Result.Success (a2,ps'2) ->
                                (match () with
                                 | () ->
                                     (reification_aux a a1 a2)
                                       (FStar_Tactics_Types.decr_depth
                                          (FStar_Tactics_Types.set_proofstate_range
                                             ps'2
                                             (FStar_Range.prims_to_fstar_range
                                                (Prims.mk_range
                                                   "FStar.Tactics.CanonMonoid.fst"
                                                   (Prims.of_int (103))
                                                   (Prims.of_int (4))
                                                   (Prims.of_int (103))
                                                   (Prims.of_int (32)))))))
                            | FStar_Tactics_Result.Failed (e,ps'2) ->
                                FStar_Tactics_Result.Failed (e, ps'2)))
                  | FStar_Tactics_Result.Failed (e,ps'1) ->
                      FStar_Tactics_Result.Failed (e, ps'1)))
        | FStar_Tactics_Result.Failed (e,ps') ->
            FStar_Tactics_Result.Failed (e, ps')
  
let canon_monoid :
  'Aa .
    'Aa FStar_Algebra_Monoid.monoid ->
      (unit,unit) FStar_Tactics_Effect._dm4f_TAC_repr
  =
  fun m  ->
    fun ps  ->
      match (FStar_Tactics_Builtins.norm [])
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.CanonMonoid.fst"
                          (Prims.of_int (106)) (Prims.of_int (2))
                          (Prims.of_int (106)) (Prims.of_int (9))))))
      with
      | FStar_Tactics_Result.Success (a,ps') ->
          (match () with
           | () ->
               (match (FStar_Tactics_Derived.cur_goal ())
                        (FStar_Tactics_Types.incr_depth
                           (FStar_Tactics_Types.set_proofstate_range
                              (FStar_Tactics_Types.decr_depth
                                 (FStar_Tactics_Types.set_proofstate_range
                                    ps'
                                    (FStar_Range.prims_to_fstar_range
                                       (Prims.mk_range
                                          "FStar.Tactics.CanonMonoid.fst"
                                          (Prims.of_int (107))
                                          (Prims.of_int (2))
                                          (Prims.of_int (120))
                                          (Prims.of_int (42))))))
                              (FStar_Range.prims_to_fstar_range
                                 (Prims.mk_range
                                    "FStar.Tactics.CanonMonoid.fst"
                                    (Prims.of_int (107)) (Prims.of_int (10))
                                    (Prims.of_int (107)) (Prims.of_int (21))))))
                with
                | FStar_Tactics_Result.Success (a1,ps'1) ->
                    (match () with
                     | () ->
                         (match (FStar_Reflection_Formula.term_as_formula a1)
                                  (FStar_Tactics_Types.incr_depth
                                     (FStar_Tactics_Types.set_proofstate_range
                                        (FStar_Tactics_Types.decr_depth
                                           (FStar_Tactics_Types.set_proofstate_range
                                              ps'1
                                              (FStar_Range.prims_to_fstar_range
                                                 (Prims.mk_range
                                                    "FStar.Tactics.CanonMonoid.fst"
                                                    (Prims.of_int (108))
                                                    (Prims.of_int (2))
                                                    (Prims.of_int (120))
                                                    (Prims.of_int (42))))))
                                        (FStar_Range.prims_to_fstar_range
                                           (Prims.mk_range
                                              "FStar.Tactics.CanonMonoid.fst"
                                              (Prims.of_int (108))
                                              (Prims.of_int (8))
                                              (Prims.of_int (108))
                                              (Prims.of_int (25))))))
                          with
                          | FStar_Tactics_Result.Success (a2,ps'2) ->
                              (match () with
                               | () ->
                                   ((match a2 with
                                     | FStar_Reflection_Formula.Comp
                                         (FStar_Reflection_Formula.Eq
                                          (FStar_Pervasives_Native.Some
                                          t),me1,me2)
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
                                                                    "FStar.Tactics.CanonMonoid.fst"
                                                                    (Prims.of_int (110))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (110))
                                                                    (Prims.of_int (28))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonMonoid.fst"
                                                                    (Prims.of_int (110))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (110))
                                                                    (Prims.of_int (28))))))
                                                                (FStar_Range.prims_to_fstar_range
                                                                   (Prims.mk_range
                                                                    "FStar.Tactics.CanonMonoid.fst"
                                                                    (Prims.of_int (110))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (110))
                                                                    (Prims.of_int (28)))))))
                                            with
                                            | FStar_Tactics_Result.Success
                                                (a3,ps'3) ->
                                                (match () with
                                                 | () ->
                                                     (if a3
                                                      then
                                                        (fun ps2  ->
                                                           match (reification
                                                                    m me1)
                                                                   (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonMonoid.fst"
                                                                    (Prims.of_int (111))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (111))
                                                                    (Prims.of_int (34))))))
                                                           with
                                                           | FStar_Tactics_Result.Success
                                                               (a4,ps'4) ->
                                                               (match () with
                                                                | () ->
                                                                    (
                                                                    match 
                                                                    (reification
                                                                    m me2)
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'4
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonMonoid.fst"
                                                                    (Prims.of_int (112))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (118))
                                                                    (Prims.of_int (56))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonMonoid.fst"
                                                                    (Prims.of_int (112))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (112))
                                                                    (Prims.of_int (34))))))
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
                                                                    "FStar.Tactics.CanonMonoid.fst"
                                                                    (Prims.of_int (113))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (118))
                                                                    (Prims.of_int (56))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonMonoid.fst"
                                                                    (Prims.of_int (113))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (113))
                                                                    (Prims.of_int (56))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonMonoid.fst"
                                                                    (Prims.of_int (113))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (113))
                                                                    (Prims.of_int (56))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonMonoid.fst"
                                                                    (Prims.of_int (113))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (113))
                                                                    (Prims.of_int (56))))))
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
                                                                    "CanonMonoid";
                                                                    "monoid_reflect"]))))
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'6
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonMonoid.fst"
                                                                    (Prims.of_int (114))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (118))
                                                                    (Prims.of_int (56))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonMonoid.fst"
                                                                    (Prims.of_int (114))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (114))
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
                                                                    ["CanonMonoid.mldenote";
                                                                    "CanonMonoid.flatten";
                                                                    "FStar.List.Tot.Base.op_At";
                                                                    "FStar.List.Tot.Base.append"]])
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'7
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonMonoid.fst"
                                                                    (Prims.of_int (115))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (118))
                                                                    (Prims.of_int (56)))))))
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
                                                                    (e, ps'5)))
                                                           | FStar_Tactics_Result.Failed
                                                               (e,ps'4) ->
                                                               FStar_Tactics_Result.Failed
                                                                 (e, ps'4))
                                                      else
                                                        FStar_Tactics_Derived.fail
                                                          "Goal should be an equality at the right monoid type")
                                                       (FStar_Tactics_Types.decr_depth
                                                          (FStar_Tactics_Types.set_proofstate_range
                                                             ps'3
                                                             (FStar_Range.prims_to_fstar_range
                                                                (Prims.mk_range
                                                                   "FStar.Tactics.CanonMonoid.fst"
                                                                   (Prims.of_int (110))
                                                                   (Prims.of_int (6))
                                                                   (Prims.of_int (119))
                                                                   (Prims.of_int (69)))))))
                                            | FStar_Tactics_Result.Failed
                                                (e,ps'3) ->
                                                FStar_Tactics_Result.Failed
                                                  (e, ps'3))
                                     | uu____1865 ->
                                         FStar_Tactics_Derived.fail
                                           "Goal should be an equality"))
                                     (FStar_Tactics_Types.decr_depth
                                        (FStar_Tactics_Types.set_proofstate_range
                                           ps'2
                                           (FStar_Range.prims_to_fstar_range
                                              (Prims.mk_range
                                                 "FStar.Tactics.CanonMonoid.fst"
                                                 (Prims.of_int (108))
                                                 (Prims.of_int (2))
                                                 (Prims.of_int (120))
                                                 (Prims.of_int (42)))))))
                          | FStar_Tactics_Result.Failed (e,ps'2) ->
                              FStar_Tactics_Result.Failed (e, ps'2)))
                | FStar_Tactics_Result.Failed (e,ps'1) ->
                    FStar_Tactics_Result.Failed (e, ps'1)))
      | FStar_Tactics_Result.Failed (e,ps') ->
          FStar_Tactics_Result.Failed (e, ps')
  
