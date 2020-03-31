open Prims

let (goals :
  unit ->
    (FStar_Tactics_Types.goal Prims.list,unit)
      FStar_Tactics_Effect._dm4f_TAC_repr)
  =
  fun uu____27  ->
    fun ps  ->
      match (FStar_Tactics_Effect.get ())
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.Derived.fst"
                          (Prims.of_int (35)) (Prims.of_int (42))
                          (Prims.of_int (35)) (Prims.of_int (50))))))
      with
      | FStar_Tactics_Result.Success (a,ps') ->
          (match () with
           | () ->
               FStar_Tactics_Result.Success
                 ((FStar_Tactics_Types.goals_of a),
                   (FStar_Tactics_Types.decr_depth
                      (FStar_Tactics_Types.set_proofstate_range ps'
                         (FStar_Range.prims_to_fstar_range
                            (Prims.mk_range "FStar.Tactics.Derived.fst"
                               (Prims.of_int (35)) (Prims.of_int (33))
                               (Prims.of_int (35)) (Prims.of_int (50))))))))
      | FStar_Tactics_Result.Failed (e,ps') ->
          FStar_Tactics_Result.Failed (e, ps')
  
let (smt_goals :
  unit ->
    (FStar_Tactics_Types.goal Prims.list,unit)
      FStar_Tactics_Effect._dm4f_TAC_repr)
  =
  fun uu____115  ->
    fun ps  ->
      match (FStar_Tactics_Effect.get ())
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.Derived.fst"
                          (Prims.of_int (36)) (Prims.of_int (50))
                          (Prims.of_int (36)) (Prims.of_int (58))))))
      with
      | FStar_Tactics_Result.Success (a,ps') ->
          (match () with
           | () ->
               FStar_Tactics_Result.Success
                 ((FStar_Tactics_Types.smt_goals_of a),
                   (FStar_Tactics_Types.decr_depth
                      (FStar_Tactics_Types.set_proofstate_range ps'
                         (FStar_Range.prims_to_fstar_range
                            (Prims.mk_range "FStar.Tactics.Derived.fst"
                               (Prims.of_int (36)) (Prims.of_int (37))
                               (Prims.of_int (36)) (Prims.of_int (58))))))))
      | FStar_Tactics_Result.Failed (e,ps') ->
          FStar_Tactics_Result.Failed (e, ps')
  
let fail :
  'Aa . Prims.string -> ('Aa,unit) FStar_Tactics_Effect._dm4f_TAC_repr =
  fun m  -> FStar_Tactics_Effect.raise (FStar_Tactics_Types.TacticFailure m) 
let (_cur_goal :
  unit -> (FStar_Tactics_Types.goal,unit) FStar_Tactics_Effect._dm4f_TAC_repr)
  =
  fun uu____229  ->
    fun ps  ->
      match (goals ())
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.Derived.fst"
                          (Prims.of_int (42)) (Prims.of_int (10))
                          (Prims.of_int (42)) (Prims.of_int (18))))))
      with
      | FStar_Tactics_Result.Success (a,ps') ->
          (match () with
           | () ->
               ((match a with
                 | [] -> fail "no more goals"
                 | g::uu____287 ->
                     (fun s  -> FStar_Tactics_Result.Success (g, s))))
                 (FStar_Tactics_Types.decr_depth
                    (FStar_Tactics_Types.set_proofstate_range ps'
                       (FStar_Range.prims_to_fstar_range
                          (Prims.mk_range "FStar.Tactics.Derived.fst"
                             (Prims.of_int (42)) (Prims.of_int (4))
                             (Prims.of_int (44)) (Prims.of_int (15)))))))
      | FStar_Tactics_Result.Failed (e,ps') ->
          FStar_Tactics_Result.Failed (e, ps')
  
let (cur_env :
  unit ->
    (FStar_Reflection_Types.env,unit) FStar_Tactics_Effect._dm4f_TAC_repr)
  =
  fun uu____320  ->
    fun ps  ->
      match (_cur_goal ())
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.Derived.fst"
                          (Prims.of_int (47)) (Prims.of_int (36))
                          (Prims.of_int (47)) (Prims.of_int (50))))))
      with
      | FStar_Tactics_Result.Success (a,ps') ->
          (match () with
           | () ->
               FStar_Tactics_Result.Success
                 ((FStar_Tactics_Types.goal_env a),
                   (FStar_Tactics_Types.decr_depth
                      (FStar_Tactics_Types.set_proofstate_range ps'
                         (FStar_Range.prims_to_fstar_range
                            (Prims.mk_range "FStar.Tactics.Derived.fst"
                               (Prims.of_int (47)) (Prims.of_int (27))
                               (Prims.of_int (47)) (Prims.of_int (50))))))))
      | FStar_Tactics_Result.Failed (e,ps') ->
          FStar_Tactics_Result.Failed (e, ps')
  
let (cur_goal :
  unit ->
    (FStar_Reflection_Types.typ,unit) FStar_Tactics_Effect._dm4f_TAC_repr)
  =
  fun uu____390  ->
    fun ps  ->
      match (_cur_goal ())
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.Derived.fst"
                          (Prims.of_int (50)) (Prims.of_int (38))
                          (Prims.of_int (50)) (Prims.of_int (52))))))
      with
      | FStar_Tactics_Result.Success (a,ps') ->
          (match () with
           | () ->
               FStar_Tactics_Result.Success
                 ((FStar_Tactics_Types.goal_type a),
                   (FStar_Tactics_Types.decr_depth
                      (FStar_Tactics_Types.set_proofstate_range ps'
                         (FStar_Range.prims_to_fstar_range
                            (Prims.mk_range "FStar.Tactics.Derived.fst"
                               (Prims.of_int (50)) (Prims.of_int (28))
                               (Prims.of_int (50)) (Prims.of_int (52))))))))
      | FStar_Tactics_Result.Failed (e,ps') ->
          FStar_Tactics_Result.Failed (e, ps')
  
let (cur_witness :
  unit ->
    (FStar_Reflection_Types.term,unit) FStar_Tactics_Effect._dm4f_TAC_repr)
  =
  fun uu____460  ->
    fun ps  ->
      match (_cur_goal ())
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.Derived.fst"
                          (Prims.of_int (53)) (Prims.of_int (45))
                          (Prims.of_int (53)) (Prims.of_int (59))))))
      with
      | FStar_Tactics_Result.Success (a,ps') ->
          (match () with
           | () ->
               FStar_Tactics_Result.Success
                 ((FStar_Tactics_Types.goal_witness a),
                   (FStar_Tactics_Types.decr_depth
                      (FStar_Tactics_Types.set_proofstate_range ps'
                         (FStar_Range.prims_to_fstar_range
                            (Prims.mk_range "FStar.Tactics.Derived.fst"
                               (Prims.of_int (53)) (Prims.of_int (32))
                               (Prims.of_int (53)) (Prims.of_int (59))))))))
      | FStar_Tactics_Result.Failed (e,ps') ->
          FStar_Tactics_Result.Failed (e, ps')
  
let (cur_goal_safe :
  unit -> (FStar_Tactics_Types.goal,unit) FStar_Tactics_Effect._dm4f_TAC_repr)
  =
  fun uu____536  ->
    fun ps  ->
      match match (FStar_Tactics_Effect.get ())
                    (FStar_Tactics_Types.incr_depth
                       (FStar_Tactics_Types.set_proofstate_range
                          (FStar_Tactics_Types.incr_depth
                             (FStar_Tactics_Types.set_proofstate_range ps
                                (FStar_Range.prims_to_fstar_range
                                   (Prims.mk_range
                                      "FStar.Tactics.Derived.fst"
                                      (Prims.of_int (60)) (Prims.of_int (9))
                                      (Prims.of_int (60)) (Prims.of_int (26))))))
                          (FStar_Range.prims_to_fstar_range
                             (Prims.mk_range "FStar.Tactics.Derived.fst"
                                (Prims.of_int (60)) (Prims.of_int (18))
                                (Prims.of_int (60)) (Prims.of_int (26))))))
            with
            | FStar_Tactics_Result.Success (a,ps') ->
                (match () with
                 | () ->
                     FStar_Tactics_Result.Success
                       ((FStar_Tactics_Types.goals_of a),
                         (FStar_Tactics_Types.decr_depth
                            (FStar_Tactics_Types.set_proofstate_range ps'
                               (FStar_Range.prims_to_fstar_range
                                  (Prims.mk_range "FStar.Tactics.Derived.fst"
                                     (Prims.of_int (60)) (Prims.of_int (9))
                                     (Prims.of_int (60)) (Prims.of_int (26))))))))
            | FStar_Tactics_Result.Failed (e,ps') ->
                FStar_Tactics_Result.Failed (e, ps')
      with
      | FStar_Tactics_Result.Success (a,ps') ->
          (match () with
           | () ->
               ((match a with
                 | g::uu____627 ->
                     (fun s  -> FStar_Tactics_Result.Success (g, s))))
                 (FStar_Tactics_Types.decr_depth
                    (FStar_Tactics_Types.set_proofstate_range ps'
                       (FStar_Range.prims_to_fstar_range
                          (Prims.mk_range "FStar.Tactics.Derived.fst"
                             (Prims.of_int (60)) (Prims.of_int (3))
                             (Prims.of_int (61)) (Prims.of_int (16)))))))
      | FStar_Tactics_Result.Failed (e,ps') ->
          FStar_Tactics_Result.Failed (e, ps')
  
let (cur_binders :
  unit ->
    (FStar_Reflection_Types.binders,unit) FStar_Tactics_Effect._dm4f_TAC_repr)
  =
  fun uu____660  ->
    fun ps  ->
      match (cur_env ())
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.Derived.fst"
                          (Prims.of_int (65)) (Prims.of_int (19))
                          (Prims.of_int (65)) (Prims.of_int (31))))))
      with
      | FStar_Tactics_Result.Success (a,ps') ->
          (match () with
           | () ->
               FStar_Tactics_Result.Success
                 ((FStar_Reflection_Basic.binders_of_env a),
                   (FStar_Tactics_Types.decr_depth
                      (FStar_Tactics_Types.set_proofstate_range ps'
                         (FStar_Range.prims_to_fstar_range
                            (Prims.mk_range "FStar.Tactics.Derived.fst"
                               (Prims.of_int (65)) (Prims.of_int (4))
                               (Prims.of_int (65)) (Prims.of_int (31))))))))
      | FStar_Tactics_Result.Failed (e,ps') ->
          FStar_Tactics_Result.Failed (e, ps')
  
let with_policy :
  'a .
    FStar_Tactics_Types.guard_policy ->
      (unit -> ('a,unit) FStar_Tactics_Effect._dm4f_TAC_repr) ->
        ('a,unit) FStar_Tactics_Effect._dm4f_TAC_repr
  =
  fun pol  ->
    fun f  ->
      fun ps  ->
        match (FStar_Tactics_Builtins.get_guard_policy ())
                (FStar_Tactics_Types.incr_depth
                   (FStar_Tactics_Types.set_proofstate_range ps
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range "FStar.Tactics.Derived.fst"
                            (Prims.of_int (69)) (Prims.of_int (18))
                            (Prims.of_int (69)) (Prims.of_int (37))))))
        with
        | FStar_Tactics_Result.Success (a,ps') ->
            (match () with
             | () ->
                 (match (FStar_Tactics_Builtins.set_guard_policy pol)
                          (FStar_Tactics_Types.incr_depth
                             (FStar_Tactics_Types.set_proofstate_range
                                (FStar_Tactics_Types.decr_depth
                                   (FStar_Tactics_Types.set_proofstate_range
                                      ps'
                                      (FStar_Range.prims_to_fstar_range
                                         (Prims.mk_range
                                            "FStar.Tactics.Derived.fst"
                                            (Prims.of_int (70))
                                            (Prims.of_int (4))
                                            (Prims.of_int (73))
                                            (Prims.of_int (5))))))
                                (FStar_Range.prims_to_fstar_range
                                   (Prims.mk_range
                                      "FStar.Tactics.Derived.fst"
                                      (Prims.of_int (70)) (Prims.of_int (4))
                                      (Prims.of_int (70)) (Prims.of_int (24))))))
                  with
                  | FStar_Tactics_Result.Success (a1,ps'1) ->
                      (match () with
                       | () ->
                           (match (f ())
                                    (FStar_Tactics_Types.incr_depth
                                       (FStar_Tactics_Types.set_proofstate_range
                                          (FStar_Tactics_Types.decr_depth
                                             (FStar_Tactics_Types.set_proofstate_range
                                                ps'1
                                                (FStar_Range.prims_to_fstar_range
                                                   (Prims.mk_range
                                                      "FStar.Tactics.Derived.fst"
                                                      (Prims.of_int (71))
                                                      (Prims.of_int (4))
                                                      (Prims.of_int (73))
                                                      (Prims.of_int (5))))))
                                          (FStar_Range.prims_to_fstar_range
                                             (Prims.mk_range
                                                "FStar.Tactics.Derived.fst"
                                                (Prims.of_int (71))
                                                (Prims.of_int (12))
                                                (Prims.of_int (71))
                                                (Prims.of_int (16))))))
                            with
                            | FStar_Tactics_Result.Success (a2,ps'2) ->
                                (match () with
                                 | () ->
                                     (match (FStar_Tactics_Builtins.set_guard_policy
                                               a)
                                              (FStar_Tactics_Types.incr_depth
                                                 (FStar_Tactics_Types.set_proofstate_range
                                                    (FStar_Tactics_Types.decr_depth
                                                       (FStar_Tactics_Types.set_proofstate_range
                                                          ps'2
                                                          (FStar_Range.prims_to_fstar_range
                                                             (Prims.mk_range
                                                                "FStar.Tactics.Derived.fst"
                                                                (Prims.of_int (72))
                                                                (Prims.of_int (4))
                                                                (Prims.of_int (73))
                                                                (Prims.of_int (5))))))
                                                    (FStar_Range.prims_to_fstar_range
                                                       (Prims.mk_range
                                                          "FStar.Tactics.Derived.fst"
                                                          (Prims.of_int (72))
                                                          (Prims.of_int (4))
                                                          (Prims.of_int (72))
                                                          (Prims.of_int (28))))))
                                      with
                                      | FStar_Tactics_Result.Success
                                          (a3,ps'3) ->
                                          (match () with
                                           | () ->
                                               FStar_Tactics_Result.Success
                                                 (a2,
                                                   (FStar_Tactics_Types.decr_depth
                                                      (FStar_Tactics_Types.set_proofstate_range
                                                         ps'3
                                                         (FStar_Range.prims_to_fstar_range
                                                            (Prims.mk_range
                                                               "FStar.Tactics.Derived.fst"
                                                               (Prims.of_int (71))
                                                               (Prims.of_int (8))
                                                               (Prims.of_int (71))
                                                               (Prims.of_int (9))))))))
                                      | FStar_Tactics_Result.Failed (e,ps'3)
                                          ->
                                          FStar_Tactics_Result.Failed
                                            (e, ps'3)))
                            | FStar_Tactics_Result.Failed (e,ps'2) ->
                                FStar_Tactics_Result.Failed (e, ps'2)))
                  | FStar_Tactics_Result.Failed (e,ps'1) ->
                      FStar_Tactics_Result.Failed (e, ps'1)))
        | FStar_Tactics_Result.Failed (e,ps') ->
            FStar_Tactics_Result.Failed (e, ps')
  
let (dismiss : unit -> (unit,unit) FStar_Tactics_Effect._dm4f_TAC_repr) =
  fun uu____925  ->
    fun ps  ->
      match (goals ())
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.Derived.fst"
                          (Prims.of_int (78)) (Prims.of_int (10))
                          (Prims.of_int (78)) (Prims.of_int (18))))))
      with
      | FStar_Tactics_Result.Success (a,ps') ->
          (match () with
           | () ->
               ((match a with
                 | [] -> fail "dismiss: no more goals"
                 | uu____980::gs -> FStar_Tactics_Builtins.set_goals gs))
                 (FStar_Tactics_Types.decr_depth
                    (FStar_Tactics_Types.set_proofstate_range ps'
                       (FStar_Range.prims_to_fstar_range
                          (Prims.mk_range "FStar.Tactics.Derived.fst"
                             (Prims.of_int (78)) (Prims.of_int (4))
                             (Prims.of_int (80)) (Prims.of_int (27)))))))
      | FStar_Tactics_Result.Failed (e,ps') ->
          FStar_Tactics_Result.Failed (e, ps')
  
let (flip : unit -> (unit,unit) FStar_Tactics_Effect._dm4f_TAC_repr) =
  fun uu____1016  ->
    fun ps  ->
      match (goals ())
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.Derived.fst"
                          (Prims.of_int (84)) (Prims.of_int (13))
                          (Prims.of_int (84)) (Prims.of_int (21))))))
      with
      | FStar_Tactics_Result.Success (a,ps') ->
          (match () with
           | () ->
               (match (goals ())
                        (FStar_Tactics_Types.incr_depth
                           (FStar_Tactics_Types.set_proofstate_range
                              (FStar_Tactics_Types.decr_depth
                                 (FStar_Tactics_Types.set_proofstate_range
                                    ps'
                                    (FStar_Range.prims_to_fstar_range
                                       (Prims.mk_range
                                          "FStar.Tactics.Derived.fst"
                                          (Prims.of_int (85))
                                          (Prims.of_int (4))
                                          (Prims.of_int (87))
                                          (Prims.of_int (42))))))
                              (FStar_Range.prims_to_fstar_range
                                 (Prims.mk_range "FStar.Tactics.Derived.fst"
                                    (Prims.of_int (85)) (Prims.of_int (10))
                                    (Prims.of_int (85)) (Prims.of_int (18))))))
                with
                | FStar_Tactics_Result.Success (a1,ps'1) ->
                    (match () with
                     | () ->
                         ((match a1 with
                           | [] -> fail "flip: less than two goals"
                           | uu____1107::[] ->
                               fail "flip: less than two goals"
                           | g1::g2::gs ->
                               FStar_Tactics_Builtins.set_goals (g2 :: g1 ::
                                 gs)))
                           (FStar_Tactics_Types.decr_depth
                              (FStar_Tactics_Types.set_proofstate_range ps'1
                                 (FStar_Range.prims_to_fstar_range
                                    (Prims.mk_range
                                       "FStar.Tactics.Derived.fst"
                                       (Prims.of_int (85)) (Prims.of_int (4))
                                       (Prims.of_int (87))
                                       (Prims.of_int (42)))))))
                | FStar_Tactics_Result.Failed (e,ps'1) ->
                    FStar_Tactics_Result.Failed (e, ps'1)))
      | FStar_Tactics_Result.Failed (e,ps') ->
          FStar_Tactics_Result.Failed (e, ps')
  
let (qed : unit -> (unit,unit) FStar_Tactics_Effect._dm4f_TAC_repr) =
  fun uu____1146  ->
    fun ps  ->
      match (goals ())
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.Derived.fst"
                          (Prims.of_int (91)) (Prims.of_int (10))
                          (Prims.of_int (91)) (Prims.of_int (18))))))
      with
      | FStar_Tactics_Result.Success (a,ps') ->
          (match () with
           | () ->
               ((match a with
                 | [] -> (fun s  -> FStar_Tactics_Result.Success ((), s))
                 | uu____1205 -> fail "qed: not done!"))
                 (FStar_Tactics_Types.decr_depth
                    (FStar_Tactics_Types.set_proofstate_range ps'
                       (FStar_Range.prims_to_fstar_range
                          (Prims.mk_range "FStar.Tactics.Derived.fst"
                             (Prims.of_int (91)) (Prims.of_int (4))
                             (Prims.of_int (93)) (Prims.of_int (32)))))))
      | FStar_Tactics_Result.Failed (e,ps') ->
          FStar_Tactics_Result.Failed (e, ps')
  
let (debug : Prims.string -> (unit,unit) FStar_Tactics_Effect._dm4f_TAC_repr)
  =
  fun m  ->
    fun ps  ->
      match (FStar_Tactics_Builtins.debugging ())
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.Derived.fst"
                          (Prims.of_int (99)) (Prims.of_int (7))
                          (Prims.of_int (99)) (Prims.of_int (19))))))
      with
      | FStar_Tactics_Result.Success (a,ps') ->
          (match () with
           | () ->
               (if a
                then FStar_Tactics_Builtins.print m
                else (fun s  -> FStar_Tactics_Result.Success ((), s)))
                 (FStar_Tactics_Types.decr_depth
                    (FStar_Tactics_Types.set_proofstate_range ps'
                       (FStar_Range.prims_to_fstar_range
                          (Prims.mk_range "FStar.Tactics.Derived.fst"
                             (Prims.of_int (99)) (Prims.of_int (4))
                             (Prims.of_int (99)) (Prims.of_int (32)))))))
      | FStar_Tactics_Result.Failed (e,ps') ->
          FStar_Tactics_Result.Failed (e, ps')
  
let (smt : unit -> (unit,unit) FStar_Tactics_Effect._dm4f_TAC_repr) =
  fun uu____1330  ->
    fun ps  ->
      match match (goals ())
                    (FStar_Tactics_Types.incr_depth
                       (FStar_Tactics_Types.set_proofstate_range
                          (FStar_Tactics_Types.incr_depth
                             (FStar_Tactics_Types.set_proofstate_range ps
                                (FStar_Range.prims_to_fstar_range
                                   (Prims.mk_range
                                      "FStar.Tactics.Derived.fst"
                                      (Prims.of_int (106))
                                      (Prims.of_int (10))
                                      (Prims.of_int (106))
                                      (Prims.of_int (32))))))
                          (FStar_Range.prims_to_fstar_range
                             (Prims.mk_range "FStar.Tactics.Derived.fst"
                                (Prims.of_int (106)) (Prims.of_int (10))
                                (Prims.of_int (106)) (Prims.of_int (18))))))
            with
            | FStar_Tactics_Result.Success (a,ps') ->
                (match () with
                 | () ->
                     (match (smt_goals ())
                              (FStar_Tactics_Types.incr_depth
                                 (FStar_Tactics_Types.set_proofstate_range
                                    (FStar_Tactics_Types.decr_depth
                                       (FStar_Tactics_Types.set_proofstate_range
                                          ps'
                                          (FStar_Range.prims_to_fstar_range
                                             (Prims.mk_range
                                                "FStar.Tactics.Derived.fst"
                                                (Prims.of_int (106))
                                                (Prims.of_int (10))
                                                (Prims.of_int (106))
                                                (Prims.of_int (32))))))
                                    (FStar_Range.prims_to_fstar_range
                                       (Prims.mk_range
                                          "FStar.Tactics.Derived.fst"
                                          (Prims.of_int (106))
                                          (Prims.of_int (20))
                                          (Prims.of_int (106))
                                          (Prims.of_int (32))))))
                      with
                      | FStar_Tactics_Result.Success (a1,ps'1) ->
                          (match () with
                           | () ->
                               FStar_Tactics_Result.Success
                                 ((a, a1),
                                   (FStar_Tactics_Types.decr_depth
                                      (FStar_Tactics_Types.set_proofstate_range
                                         ps'1
                                         (FStar_Range.prims_to_fstar_range
                                            (Prims.mk_range
                                               "FStar.Tactics.Derived.fst"
                                               (Prims.of_int (106))
                                               (Prims.of_int (10))
                                               (Prims.of_int (106))
                                               (Prims.of_int (32))))))))
                      | FStar_Tactics_Result.Failed (e,ps'1) ->
                          FStar_Tactics_Result.Failed (e, ps'1)))
            | FStar_Tactics_Result.Failed (e,ps') ->
                FStar_Tactics_Result.Failed (e, ps')
      with
      | FStar_Tactics_Result.Success (a,ps') ->
          (match () with
           | () ->
               ((match a with
                 | ([],uu____1558) -> fail "smt: no active goals"
                 | (g::gs,gs') ->
                     (fun ps1  ->
                        match (FStar_Tactics_Builtins.set_goals gs)
                                (FStar_Tactics_Types.incr_depth
                                   (FStar_Tactics_Types.set_proofstate_range
                                      ps1
                                      (FStar_Range.prims_to_fstar_range
                                         (Prims.mk_range
                                            "FStar.Tactics.Derived.fst"
                                            (Prims.of_int (110))
                                            (Prims.of_int (8))
                                            (Prims.of_int (110))
                                            (Prims.of_int (20))))))
                        with
                        | FStar_Tactics_Result.Success (a1,ps'1) ->
                            (match () with
                             | () ->
                                 (FStar_Tactics_Builtins.set_smt_goals (g ::
                                    gs'))
                                   (FStar_Tactics_Types.decr_depth
                                      (FStar_Tactics_Types.set_proofstate_range
                                         ps'1
                                         (FStar_Range.prims_to_fstar_range
                                            (Prims.mk_range
                                               "FStar.Tactics.Derived.fst"
                                               (Prims.of_int (111))
                                               (Prims.of_int (8))
                                               (Prims.of_int (111))
                                               (Prims.of_int (32)))))))
                        | FStar_Tactics_Result.Failed (e,ps'1) ->
                            FStar_Tactics_Result.Failed (e, ps'1))))
                 (FStar_Tactics_Types.decr_depth
                    (FStar_Tactics_Types.set_proofstate_range ps'
                       (FStar_Range.prims_to_fstar_range
                          (Prims.mk_range "FStar.Tactics.Derived.fst"
                             (Prims.of_int (106)) (Prims.of_int (4))
                             (Prims.of_int (112)) (Prims.of_int (11)))))))
      | FStar_Tactics_Result.Failed (e,ps') ->
          FStar_Tactics_Result.Failed (e, ps')
  
let (idtac : unit -> (unit,unit) FStar_Tactics_Effect._dm4f_TAC_repr) =
  fun uu____1630  -> fun s  -> FStar_Tactics_Result.Success ((), s) 
let (later : unit -> (unit,unit) FStar_Tactics_Effect._dm4f_TAC_repr) =
  fun uu____1664  ->
    fun ps  ->
      match (goals ())
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.Derived.fst"
                          (Prims.of_int (118)) (Prims.of_int (10))
                          (Prims.of_int (118)) (Prims.of_int (18))))))
      with
      | FStar_Tactics_Result.Success (a,ps') ->
          (match () with
           | () ->
               ((match a with
                 | g::gs ->
                     FStar_Tactics_Builtins.set_goals
                       (FStar_List_Tot_Base.append gs [g])
                 | uu____1727 -> fail "later: no goals"))
                 (FStar_Tactics_Types.decr_depth
                    (FStar_Tactics_Types.set_proofstate_range ps'
                       (FStar_Range.prims_to_fstar_range
                          (Prims.mk_range "FStar.Tactics.Derived.fst"
                             (Prims.of_int (118)) (Prims.of_int (4))
                             (Prims.of_int (120)) (Prims.of_int (33)))))))
      | FStar_Tactics_Result.Failed (e,ps') ->
          FStar_Tactics_Result.Failed (e, ps')
  
let (exact :
  FStar_Reflection_Types.term ->
    (unit,unit) FStar_Tactics_Effect._dm4f_TAC_repr)
  =
  fun t  ->
    with_policy FStar_Tactics_Types.SMT
      (fun uu____1763  -> FStar_Tactics_Builtins.t_exact true false t)
  
let (exact_with_ref :
  FStar_Reflection_Types.term ->
    (unit,unit) FStar_Tactics_Effect._dm4f_TAC_repr)
  =
  fun t  ->
    with_policy FStar_Tactics_Types.SMT
      (fun uu____1794  -> FStar_Tactics_Builtins.t_exact true true t)
  
let (apply :
  FStar_Reflection_Types.term ->
    (unit,unit) FStar_Tactics_Effect._dm4f_TAC_repr)
  = fun t  -> FStar_Tactics_Builtins.t_apply true false t 
let (apply_noinst :
  FStar_Reflection_Types.term ->
    (unit,unit) FStar_Tactics_Effect._dm4f_TAC_repr)
  = fun t  -> FStar_Tactics_Builtins.t_apply true true t 
let (apply_raw :
  FStar_Reflection_Types.term ->
    (unit,unit) FStar_Tactics_Effect._dm4f_TAC_repr)
  = fun t  -> FStar_Tactics_Builtins.t_apply false false t 
let (exact_guard :
  FStar_Reflection_Types.term ->
    (unit,unit) FStar_Tactics_Effect._dm4f_TAC_repr)
  =
  fun t  ->
    with_policy FStar_Tactics_Types.Goal
      (fun uu____1900  -> FStar_Tactics_Builtins.t_exact true false t)
  
let (pointwise :
  (unit -> (unit,unit) FStar_Tactics_Effect._dm4f_TAC_repr) ->
    (unit,unit) FStar_Tactics_Effect._dm4f_TAC_repr)
  =
  fun tau  ->
    FStar_Tactics_Builtins.t_pointwise FStar_Tactics_Types.BottomUp tau
  
let (pointwise' :
  (unit -> (unit,unit) FStar_Tactics_Effect._dm4f_TAC_repr) ->
    (unit,unit) FStar_Tactics_Effect._dm4f_TAC_repr)
  =
  fun tau  ->
    FStar_Tactics_Builtins.t_pointwise FStar_Tactics_Types.TopDown tau
  
let (cur_module :
  unit ->
    (FStar_Reflection_Types.name,unit) FStar_Tactics_Effect._dm4f_TAC_repr)
  =
  fun uu____2049  ->
    fun ps  ->
      match (FStar_Tactics_Builtins.top_env ())
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.Derived.fst"
                          (Prims.of_int (158)) (Prims.of_int (13))
                          (Prims.of_int (158)) (Prims.of_int (25))))))
      with
      | FStar_Tactics_Result.Success (a,ps') ->
          (match () with
           | () ->
               FStar_Tactics_Result.Success
                 ((FStar_Reflection_Basic.moduleof a),
                   (FStar_Tactics_Types.decr_depth
                      (FStar_Tactics_Types.set_proofstate_range ps'
                         (FStar_Range.prims_to_fstar_range
                            (Prims.mk_range "FStar.Tactics.Derived.fst"
                               (Prims.of_int (158)) (Prims.of_int (4))
                               (Prims.of_int (158)) (Prims.of_int (25))))))))
      | FStar_Tactics_Result.Failed (e,ps') ->
          FStar_Tactics_Result.Failed (e, ps')
  
let (open_modules :
  unit ->
    (FStar_Reflection_Types.name Prims.list,unit)
      FStar_Tactics_Effect._dm4f_TAC_repr)
  =
  fun uu____2130  ->
    fun ps  ->
      match (FStar_Tactics_Builtins.top_env ())
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.Derived.fst"
                          (Prims.of_int (161)) (Prims.of_int (21))
                          (Prims.of_int (161)) (Prims.of_int (33))))))
      with
      | FStar_Tactics_Result.Success (a,ps') ->
          (match () with
           | () ->
               FStar_Tactics_Result.Success
                 ((FStar_Reflection_Basic.env_open_modules a),
                   (FStar_Tactics_Types.decr_depth
                      (FStar_Tactics_Types.set_proofstate_range ps'
                         (FStar_Range.prims_to_fstar_range
                            (Prims.mk_range "FStar.Tactics.Derived.fst"
                               (Prims.of_int (161)) (Prims.of_int (4))
                               (Prims.of_int (161)) (Prims.of_int (33))))))))
      | FStar_Tactics_Result.Failed (e,ps') ->
          FStar_Tactics_Result.Failed (e, ps')
  
let rec repeatn :
  'Aa .
    Prims.int ->
      (unit -> ('Aa,unit) FStar_Tactics_Effect._dm4f_TAC_repr) ->
        ('Aa Prims.list,unit) FStar_Tactics_Effect._dm4f_TAC_repr
  =
  fun n1  ->
    fun t  ->
      if n1 = Prims.int_zero
      then fun s  -> FStar_Tactics_Result.Success ([], s)
      else
        (fun ps  ->
           match (t ())
                   (FStar_Tactics_Types.incr_depth
                      (FStar_Tactics_Types.set_proofstate_range ps
                         (FStar_Range.prims_to_fstar_range
                            (Prims.mk_range "FStar.Tactics.Derived.fst"
                               (Prims.of_int (166)) (Prims.of_int (9))
                               (Prims.of_int (166)) (Prims.of_int (13))))))
           with
           | FStar_Tactics_Result.Success (a,ps') ->
               (match () with
                | () ->
                    (match (repeatn (n1 - Prims.int_one) t)
                             (FStar_Tactics_Types.incr_depth
                                (FStar_Tactics_Types.set_proofstate_range
                                   (FStar_Tactics_Types.decr_depth
                                      (FStar_Tactics_Types.set_proofstate_range
                                         ps'
                                         (FStar_Range.prims_to_fstar_range
                                            (Prims.mk_range
                                               "FStar.Tactics.Derived.fst"
                                               (Prims.of_int (166))
                                               (Prims.of_int (14))
                                               (Prims.of_int (166))
                                               (Prims.of_int (16))))))
                                   (FStar_Range.prims_to_fstar_range
                                      (Prims.mk_range
                                         "FStar.Tactics.Derived.fst"
                                         (Prims.of_int (166))
                                         (Prims.of_int (17))
                                         (Prims.of_int (166))
                                         (Prims.of_int (34))))))
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
                                              "FStar.Tactics.Derived.fst"
                                              (Prims.of_int (166))
                                              (Prims.of_int (14))
                                              (Prims.of_int (166))
                                              (Prims.of_int (16))))))))
                     | FStar_Tactics_Result.Failed (e,ps'1) ->
                         FStar_Tactics_Result.Failed (e, ps'1)))
           | FStar_Tactics_Result.Failed (e,ps') ->
               FStar_Tactics_Result.Failed (e, ps'))
  
let (fresh_uvar :
  FStar_Reflection_Types.typ FStar_Pervasives_Native.option ->
    (FStar_Reflection_Types.term,unit) FStar_Tactics_Effect._dm4f_TAC_repr)
  =
  fun o  ->
    fun ps  ->
      match (cur_env ())
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.Derived.fst"
                          (Prims.of_int (169)) (Prims.of_int (12))
                          (Prims.of_int (169)) (Prims.of_int (22))))))
      with
      | FStar_Tactics_Result.Success (a,ps') ->
          (match () with
           | () ->
               (FStar_Tactics_Builtins.uvar_env a o)
                 (FStar_Tactics_Types.decr_depth
                    (FStar_Tactics_Types.set_proofstate_range ps'
                       (FStar_Range.prims_to_fstar_range
                          (Prims.mk_range "FStar.Tactics.Derived.fst"
                             (Prims.of_int (170)) (Prims.of_int (4))
                             (Prims.of_int (170)) (Prims.of_int (16)))))))
      | FStar_Tactics_Result.Failed (e,ps') ->
          FStar_Tactics_Result.Failed (e, ps')
  
let (unify :
  FStar_Reflection_Types.term ->
    FStar_Reflection_Types.term ->
      (Prims.bool,unit) FStar_Tactics_Effect._dm4f_TAC_repr)
  =
  fun t1  ->
    fun t2  ->
      fun ps  ->
        match (cur_env ())
                (FStar_Tactics_Types.incr_depth
                   (FStar_Tactics_Types.set_proofstate_range ps
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range "FStar.Tactics.Derived.fst"
                            (Prims.of_int (173)) (Prims.of_int (12))
                            (Prims.of_int (173)) (Prims.of_int (22))))))
        with
        | FStar_Tactics_Result.Success (a,ps') ->
            (match () with
             | () ->
                 (FStar_Tactics_Builtins.unify_env a t1 t2)
                   (FStar_Tactics_Types.decr_depth
                      (FStar_Tactics_Types.set_proofstate_range ps'
                         (FStar_Range.prims_to_fstar_range
                            (Prims.mk_range "FStar.Tactics.Derived.fst"
                               (Prims.of_int (174)) (Prims.of_int (4))
                               (Prims.of_int (174)) (Prims.of_int (21)))))))
        | FStar_Tactics_Result.Failed (e,ps') ->
            FStar_Tactics_Result.Failed (e, ps')
  
let divide :
  'a 'b .
    Prims.int ->
      (unit -> ('a,unit) FStar_Tactics_Effect._dm4f_TAC_repr) ->
        (unit -> ('b,unit) FStar_Tactics_Effect._dm4f_TAC_repr) ->
          (('a * 'b),unit) FStar_Tactics_Effect._dm4f_TAC_repr
  =
  fun n1  ->
    fun l  ->
      fun r  ->
        fun ps  ->
          match (if n1 < Prims.int_zero
                 then fail "divide: negative n"
                 else (fun s  -> FStar_Tactics_Result.Success ((), s)))
                  (FStar_Tactics_Types.incr_depth
                     (FStar_Tactics_Types.set_proofstate_range ps
                        (FStar_Range.prims_to_fstar_range
                           (Prims.mk_range "FStar.Tactics.Derived.fst"
                              (Prims.of_int (181)) (Prims.of_int (4))
                              (Prims.of_int (182)) (Prims.of_int (31))))))
          with
          | FStar_Tactics_Result.Success (a,ps') ->
              (match () with
               | () ->
                   (match match (goals ())
                                  (FStar_Tactics_Types.incr_depth
                                     (FStar_Tactics_Types.set_proofstate_range
                                        (FStar_Tactics_Types.incr_depth
                                           (FStar_Tactics_Types.set_proofstate_range
                                              (FStar_Tactics_Types.decr_depth
                                                 (FStar_Tactics_Types.set_proofstate_range
                                                    ps'
                                                    (FStar_Range.prims_to_fstar_range
                                                       (Prims.mk_range
                                                          "FStar.Tactics.Derived.fst"
                                                          (Prims.of_int (183))
                                                          (Prims.of_int (4))
                                                          (Prims.of_int (195))
                                                          (Prims.of_int (10))))))
                                              (FStar_Range.prims_to_fstar_range
                                                 (Prims.mk_range
                                                    "FStar.Tactics.Derived.fst"
                                                    (Prims.of_int (183))
                                                    (Prims.of_int (18))
                                                    (Prims.of_int (183))
                                                    (Prims.of_int (40))))))
                                        (FStar_Range.prims_to_fstar_range
                                           (Prims.mk_range
                                              "FStar.Tactics.Derived.fst"
                                              (Prims.of_int (183))
                                              (Prims.of_int (18))
                                              (Prims.of_int (183))
                                              (Prims.of_int (26))))))
                          with
                          | FStar_Tactics_Result.Success (a1,ps'1) ->
                              (match () with
                               | () ->
                                   (match (smt_goals ())
                                            (FStar_Tactics_Types.incr_depth
                                               (FStar_Tactics_Types.set_proofstate_range
                                                  (FStar_Tactics_Types.decr_depth
                                                     (FStar_Tactics_Types.set_proofstate_range
                                                        ps'1
                                                        (FStar_Range.prims_to_fstar_range
                                                           (Prims.mk_range
                                                              "FStar.Tactics.Derived.fst"
                                                              (Prims.of_int (183))
                                                              (Prims.of_int (18))
                                                              (Prims.of_int (183))
                                                              (Prims.of_int (40))))))
                                                  (FStar_Range.prims_to_fstar_range
                                                     (Prims.mk_range
                                                        "FStar.Tactics.Derived.fst"
                                                        (Prims.of_int (183))
                                                        (Prims.of_int (28))
                                                        (Prims.of_int (183))
                                                        (Prims.of_int (40))))))
                                    with
                                    | FStar_Tactics_Result.Success (a2,ps'2)
                                        ->
                                        (match () with
                                         | () ->
                                             FStar_Tactics_Result.Success
                                               ((a1, a2),
                                                 (FStar_Tactics_Types.decr_depth
                                                    (FStar_Tactics_Types.set_proofstate_range
                                                       ps'2
                                                       (FStar_Range.prims_to_fstar_range
                                                          (Prims.mk_range
                                                             "FStar.Tactics.Derived.fst"
                                                             (Prims.of_int (183))
                                                             (Prims.of_int (18))
                                                             (Prims.of_int (183))
                                                             (Prims.of_int (40))))))))
                                    | FStar_Tactics_Result.Failed (e,ps'2) ->
                                        FStar_Tactics_Result.Failed (e, ps'2)))
                          | FStar_Tactics_Result.Failed (e,ps'1) ->
                              FStar_Tactics_Result.Failed (e, ps'1)
                    with
                    | FStar_Tactics_Result.Success (a1,ps'1) ->
                        (match () with
                         | () ->
                             ((match a1 with
                               | (gs,sgs) ->
                                   (fun ps1  ->
                                      match () with
                                      | () ->
                                          ((match FStar_List_Tot_Base.splitAt
                                                    n1 gs
                                            with
                                            | (gs1,gs2) ->
                                                (fun ps2  ->
                                                   match (FStar_Tactics_Builtins.set_goals
                                                            gs1)
                                                           (FStar_Tactics_Types.incr_depth
                                                              (FStar_Tactics_Types.set_proofstate_range
                                                                 ps2
                                                                 (FStar_Range.prims_to_fstar_range
                                                                    (
                                                                    Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (186))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (186))
                                                                    (Prims.of_int (17))))))
                                                   with
                                                   | FStar_Tactics_Result.Success
                                                       (a2,ps'2) ->
                                                       (match () with
                                                        | () ->
                                                            (match (FStar_Tactics_Builtins.set_smt_goals
                                                                    [])
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (186))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (195))
                                                                    (Prims.of_int (10))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (186))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (186))
                                                                    (Prims.of_int (35))))))
                                                             with
                                                             | FStar_Tactics_Result.Success
                                                                 (a3,ps'3) ->
                                                                 (match ()
                                                                  with
                                                                  | () ->
                                                                    (match 
                                                                    (l ())
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (187))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (195))
                                                                    (Prims.of_int (10))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (187))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (187))
                                                                    (Prims.of_int (16))))))
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
                                                                    match 
                                                                    (goals ())
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'4
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (188))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (195))
                                                                    (Prims.of_int (10))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (188))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (188))
                                                                    (Prims.of_int (42))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (188))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (188))
                                                                    (Prims.of_int (28))))))
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
                                                                    (smt_goals
                                                                    ())
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'5
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (188))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (188))
                                                                    (Prims.of_int (42))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (188))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (188))
                                                                    (Prims.of_int (42))))))
                                                                    with
                                                                    | 
                                                                    FStar_Tactics_Result.Success
                                                                    (a6,ps'6)
                                                                    ->
                                                                    (match ()
                                                                    with
                                                                    | 
                                                                    () ->
                                                                    FStar_Tactics_Result.Success
                                                                    ((a5, a6),
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'6
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (188))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (188))
                                                                    (Prims.of_int (42))))))))
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
                                                                    ((match a5
                                                                    with
                                                                    | (gsl,sgsl)
                                                                    ->
                                                                    (fun ps3 
                                                                    ->
                                                                    match 
                                                                    (FStar_Tactics_Builtins.set_goals
                                                                    gs2)
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (190))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (190))
                                                                    (Prims.of_int (17))))))
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
                                                                    (FStar_Tactics_Builtins.set_smt_goals
                                                                    [])
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'6
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (190))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (195))
                                                                    (Prims.of_int (10))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (190))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (190))
                                                                    (Prims.of_int (35))))))
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
                                                                    (r ())
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'7
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (191))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (195))
                                                                    (Prims.of_int (10))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (191))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (191))
                                                                    (Prims.of_int (16))))))
                                                                    with
                                                                    | 
                                                                    FStar_Tactics_Result.Success
                                                                    (a8,ps'8)
                                                                    ->
                                                                    (match ()
                                                                    with
                                                                    | 
                                                                    () ->
                                                                    (match 
                                                                    match 
                                                                    (goals ())
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'8
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (192))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (195))
                                                                    (Prims.of_int (10))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (192))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (192))
                                                                    (Prims.of_int (42))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (192))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (192))
                                                                    (Prims.of_int (28))))))
                                                                    with
                                                                    | 
                                                                    FStar_Tactics_Result.Success
                                                                    (a9,ps'9)
                                                                    ->
                                                                    (match ()
                                                                    with
                                                                    | 
                                                                    () ->
                                                                    (match 
                                                                    (smt_goals
                                                                    ())
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'9
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (192))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (192))
                                                                    (Prims.of_int (42))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (192))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (192))
                                                                    (Prims.of_int (42))))))
                                                                    with
                                                                    | 
                                                                    FStar_Tactics_Result.Success
                                                                    (a10,ps'10)
                                                                    ->
                                                                    (match ()
                                                                    with
                                                                    | 
                                                                    () ->
                                                                    FStar_Tactics_Result.Success
                                                                    ((a9,
                                                                    a10),
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'10
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (192))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (192))
                                                                    (Prims.of_int (42))))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e,ps'10)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e,
                                                                    ps'10)))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e,ps'9)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'9)
                                                                    with
                                                                    | 
                                                                    FStar_Tactics_Result.Success
                                                                    (a9,ps'9)
                                                                    ->
                                                                    (match ()
                                                                    with
                                                                    | 
                                                                    () ->
                                                                    ((match a9
                                                                    with
                                                                    | (gsr,sgsr)
                                                                    ->
                                                                    (fun ps4 
                                                                    ->
                                                                    match 
                                                                    (FStar_Tactics_Builtins.set_goals
                                                                    (FStar_List_Tot_Base.append
                                                                    gsl gsr))
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps4
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (194))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (194))
                                                                    (Prims.of_int (25))))))
                                                                    with
                                                                    | 
                                                                    FStar_Tactics_Result.Success
                                                                    (a10,ps'10)
                                                                    ->
                                                                    (match ()
                                                                    with
                                                                    | 
                                                                    () ->
                                                                    (match 
                                                                    (FStar_Tactics_Builtins.set_smt_goals
                                                                    (FStar_List_Tot_Base.append
                                                                    sgs
                                                                    (FStar_List_Tot_Base.append
                                                                    sgsl sgsr)))
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'10
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (194))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (195))
                                                                    (Prims.of_int (10))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (194))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (194))
                                                                    (Prims.of_int (60))))))
                                                                    with
                                                                    | 
                                                                    FStar_Tactics_Result.Success
                                                                    (a11,ps'11)
                                                                    ->
                                                                    (match ()
                                                                    with
                                                                    | 
                                                                    () ->
                                                                    FStar_Tactics_Result.Success
                                                                    ((a4, a8),
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'11
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (195))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (195))
                                                                    (Prims.of_int (10))))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e,ps'11)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e,
                                                                    ps'11)))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e,ps'10)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e,
                                                                    ps'10))))
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'9
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (192))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (195))
                                                                    (Prims.of_int (10)))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e,ps'9)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'9)))
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
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'5
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (188))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (195))
                                                                    (Prims.of_int (10)))))))
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
                                                             | FStar_Tactics_Result.Failed
                                                                 (e,ps'3) ->
                                                                 FStar_Tactics_Result.Failed
                                                                   (e, ps'3)))
                                                   | FStar_Tactics_Result.Failed
                                                       (e,ps'2) ->
                                                       FStar_Tactics_Result.Failed
                                                         (e, ps'2))))
                                            (FStar_Tactics_Types.decr_depth
                                               (FStar_Tactics_Types.set_proofstate_range
                                                  (FStar_Tactics_Types.incr_depth
                                                     (FStar_Tactics_Types.set_proofstate_range
                                                        ps1
                                                        (FStar_Range.prims_to_fstar_range
                                                           (Prims.mk_range
                                                              "FStar.Tactics.Derived.fst"
                                                              (Prims.of_int (184))
                                                              (Prims.of_int (19))
                                                              (Prims.of_int (184))
                                                              (Prims.of_int (40))))))
                                                  (FStar_Range.prims_to_fstar_range
                                                     (Prims.mk_range
                                                        "FStar.Tactics.Derived.fst"
                                                        (Prims.of_int (184))
                                                        (Prims.of_int (4))
                                                        (Prims.of_int (195))
                                                        (Prims.of_int (10)))))))))
                               (FStar_Tactics_Types.decr_depth
                                  (FStar_Tactics_Types.set_proofstate_range
                                     ps'1
                                     (FStar_Range.prims_to_fstar_range
                                        (Prims.mk_range
                                           "FStar.Tactics.Derived.fst"
                                           (Prims.of_int (183))
                                           (Prims.of_int (4))
                                           (Prims.of_int (195))
                                           (Prims.of_int (10)))))))
                    | FStar_Tactics_Result.Failed (e,ps'1) ->
                        FStar_Tactics_Result.Failed (e, ps'1)))
          | FStar_Tactics_Result.Failed (e,ps') ->
              FStar_Tactics_Result.Failed (e, ps')
  
let focus :
  'a .
    (unit -> ('a,unit) FStar_Tactics_Effect._dm4f_TAC_repr) ->
      ('a,unit) FStar_Tactics_Effect._dm4f_TAC_repr
  =
  fun t  ->
    fun ps  ->
      match (goals ())
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.Derived.fst"
                          (Prims.of_int (200)) (Prims.of_int (10))
                          (Prims.of_int (200)) (Prims.of_int (18))))))
      with
      | FStar_Tactics_Result.Success (a,ps') ->
          (match () with
           | () ->
               ((match a with
                 | [] -> fail "focus: no goals"
                 | g::gs ->
                     (fun ps1  ->
                        match (smt_goals ())
                                (FStar_Tactics_Types.incr_depth
                                   (FStar_Tactics_Types.set_proofstate_range
                                      ps1
                                      (FStar_Range.prims_to_fstar_range
                                         (Prims.mk_range
                                            "FStar.Tactics.Derived.fst"
                                            (Prims.of_int (203))
                                            (Prims.of_int (18))
                                            (Prims.of_int (203))
                                            (Prims.of_int (30))))))
                        with
                        | FStar_Tactics_Result.Success (a1,ps'1) ->
                            (match () with
                             | () ->
                                 (match (FStar_Tactics_Builtins.set_goals [g])
                                          (FStar_Tactics_Types.incr_depth
                                             (FStar_Tactics_Types.set_proofstate_range
                                                (FStar_Tactics_Types.decr_depth
                                                   (FStar_Tactics_Types.set_proofstate_range
                                                      ps'1
                                                      (FStar_Range.prims_to_fstar_range
                                                         (Prims.mk_range
                                                            "FStar.Tactics.Derived.fst"
                                                            (Prims.of_int (204))
                                                            (Prims.of_int (8))
                                                            (Prims.of_int (207))
                                                            (Prims.of_int (9))))))
                                                (FStar_Range.prims_to_fstar_range
                                                   (Prims.mk_range
                                                      "FStar.Tactics.Derived.fst"
                                                      (Prims.of_int (204))
                                                      (Prims.of_int (8))
                                                      (Prims.of_int (204))
                                                      (Prims.of_int (21))))))
                                  with
                                  | FStar_Tactics_Result.Success (a2,ps'2) ->
                                      (match () with
                                       | () ->
                                           (match (FStar_Tactics_Builtins.set_smt_goals
                                                     [])
                                                    (FStar_Tactics_Types.incr_depth
                                                       (FStar_Tactics_Types.set_proofstate_range
                                                          (FStar_Tactics_Types.decr_depth
                                                             (FStar_Tactics_Types.set_proofstate_range
                                                                ps'2
                                                                (FStar_Range.prims_to_fstar_range
                                                                   (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (204))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (207))
                                                                    (Prims.of_int (9))))))
                                                          (FStar_Range.prims_to_fstar_range
                                                             (Prims.mk_range
                                                                "FStar.Tactics.Derived.fst"
                                                                (Prims.of_int (204))
                                                                (Prims.of_int (23))
                                                                (Prims.of_int (204))
                                                                (Prims.of_int (39))))))
                                            with
                                            | FStar_Tactics_Result.Success
                                                (a3,ps'3) ->
                                                (match () with
                                                 | () ->
                                                     (match (t ())
                                                              (FStar_Tactics_Types.incr_depth
                                                                 (FStar_Tactics_Types.set_proofstate_range
                                                                    (
                                                                    FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (205))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (207))
                                                                    (Prims.of_int (9))))))
                                                                    (
                                                                    FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (205))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (205))
                                                                    (Prims.of_int (20))))))
                                                      with
                                                      | FStar_Tactics_Result.Success
                                                          (a4,ps'4) ->
                                                          (match () with
                                                           | () ->
                                                               (match 
                                                                  match 
                                                                    match 
                                                                    (goals ())
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'4
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (206))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (207))
                                                                    (Prims.of_int (9))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (206))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (206))
                                                                    (Prims.of_int (33))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (206))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (206))
                                                                    (Prims.of_int (33))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (206))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (206))
                                                                    (Prims.of_int (27))))))
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
                                                                    ((FStar_List_Tot_Base.append
                                                                    a5 gs),
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'5
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (206))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (206))
                                                                    (Prims.of_int (33))))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e,ps'5)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'5)
                                                                  with
                                                                  | FStar_Tactics_Result.Success
                                                                    (a5,ps'5)
                                                                    ->
                                                                    (match ()
                                                                    with
                                                                    | 
                                                                    () ->
                                                                    (FStar_Tactics_Builtins.set_goals
                                                                    a5)
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'5
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (206))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (206))
                                                                    (Prims.of_int (33)))))))
                                                                  | FStar_Tactics_Result.Failed
                                                                    (e,ps'5)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'5)
                                                                with
                                                                | FStar_Tactics_Result.Success
                                                                    (a5,ps'5)
                                                                    ->
                                                                    (
                                                                    match ()
                                                                    with
                                                                    | 
                                                                    () ->
                                                                    (match 
                                                                    match 
                                                                    match 
                                                                    (smt_goals
                                                                    ())
                                                                    (FStar_Tactics_Types.incr_depth
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
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (206))
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (207))
                                                                    (Prims.of_int (9))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (206))
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (206))
                                                                    (Prims.of_int (69))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (206))
                                                                    (Prims.of_int (49))
                                                                    (Prims.of_int (206))
                                                                    (Prims.of_int (69))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (206))
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (206))
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
                                                                    FStar_Tactics_Result.Success
                                                                    ((FStar_List_Tot_Base.append
                                                                    a6 a1),
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'6
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (206))
                                                                    (Prims.of_int (49))
                                                                    (Prims.of_int (206))
                                                                    (Prims.of_int (69))))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e,ps'6)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'6)
                                                                    with
                                                                    | 
                                                                    FStar_Tactics_Result.Success
                                                                    (a6,ps'6)
                                                                    ->
                                                                    (match ()
                                                                    with
                                                                    | 
                                                                    () ->
                                                                    (FStar_Tactics_Builtins.set_smt_goals
                                                                    a6)
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'6
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (206))
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (206))
                                                                    (Prims.of_int (69)))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e,ps'6)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'6)
                                                                    with
                                                                    | 
                                                                    FStar_Tactics_Result.Success
                                                                    (a6,ps'6)
                                                                    ->
                                                                    (match ()
                                                                    with
                                                                    | 
                                                                    () ->
                                                                    FStar_Tactics_Result.Success
                                                                    (a4,
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'6
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Effect.fst"
                                                                    (Prims.of_int (42))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (42))
                                                                    (Prims.of_int (19))))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e,ps'6)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'6)))
                                                                | FStar_Tactics_Result.Failed
                                                                    (e,ps'5)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'5)))
                                                      | FStar_Tactics_Result.Failed
                                                          (e,ps'4) ->
                                                          FStar_Tactics_Result.Failed
                                                            (e, ps'4)))
                                            | FStar_Tactics_Result.Failed
                                                (e,ps'3) ->
                                                FStar_Tactics_Result.Failed
                                                  (e, ps'3)))
                                  | FStar_Tactics_Result.Failed (e,ps'2) ->
                                      FStar_Tactics_Result.Failed (e, ps'2)))
                        | FStar_Tactics_Result.Failed (e,ps'1) ->
                            FStar_Tactics_Result.Failed (e, ps'1))))
                 (FStar_Tactics_Types.decr_depth
                    (FStar_Tactics_Types.set_proofstate_range ps'
                       (FStar_Range.prims_to_fstar_range
                          (Prims.mk_range "FStar.Tactics.Derived.fst"
                             (Prims.of_int (200)) (Prims.of_int (4))
                             (Prims.of_int (207)) (Prims.of_int (9)))))))
      | FStar_Tactics_Result.Failed (e,ps') ->
          FStar_Tactics_Result.Failed (e, ps')
  
let (dump1 : Prims.string -> (unit,unit) FStar_Tactics_Effect._dm4f_TAC_repr)
  = fun m  -> focus (fun uu____4662  -> FStar_Tactics_Builtins.dump m) 
let rec mapAll :
  'a .
    (unit -> ('a,unit) FStar_Tactics_Effect._dm4f_TAC_repr) ->
      ('a Prims.list,unit) FStar_Tactics_Effect._dm4f_TAC_repr
  =
  fun t  ->
    fun ps  ->
      match (goals ())
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.Derived.fst"
                          (Prims.of_int (213)) (Prims.of_int (10))
                          (Prims.of_int (213)) (Prims.of_int (18))))))
      with
      | FStar_Tactics_Result.Success (a,ps') ->
          (match () with
           | () ->
               ((match a with
                 | [] -> (fun s  -> FStar_Tactics_Result.Success ([], s))
                 | uu____4862::uu____4863 ->
                     (fun ps1  ->
                        match (divide Prims.int_one t
                                 (fun uu____4890  -> mapAll t))
                                (FStar_Tactics_Types.incr_depth
                                   (FStar_Tactics_Types.set_proofstate_range
                                      ps1
                                      (FStar_Range.prims_to_fstar_range
                                         (Prims.mk_range
                                            "FStar.Tactics.Derived.fst"
                                            (Prims.of_int (215))
                                            (Prims.of_int (27))
                                            (Prims.of_int (215))
                                            (Prims.of_int (58))))))
                        with
                        | FStar_Tactics_Result.Success (a1,ps'1) ->
                            (match () with
                             | () ->
                                 FStar_Tactics_Result.Success
                                   (((match a1 with | (h,t1) -> h :: t1)),
                                     (FStar_Tactics_Types.decr_depth
                                        (FStar_Tactics_Types.set_proofstate_range
                                           ps'1
                                           (FStar_Range.prims_to_fstar_range
                                              (Prims.mk_range
                                                 "FStar.Tactics.Derived.fst"
                                                 (Prims.of_int (215))
                                                 (Prims.of_int (14))
                                                 (Prims.of_int (215))
                                                 (Prims.of_int (66))))))))
                        | FStar_Tactics_Result.Failed (e,ps'1) ->
                            FStar_Tactics_Result.Failed (e, ps'1))))
                 (FStar_Tactics_Types.decr_depth
                    (FStar_Tactics_Types.set_proofstate_range ps'
                       (FStar_Range.prims_to_fstar_range
                          (Prims.mk_range "FStar.Tactics.Derived.fst"
                             (Prims.of_int (213)) (Prims.of_int (4))
                             (Prims.of_int (215)) (Prims.of_int (66)))))))
      | FStar_Tactics_Result.Failed (e,ps') ->
          FStar_Tactics_Result.Failed (e, ps')
  
let rec (iterAll :
  (unit -> (unit,unit) FStar_Tactics_Effect._dm4f_TAC_repr) ->
    (unit,unit) FStar_Tactics_Effect._dm4f_TAC_repr)
  =
  fun t  ->
    fun ps  ->
      match (goals ())
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.Derived.fst"
                          (Prims.of_int (219)) (Prims.of_int (10))
                          (Prims.of_int (219)) (Prims.of_int (18))))))
      with
      | FStar_Tactics_Result.Success (a,ps') ->
          (match () with
           | () ->
               ((match a with
                 | [] -> (fun s  -> FStar_Tactics_Result.Success ((), s))
                 | uu____5101::uu____5102 ->
                     (fun ps1  ->
                        match (divide Prims.int_one t
                                 (fun uu____5123  -> iterAll t))
                                (FStar_Tactics_Types.incr_depth
                                   (FStar_Tactics_Types.set_proofstate_range
                                      ps1
                                      (FStar_Range.prims_to_fstar_range
                                         (Prims.mk_range
                                            "FStar.Tactics.Derived.fst"
                                            (Prims.of_int (221))
                                            (Prims.of_int (22))
                                            (Prims.of_int (221))
                                            (Prims.of_int (54))))))
                        with
                        | FStar_Tactics_Result.Success (a1,ps'1) ->
                            (match () with
                             | () ->
                                 FStar_Tactics_Result.Success
                                   ((),
                                     (FStar_Tactics_Types.decr_depth
                                        (FStar_Tactics_Types.set_proofstate_range
                                           ps'1
                                           (FStar_Range.prims_to_fstar_range
                                              (Prims.mk_range
                                                 "FStar.Tactics.Derived.fst"
                                                 (Prims.of_int (221))
                                                 (Prims.of_int (58))
                                                 (Prims.of_int (221))
                                                 (Prims.of_int (60))))))))
                        | FStar_Tactics_Result.Failed (e,ps'1) ->
                            FStar_Tactics_Result.Failed (e, ps'1))))
                 (FStar_Tactics_Types.decr_depth
                    (FStar_Tactics_Types.set_proofstate_range ps'
                       (FStar_Range.prims_to_fstar_range
                          (Prims.mk_range "FStar.Tactics.Derived.fst"
                             (Prims.of_int (219)) (Prims.of_int (4))
                             (Prims.of_int (221)) (Prims.of_int (60)))))))
      | FStar_Tactics_Result.Failed (e,ps') ->
          FStar_Tactics_Result.Failed (e, ps')
  
let (iterAllSMT :
  (unit -> (unit,unit) FStar_Tactics_Effect._dm4f_TAC_repr) ->
    (unit,unit) FStar_Tactics_Effect._dm4f_TAC_repr)
  =
  fun t  ->
    fun ps  ->
      match match (goals ())
                    (FStar_Tactics_Types.incr_depth
                       (FStar_Tactics_Types.set_proofstate_range
                          (FStar_Tactics_Types.incr_depth
                             (FStar_Tactics_Types.set_proofstate_range ps
                                (FStar_Range.prims_to_fstar_range
                                   (Prims.mk_range
                                      "FStar.Tactics.Derived.fst"
                                      (Prims.of_int (224))
                                      (Prims.of_int (18))
                                      (Prims.of_int (224))
                                      (Prims.of_int (40))))))
                          (FStar_Range.prims_to_fstar_range
                             (Prims.mk_range "FStar.Tactics.Derived.fst"
                                (Prims.of_int (224)) (Prims.of_int (18))
                                (Prims.of_int (224)) (Prims.of_int (26))))))
            with
            | FStar_Tactics_Result.Success (a,ps') ->
                (match () with
                 | () ->
                     (match (smt_goals ())
                              (FStar_Tactics_Types.incr_depth
                                 (FStar_Tactics_Types.set_proofstate_range
                                    (FStar_Tactics_Types.decr_depth
                                       (FStar_Tactics_Types.set_proofstate_range
                                          ps'
                                          (FStar_Range.prims_to_fstar_range
                                             (Prims.mk_range
                                                "FStar.Tactics.Derived.fst"
                                                (Prims.of_int (224))
                                                (Prims.of_int (18))
                                                (Prims.of_int (224))
                                                (Prims.of_int (40))))))
                                    (FStar_Range.prims_to_fstar_range
                                       (Prims.mk_range
                                          "FStar.Tactics.Derived.fst"
                                          (Prims.of_int (224))
                                          (Prims.of_int (28))
                                          (Prims.of_int (224))
                                          (Prims.of_int (40))))))
                      with
                      | FStar_Tactics_Result.Success (a1,ps'1) ->
                          (match () with
                           | () ->
                               FStar_Tactics_Result.Success
                                 ((a, a1),
                                   (FStar_Tactics_Types.decr_depth
                                      (FStar_Tactics_Types.set_proofstate_range
                                         ps'1
                                         (FStar_Range.prims_to_fstar_range
                                            (Prims.mk_range
                                               "FStar.Tactics.Derived.fst"
                                               (Prims.of_int (224))
                                               (Prims.of_int (18))
                                               (Prims.of_int (224))
                                               (Prims.of_int (40))))))))
                      | FStar_Tactics_Result.Failed (e,ps'1) ->
                          FStar_Tactics_Result.Failed (e, ps'1)))
            | FStar_Tactics_Result.Failed (e,ps') ->
                FStar_Tactics_Result.Failed (e, ps')
      with
      | FStar_Tactics_Result.Success (a,ps') ->
          (match () with
           | () ->
               ((match a with
                 | (gs,sgs) ->
                     (fun ps1  ->
                        match (FStar_Tactics_Builtins.set_goals sgs)
                                (FStar_Tactics_Types.incr_depth
                                   (FStar_Tactics_Types.set_proofstate_range
                                      ps1
                                      (FStar_Range.prims_to_fstar_range
                                         (Prims.mk_range
                                            "FStar.Tactics.Derived.fst"
                                            (Prims.of_int (225))
                                            (Prims.of_int (4))
                                            (Prims.of_int (225))
                                            (Prims.of_int (17))))))
                        with
                        | FStar_Tactics_Result.Success (a1,ps'1) ->
                            (match () with
                             | () ->
                                 (match (FStar_Tactics_Builtins.set_smt_goals
                                           [])
                                          (FStar_Tactics_Types.incr_depth
                                             (FStar_Tactics_Types.set_proofstate_range
                                                (FStar_Tactics_Types.decr_depth
                                                   (FStar_Tactics_Types.set_proofstate_range
                                                      ps'1
                                                      (FStar_Range.prims_to_fstar_range
                                                         (Prims.mk_range
                                                            "FStar.Tactics.Derived.fst"
                                                            (Prims.of_int (226))
                                                            (Prims.of_int (4))
                                                            (Prims.of_int (230))
                                                            (Prims.of_int (28))))))
                                                (FStar_Range.prims_to_fstar_range
                                                   (Prims.mk_range
                                                      "FStar.Tactics.Derived.fst"
                                                      (Prims.of_int (226))
                                                      (Prims.of_int (4))
                                                      (Prims.of_int (226))
                                                      (Prims.of_int (20))))))
                                  with
                                  | FStar_Tactics_Result.Success (a2,ps'2) ->
                                      (match () with
                                       | () ->
                                           (match (iterAll t)
                                                    (FStar_Tactics_Types.incr_depth
                                                       (FStar_Tactics_Types.set_proofstate_range
                                                          (FStar_Tactics_Types.decr_depth
                                                             (FStar_Tactics_Types.set_proofstate_range
                                                                ps'2
                                                                (FStar_Range.prims_to_fstar_range
                                                                   (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (227))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (230))
                                                                    (Prims.of_int (28))))))
                                                          (FStar_Range.prims_to_fstar_range
                                                             (Prims.mk_range
                                                                "FStar.Tactics.Derived.fst"
                                                                (Prims.of_int (227))
                                                                (Prims.of_int (4))
                                                                (Prims.of_int (227))
                                                                (Prims.of_int (13))))))
                                            with
                                            | FStar_Tactics_Result.Success
                                                (a3,ps'3) ->
                                                (match () with
                                                 | () ->
                                                     (match match (goals ())
                                                                    (
                                                                    FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (228))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (230))
                                                                    (Prims.of_int (28))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (228))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (228))
                                                                    (Prims.of_int (42))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (228))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (228))
                                                                    (Prims.of_int (28))))))
                                                            with
                                                            | FStar_Tactics_Result.Success
                                                                (a4,ps'4) ->
                                                                (match ()
                                                                 with
                                                                 | () ->
                                                                    (match 
                                                                    (smt_goals
                                                                    ())
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'4
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (228))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (228))
                                                                    (Prims.of_int (42))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (228))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (228))
                                                                    (Prims.of_int (42))))))
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
                                                                    ((a4, a5),
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'5
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (228))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (228))
                                                                    (Prims.of_int (42))))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e,ps'5)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'5)))
                                                            | FStar_Tactics_Result.Failed
                                                                (e,ps'4) ->
                                                                FStar_Tactics_Result.Failed
                                                                  (e, ps'4)
                                                      with
                                                      | FStar_Tactics_Result.Success
                                                          (a4,ps'4) ->
                                                          (match () with
                                                           | () ->
                                                               ((match a4
                                                                 with
                                                                 | (gs',sgs')
                                                                    ->
                                                                    (fun ps2 
                                                                    ->
                                                                    match 
                                                                    (FStar_Tactics_Builtins.set_goals
                                                                    gs)
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (229))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (229))
                                                                    (Prims.of_int (16))))))
                                                                    with
                                                                    | 
                                                                    FStar_Tactics_Result.Success
                                                                    (a5,ps'5)
                                                                    ->
                                                                    (match ()
                                                                    with
                                                                    | 
                                                                    () ->
                                                                    (FStar_Tactics_Builtins.set_smt_goals
                                                                    (FStar_List_Tot_Base.append
                                                                    gs' sgs'))
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'5
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (230))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (230))
                                                                    (Prims.of_int (28)))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e,ps'5)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'5))))
                                                                 (FStar_Tactics_Types.decr_depth
                                                                    (
                                                                    FStar_Tactics_Types.set_proofstate_range
                                                                    ps'4
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (228))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (230))
                                                                    (Prims.of_int (28)))))))
                                                      | FStar_Tactics_Result.Failed
                                                          (e,ps'4) ->
                                                          FStar_Tactics_Result.Failed
                                                            (e, ps'4)))
                                            | FStar_Tactics_Result.Failed
                                                (e,ps'3) ->
                                                FStar_Tactics_Result.Failed
                                                  (e, ps'3)))
                                  | FStar_Tactics_Result.Failed (e,ps'2) ->
                                      FStar_Tactics_Result.Failed (e, ps'2)))
                        | FStar_Tactics_Result.Failed (e,ps'1) ->
                            FStar_Tactics_Result.Failed (e, ps'1))))
                 (FStar_Tactics_Types.decr_depth
                    (FStar_Tactics_Types.set_proofstate_range ps'
                       (FStar_Range.prims_to_fstar_range
                          (Prims.mk_range "FStar.Tactics.Derived.fst"
                             (Prims.of_int (224)) (Prims.of_int (4))
                             (Prims.of_int (230)) (Prims.of_int (28)))))))
      | FStar_Tactics_Result.Failed (e,ps') ->
          FStar_Tactics_Result.Failed (e, ps')
  
let (seq :
  (unit -> (unit,unit) FStar_Tactics_Effect._dm4f_TAC_repr) ->
    (unit -> (unit,unit) FStar_Tactics_Effect._dm4f_TAC_repr) ->
      (unit,unit) FStar_Tactics_Effect._dm4f_TAC_repr)
  =
  fun f  ->
    fun g  ->
      focus
        (fun uu____5940  ->
           fun ps  ->
             match (f ())
                     (FStar_Tactics_Types.incr_depth
                        (FStar_Tactics_Types.set_proofstate_range ps
                           (FStar_Range.prims_to_fstar_range
                              (Prims.mk_range "FStar.Tactics.Derived.fst"
                                 (Prims.of_int (236)) (Prims.of_int (21))
                                 (Prims.of_int (236)) (Prims.of_int (25))))))
             with
             | FStar_Tactics_Result.Success (a,ps') ->
                 (match () with
                  | () ->
                      (iterAll g)
                        (FStar_Tactics_Types.decr_depth
                           (FStar_Tactics_Types.set_proofstate_range ps'
                              (FStar_Range.prims_to_fstar_range
                                 (Prims.mk_range "FStar.Tactics.Derived.fst"
                                    (Prims.of_int (236)) (Prims.of_int (27))
                                    (Prims.of_int (236)) (Prims.of_int (36)))))))
             | FStar_Tactics_Result.Failed (e,ps') ->
                 FStar_Tactics_Result.Failed (e, ps'))
  
let (exact_args :
  FStar_Reflection_Data.aqualv Prims.list ->
    FStar_Reflection_Types.term ->
      (unit,unit) FStar_Tactics_Effect._dm4f_TAC_repr)
  =
  fun qs  ->
    fun t  ->
      focus
        (fun uu____6059  ->
           fun ps  ->
             match () with
             | () ->
                 (match (repeatn (FStar_List_Tot_Base.length qs)
                           (fun uu____6175  ->
                              fresh_uvar FStar_Pervasives_Native.None))
                          (FStar_Tactics_Types.incr_depth
                             (FStar_Tactics_Types.set_proofstate_range
                                (FStar_Tactics_Types.decr_depth
                                   (FStar_Tactics_Types.set_proofstate_range
                                      (FStar_Tactics_Types.incr_depth
                                         (FStar_Tactics_Types.set_proofstate_range
                                            ps
                                            (FStar_Range.prims_to_fstar_range
                                               (Prims.mk_range
                                                  "FStar.Tactics.Derived.fst"
                                                  (Prims.of_int (240))
                                                  (Prims.of_int (16))
                                                  (Prims.of_int (240))
                                                  (Prims.of_int (30))))))
                                      (FStar_Range.prims_to_fstar_range
                                         (Prims.mk_range
                                            "FStar.Tactics.Derived.fst"
                                            (Prims.of_int (241))
                                            (Prims.of_int (8))
                                            (Prims.of_int (246))
                                            (Prims.of_int (44))))))
                                (FStar_Range.prims_to_fstar_range
                                   (Prims.mk_range
                                      "FStar.Tactics.Derived.fst"
                                      (Prims.of_int (241))
                                      (Prims.of_int (18))
                                      (Prims.of_int (241))
                                      (Prims.of_int (55))))))
                  with
                  | FStar_Tactics_Result.Success (a,ps') ->
                      (match () with
                       | () ->
                           (match match (FStar_Tactics_Util.zip a qs)
                                          (FStar_Tactics_Types.incr_depth
                                             (FStar_Tactics_Types.set_proofstate_range
                                                (FStar_Tactics_Types.incr_depth
                                                   (FStar_Tactics_Types.set_proofstate_range
                                                      (FStar_Tactics_Types.decr_depth
                                                         (FStar_Tactics_Types.set_proofstate_range
                                                            ps'
                                                            (FStar_Range.prims_to_fstar_range
                                                               (Prims.mk_range
                                                                  "FStar.Tactics.Derived.fst"
                                                                  (Prims.of_int (242))
                                                                  (Prims.of_int (8))
                                                                  (Prims.of_int (246))
                                                                  (Prims.of_int (44))))))
                                                      (FStar_Range.prims_to_fstar_range
                                                         (Prims.mk_range
                                                            "FStar.Tactics.Derived.fst"
                                                            (Prims.of_int (242))
                                                            (Prims.of_int (17))
                                                            (Prims.of_int (242))
                                                            (Prims.of_int (38))))))
                                                (FStar_Range.prims_to_fstar_range
                                                   (Prims.mk_range
                                                      "FStar.Tactics.Derived.fst"
                                                      (Prims.of_int (242))
                                                      (Prims.of_int (26))
                                                      (Prims.of_int (242))
                                                      (Prims.of_int (38))))))
                                  with
                                  | FStar_Tactics_Result.Success (a1,ps'1) ->
                                      (match () with
                                       | () ->
                                           FStar_Tactics_Result.Success
                                             ((FStar_Reflection_Derived.mk_app
                                                 t a1),
                                               (FStar_Tactics_Types.decr_depth
                                                  (FStar_Tactics_Types.set_proofstate_range
                                                     ps'1
                                                     (FStar_Range.prims_to_fstar_range
                                                        (Prims.mk_range
                                                           "FStar.Tactics.Derived.fst"
                                                           (Prims.of_int (242))
                                                           (Prims.of_int (17))
                                                           (Prims.of_int (242))
                                                           (Prims.of_int (38))))))))
                                  | FStar_Tactics_Result.Failed (e,ps'1) ->
                                      FStar_Tactics_Result.Failed (e, ps'1)
                            with
                            | FStar_Tactics_Result.Success (a1,ps'1) ->
                                (match () with
                                 | () ->
                                     (match (exact a1)
                                              (FStar_Tactics_Types.incr_depth
                                                 (FStar_Tactics_Types.set_proofstate_range
                                                    (FStar_Tactics_Types.decr_depth
                                                       (FStar_Tactics_Types.set_proofstate_range
                                                          ps'1
                                                          (FStar_Range.prims_to_fstar_range
                                                             (Prims.mk_range
                                                                "FStar.Tactics.Derived.fst"
                                                                (Prims.of_int (243))
                                                                (Prims.of_int (8))
                                                                (Prims.of_int (246))
                                                                (Prims.of_int (44))))))
                                                    (FStar_Range.prims_to_fstar_range
                                                       (Prims.mk_range
                                                          "FStar.Tactics.Derived.fst"
                                                          (Prims.of_int (243))
                                                          (Prims.of_int (8))
                                                          (Prims.of_int (243))
                                                          (Prims.of_int (16))))))
                                      with
                                      | FStar_Tactics_Result.Success
                                          (a2,ps'2) ->
                                          (match () with
                                           | () ->
                                               (FStar_Tactics_Util.iter
                                                  (fun uv  ->
                                                     if
                                                       FStar_Reflection_Derived.is_uvar
                                                         uv
                                                     then
                                                       FStar_Tactics_Builtins.unshelve
                                                         uv
                                                     else
                                                       (fun s  ->
                                                          FStar_Tactics_Result.Success
                                                            ((), s)))
                                                  (FStar_List_Tot_Base.rev a))
                                                 (FStar_Tactics_Types.decr_depth
                                                    (FStar_Tactics_Types.set_proofstate_range
                                                       ps'2
                                                       (FStar_Range.prims_to_fstar_range
                                                          (Prims.mk_range
                                                             "FStar.Tactics.Derived.fst"
                                                             (Prims.of_int (244))
                                                             (Prims.of_int (8))
                                                             (Prims.of_int (246))
                                                             (Prims.of_int (44)))))))
                                      | FStar_Tactics_Result.Failed (e,ps'2)
                                          ->
                                          FStar_Tactics_Result.Failed
                                            (e, ps'2)))
                            | FStar_Tactics_Result.Failed (e,ps'1) ->
                                FStar_Tactics_Result.Failed (e, ps'1)))
                  | FStar_Tactics_Result.Failed (e,ps') ->
                      FStar_Tactics_Result.Failed (e, ps')))
  
let (exact_n :
  Prims.int ->
    FStar_Reflection_Types.term ->
      (unit,unit) FStar_Tactics_Effect._dm4f_TAC_repr)
  =
  fun n1  ->
    fun t  ->
      fun ps  ->
        match (repeatn n1
                 (fun uu____6310  ->
                    fun s  ->
                      FStar_Tactics_Result.Success
                        (FStar_Reflection_Data.Q_Explicit, s)))
                (FStar_Tactics_Types.incr_depth
                   (FStar_Tactics_Types.set_proofstate_range ps
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range "FStar.Tactics.Derived.fst"
                            (Prims.of_int (250)) (Prims.of_int (15))
                            (Prims.of_int (250)) (Prims.of_int (49))))))
        with
        | FStar_Tactics_Result.Success (a,ps') ->
            (match () with
             | () ->
                 (exact_args a t)
                   (FStar_Tactics_Types.decr_depth
                      (FStar_Tactics_Types.set_proofstate_range ps'
                         (FStar_Range.prims_to_fstar_range
                            (Prims.mk_range "FStar.Tactics.Derived.fst"
                               (Prims.of_int (250)) (Prims.of_int (4))
                               (Prims.of_int (250)) (Prims.of_int (51)))))))
        | FStar_Tactics_Result.Failed (e,ps') ->
            FStar_Tactics_Result.Failed (e, ps')
  
let (ngoals : unit -> (Prims.int,unit) FStar_Tactics_Effect._dm4f_TAC_repr) =
  fun uu____6353  ->
    fun ps  ->
      match (goals ())
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.Derived.fst"
                          (Prims.of_int (253)) (Prims.of_int (38))
                          (Prims.of_int (253)) (Prims.of_int (48))))))
      with
      | FStar_Tactics_Result.Success (a,ps') ->
          (match () with
           | () ->
               FStar_Tactics_Result.Success
                 ((FStar_List_Tot_Base.length a),
                   (FStar_Tactics_Types.decr_depth
                      (FStar_Tactics_Types.set_proofstate_range ps'
                         (FStar_Range.prims_to_fstar_range
                            (Prims.mk_range "FStar.Tactics.Derived.fst"
                               (Prims.of_int (253)) (Prims.of_int (26))
                               (Prims.of_int (253)) (Prims.of_int (48))))))))
      | FStar_Tactics_Result.Failed (e,ps') ->
          FStar_Tactics_Result.Failed (e, ps')
  
let (ngoals_smt :
  unit -> (Prims.int,unit) FStar_Tactics_Effect._dm4f_TAC_repr) =
  fun uu____6432  ->
    fun ps  ->
      match (smt_goals ())
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.Derived.fst"
                          (Prims.of_int (256)) (Prims.of_int (42))
                          (Prims.of_int (256)) (Prims.of_int (56))))))
      with
      | FStar_Tactics_Result.Success (a,ps') ->
          (match () with
           | () ->
               FStar_Tactics_Result.Success
                 ((FStar_List_Tot_Base.length a),
                   (FStar_Tactics_Types.decr_depth
                      (FStar_Tactics_Types.set_proofstate_range ps'
                         (FStar_Range.prims_to_fstar_range
                            (Prims.mk_range "FStar.Tactics.Derived.fst"
                               (Prims.of_int (256)) (Prims.of_int (30))
                               (Prims.of_int (256)) (Prims.of_int (56))))))))
      | FStar_Tactics_Result.Failed (e,ps') ->
          FStar_Tactics_Result.Failed (e, ps')
  
let (fresh_bv :
  FStar_Reflection_Types.typ ->
    (FStar_Reflection_Types.bv,unit) FStar_Tactics_Effect._dm4f_TAC_repr)
  =
  fun t  ->
    fun ps  ->
      match (FStar_Tactics_Builtins.fresh ())
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.Derived.fst"
                          (Prims.of_int (262)) (Prims.of_int (12))
                          (Prims.of_int (262)) (Prims.of_int (20))))))
      with
      | FStar_Tactics_Result.Success (a,ps') ->
          (match () with
           | () ->
               (FStar_Tactics_Builtins.fresh_bv_named
                  (Prims.strcat "x" (Prims.string_of_int a)) t)
                 (FStar_Tactics_Types.decr_depth
                    (FStar_Tactics_Types.set_proofstate_range ps'
                       (FStar_Range.prims_to_fstar_range
                          (Prims.mk_range "FStar.Tactics.Derived.fst"
                             (Prims.of_int (263)) (Prims.of_int (4))
                             (Prims.of_int (263)) (Prims.of_int (44)))))))
      | FStar_Tactics_Result.Failed (e,ps') ->
          FStar_Tactics_Result.Failed (e, ps')
  
let (fresh_binder_named :
  Prims.string ->
    FStar_Reflection_Types.typ ->
      (FStar_Reflection_Types.binder,unit)
        FStar_Tactics_Effect._dm4f_TAC_repr)
  =
  fun nm  ->
    fun t  ->
      fun ps  ->
        match (FStar_Tactics_Builtins.fresh_bv_named nm t)
                (FStar_Tactics_Types.incr_depth
                   (FStar_Tactics_Types.set_proofstate_range ps
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range "FStar.Tactics.Derived.fst"
                            (Prims.of_int (266)) (Prims.of_int (14))
                            (Prims.of_int (266)) (Prims.of_int (35))))))
        with
        | FStar_Tactics_Result.Success (a,ps') ->
            (match () with
             | () ->
                 FStar_Tactics_Result.Success
                   ((FStar_Reflection_Derived.mk_binder a),
                     (FStar_Tactics_Types.decr_depth
                        (FStar_Tactics_Types.set_proofstate_range ps'
                           (FStar_Range.prims_to_fstar_range
                              (Prims.mk_range "FStar.Tactics.Derived.fst"
                                 (Prims.of_int (266)) (Prims.of_int (4))
                                 (Prims.of_int (266)) (Prims.of_int (35))))))))
        | FStar_Tactics_Result.Failed (e,ps') ->
            FStar_Tactics_Result.Failed (e, ps')
  
let (fresh_binder :
  FStar_Reflection_Types.typ ->
    (FStar_Reflection_Types.binder,unit) FStar_Tactics_Effect._dm4f_TAC_repr)
  =
  fun t  ->
    fun ps  ->
      match (FStar_Tactics_Builtins.fresh ())
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.Derived.fst"
                          (Prims.of_int (270)) (Prims.of_int (12))
                          (Prims.of_int (270)) (Prims.of_int (20))))))
      with
      | FStar_Tactics_Result.Success (a,ps') ->
          (match () with
           | () ->
               (fresh_binder_named (Prims.strcat "x" (Prims.string_of_int a))
                  t)
                 (FStar_Tactics_Types.decr_depth
                    (FStar_Tactics_Types.set_proofstate_range ps'
                       (FStar_Range.prims_to_fstar_range
                          (Prims.mk_range "FStar.Tactics.Derived.fst"
                             (Prims.of_int (271)) (Prims.of_int (4))
                             (Prims.of_int (271)) (Prims.of_int (48)))))))
      | FStar_Tactics_Result.Failed (e,ps') ->
          FStar_Tactics_Result.Failed (e, ps')
  
let (guard : Prims.bool -> (unit,unit) FStar_Tactics_Effect._dm4f_TAC_repr) =
  fun b  ->
    if Prims.op_Negation b
    then fail "guard failed"
    else (fun s  -> FStar_Tactics_Result.Success ((), s))
  
let try_with :
  'a .
    (unit -> ('a,unit) FStar_Tactics_Effect._dm4f_TAC_repr) ->
      (Prims.exn -> ('a,unit) FStar_Tactics_Effect._dm4f_TAC_repr) ->
        ('a,unit) FStar_Tactics_Effect._dm4f_TAC_repr
  =
  fun f  ->
    fun h  ->
      fun ps  ->
        match (FStar_Tactics_Builtins.catch f)
                (FStar_Tactics_Types.incr_depth
                   (FStar_Tactics_Types.set_proofstate_range ps
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range "FStar.Tactics.Derived.fst"
                            (Prims.of_int (284)) (Prims.of_int (10))
                            (Prims.of_int (284)) (Prims.of_int (17))))))
        with
        | FStar_Tactics_Result.Success (a,ps') ->
            (match () with
             | () ->
                 ((match a with
                   | FStar_Pervasives.Inl e -> h e
                   | FStar_Pervasives.Inr x ->
                       (fun s  -> FStar_Tactics_Result.Success (x, s))))
                   (FStar_Tactics_Types.decr_depth
                      (FStar_Tactics_Types.set_proofstate_range ps'
                         (FStar_Range.prims_to_fstar_range
                            (Prims.mk_range "FStar.Tactics.Derived.fst"
                               (Prims.of_int (284)) (Prims.of_int (4))
                               (Prims.of_int (286)) (Prims.of_int (16)))))))
        | FStar_Tactics_Result.Failed (e,ps') ->
            FStar_Tactics_Result.Failed (e, ps')
  
let trytac :
  'a .
    (unit -> ('a,unit) FStar_Tactics_Effect._dm4f_TAC_repr) ->
      ('a FStar_Pervasives_Native.option,unit)
        FStar_Tactics_Effect._dm4f_TAC_repr
  =
  fun t  ->
    try_with
      (fun uu___200_7023  ->
         match () with
         | () ->
             (fun ps  ->
                match (t ())
                        (FStar_Tactics_Types.incr_depth
                           (FStar_Tactics_Types.set_proofstate_range ps
                              (FStar_Range.prims_to_fstar_range
                                 (Prims.mk_range "FStar.Tactics.Derived.fst"
                                    (Prims.of_int (289)) (Prims.of_int (13))
                                    (Prims.of_int (289)) (Prims.of_int (19))))))
                with
                | FStar_Tactics_Result.Success (a,ps') ->
                    (match () with
                     | () ->
                         FStar_Tactics_Result.Success
                           ((FStar_Pervasives_Native.Some a),
                             (FStar_Tactics_Types.decr_depth
                                (FStar_Tactics_Types.set_proofstate_range ps'
                                   (FStar_Range.prims_to_fstar_range
                                      (Prims.mk_range
                                         "FStar.Tactics.Derived.fst"
                                         (Prims.of_int (289))
                                         (Prims.of_int (8))
                                         (Prims.of_int (289))
                                         (Prims.of_int (19))))))))
                | FStar_Tactics_Result.Failed (e,ps') ->
                    FStar_Tactics_Result.Failed (e, ps')))
      (fun uu___199_7088  ->
         fun s  ->
           FStar_Tactics_Result.Success (FStar_Pervasives_Native.None, s))
  
let or_else :
  'Aa .
    (unit -> ('Aa,unit) FStar_Tactics_Effect._dm4f_TAC_repr) ->
      (unit -> ('Aa,unit) FStar_Tactics_Effect._dm4f_TAC_repr) ->
        ('Aa,unit) FStar_Tactics_Effect._dm4f_TAC_repr
  =
  fun t1  ->
    fun t2  ->
      try_with (fun uu___209_7223  -> match () with | () -> t1 ())
        (fun uu___208_7225  -> t2 ())
  
let op_Less_Bar_Greater :
  'a .
    (unit -> ('a,unit) FStar_Tactics_Effect._dm4f_TAC_repr) ->
      (unit -> ('a,unit) FStar_Tactics_Effect._dm4f_TAC_repr) ->
        unit -> ('a,unit) FStar_Tactics_Effect._dm4f_TAC_repr
  = fun t1  -> fun t2  -> fun uu____7310  -> or_else t1 t2 
let first :
  'a .
    (unit -> ('a,unit) FStar_Tactics_Effect._dm4f_TAC_repr) Prims.list ->
      ('a,unit) FStar_Tactics_Effect._dm4f_TAC_repr
  =
  fun ts  ->
    FStar_List_Tot_Base.fold_right op_Less_Bar_Greater ts
      (fun uu____7469  -> fail "no tactics to try") ()
  
let rec repeat :
  'Aa .
    (unit -> ('Aa,unit) FStar_Tactics_Effect._dm4f_TAC_repr) ->
      ('Aa Prims.list,unit) FStar_Tactics_Effect._dm4f_TAC_repr
  =
  fun t  ->
    fun ps  ->
      match (FStar_Tactics_Builtins.catch t)
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.Derived.fst"
                          (Prims.of_int (306)) (Prims.of_int (10))
                          (Prims.of_int (306)) (Prims.of_int (17))))))
      with
      | FStar_Tactics_Result.Success (a,ps') ->
          (match () with
           | () ->
               ((match a with
                 | FStar_Pervasives.Inl uu____7649 ->
                     (fun s  -> FStar_Tactics_Result.Success ([], s))
                 | FStar_Pervasives.Inr x ->
                     (fun ps1  ->
                        match (repeat t)
                                (FStar_Tactics_Types.incr_depth
                                   (FStar_Tactics_Types.set_proofstate_range
                                      ps1
                                      (FStar_Range.prims_to_fstar_range
                                         (Prims.mk_range
                                            "FStar.Tactics.Derived.fst"
                                            (Prims.of_int (308))
                                            (Prims.of_int (20))
                                            (Prims.of_int (308))
                                            (Prims.of_int (28))))))
                        with
                        | FStar_Tactics_Result.Success (a1,ps'1) ->
                            (match () with
                             | () ->
                                 FStar_Tactics_Result.Success
                                   ((x :: a1),
                                     (FStar_Tactics_Types.decr_depth
                                        (FStar_Tactics_Types.set_proofstate_range
                                           ps'1
                                           (FStar_Range.prims_to_fstar_range
                                              (Prims.mk_range
                                                 "FStar.Tactics.Derived.fst"
                                                 (Prims.of_int (308))
                                                 (Prims.of_int (17))
                                                 (Prims.of_int (308))
                                                 (Prims.of_int (19))))))))
                        | FStar_Tactics_Result.Failed (e,ps'1) ->
                            FStar_Tactics_Result.Failed (e, ps'1))))
                 (FStar_Tactics_Types.decr_depth
                    (FStar_Tactics_Types.set_proofstate_range ps'
                       (FStar_Range.prims_to_fstar_range
                          (Prims.mk_range "FStar.Tactics.Derived.fst"
                             (Prims.of_int (306)) (Prims.of_int (4))
                             (Prims.of_int (308)) (Prims.of_int (28)))))))
      | FStar_Tactics_Result.Failed (e,ps') ->
          FStar_Tactics_Result.Failed (e, ps')
  
let repeat1 :
  'Aa .
    (unit -> ('Aa,unit) FStar_Tactics_Effect._dm4f_TAC_repr) ->
      ('Aa Prims.list,unit) FStar_Tactics_Effect._dm4f_TAC_repr
  =
  fun t  ->
    fun ps  ->
      match (t ())
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.Derived.fst"
                          (Prims.of_int (311)) (Prims.of_int (4))
                          (Prims.of_int (311)) (Prims.of_int (8))))))
      with
      | FStar_Tactics_Result.Success (a,ps') ->
          (match () with
           | () ->
               (match (repeat t)
                        (FStar_Tactics_Types.incr_depth
                           (FStar_Tactics_Types.set_proofstate_range
                              (FStar_Tactics_Types.decr_depth
                                 (FStar_Tactics_Types.set_proofstate_range
                                    ps'
                                    (FStar_Range.prims_to_fstar_range
                                       (Prims.mk_range
                                          "FStar.Tactics.Derived.fst"
                                          (Prims.of_int (311))
                                          (Prims.of_int (9))
                                          (Prims.of_int (311))
                                          (Prims.of_int (11))))))
                              (FStar_Range.prims_to_fstar_range
                                 (Prims.mk_range "FStar.Tactics.Derived.fst"
                                    (Prims.of_int (311)) (Prims.of_int (12))
                                    (Prims.of_int (311)) (Prims.of_int (20))))))
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
                                         "FStar.Tactics.Derived.fst"
                                         (Prims.of_int (311))
                                         (Prims.of_int (9))
                                         (Prims.of_int (311))
                                         (Prims.of_int (11))))))))
                | FStar_Tactics_Result.Failed (e,ps'1) ->
                    FStar_Tactics_Result.Failed (e, ps'1)))
      | FStar_Tactics_Result.Failed (e,ps') ->
          FStar_Tactics_Result.Failed (e, ps')
  
let repeat' :
  'a .
    (unit -> ('a,unit) FStar_Tactics_Effect._dm4f_TAC_repr) ->
      (unit,unit) FStar_Tactics_Effect._dm4f_TAC_repr
  =
  fun f  ->
    fun ps  ->
      match (repeat f)
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.Derived.fst"
                          (Prims.of_int (314)) (Prims.of_int (12))
                          (Prims.of_int (314)) (Prims.of_int (20))))))
      with
      | FStar_Tactics_Result.Success (a,ps') ->
          (match () with
           | () ->
               FStar_Tactics_Result.Success
                 ((),
                   (FStar_Tactics_Types.decr_depth
                      (FStar_Tactics_Types.set_proofstate_range ps'
                         (FStar_Range.prims_to_fstar_range
                            (Prims.mk_range "FStar.Tactics.Derived.fst"
                               (Prims.of_int (314)) (Prims.of_int (24))
                               (Prims.of_int (314)) (Prims.of_int (26))))))))
      | FStar_Tactics_Result.Failed (e,ps') ->
          FStar_Tactics_Result.Failed (e, ps')
  
let (norm_term :
  FStar_Pervasives.norm_step Prims.list ->
    FStar_Reflection_Types.term ->
      (FStar_Reflection_Types.term,unit) FStar_Tactics_Effect._dm4f_TAC_repr)
  =
  fun s  ->
    fun t  ->
      fun ps  ->
        match (try_with
                 (fun uu___235_8080  -> match () with | () -> cur_env ())
                 (fun uu___234_8082  -> FStar_Tactics_Builtins.top_env ()))
                (FStar_Tactics_Types.incr_depth
                   (FStar_Tactics_Types.set_proofstate_range ps
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range "FStar.Tactics.Derived.fst"
                            (Prims.of_int (318)) (Prims.of_int (8))
                            (Prims.of_int (319)) (Prims.of_int (30))))))
        with
        | FStar_Tactics_Result.Success (a,ps') ->
            (match () with
             | () ->
                 (FStar_Tactics_Builtins.norm_term_env a s t)
                   (FStar_Tactics_Types.decr_depth
                      (FStar_Tactics_Types.set_proofstate_range ps'
                         (FStar_Range.prims_to_fstar_range
                            (Prims.mk_range "FStar.Tactics.Derived.fst"
                               (Prims.of_int (321)) (Prims.of_int (4))
                               (Prims.of_int (321)) (Prims.of_int (23)))))))
        | FStar_Tactics_Result.Failed (e,ps') ->
            FStar_Tactics_Result.Failed (e, ps')
  
let (join_all_smt_goals :
  unit -> (unit,unit) FStar_Tactics_Effect._dm4f_TAC_repr) =
  fun uu____8191  ->
    fun ps  ->
      match match (goals ())
                    (FStar_Tactics_Types.incr_depth
                       (FStar_Tactics_Types.set_proofstate_range
                          (FStar_Tactics_Types.incr_depth
                             (FStar_Tactics_Types.set_proofstate_range ps
                                (FStar_Range.prims_to_fstar_range
                                   (Prims.mk_range
                                      "FStar.Tactics.Derived.fst"
                                      (Prims.of_int (328))
                                      (Prims.of_int (16))
                                      (Prims.of_int (328))
                                      (Prims.of_int (38))))))
                          (FStar_Range.prims_to_fstar_range
                             (Prims.mk_range "FStar.Tactics.Derived.fst"
                                (Prims.of_int (328)) (Prims.of_int (16))
                                (Prims.of_int (328)) (Prims.of_int (24))))))
            with
            | FStar_Tactics_Result.Success (a,ps') ->
                (match () with
                 | () ->
                     (match (smt_goals ())
                              (FStar_Tactics_Types.incr_depth
                                 (FStar_Tactics_Types.set_proofstate_range
                                    (FStar_Tactics_Types.decr_depth
                                       (FStar_Tactics_Types.set_proofstate_range
                                          ps'
                                          (FStar_Range.prims_to_fstar_range
                                             (Prims.mk_range
                                                "FStar.Tactics.Derived.fst"
                                                (Prims.of_int (328))
                                                (Prims.of_int (16))
                                                (Prims.of_int (328))
                                                (Prims.of_int (38))))))
                                    (FStar_Range.prims_to_fstar_range
                                       (Prims.mk_range
                                          "FStar.Tactics.Derived.fst"
                                          (Prims.of_int (328))
                                          (Prims.of_int (26))
                                          (Prims.of_int (328))
                                          (Prims.of_int (38))))))
                      with
                      | FStar_Tactics_Result.Success (a1,ps'1) ->
                          (match () with
                           | () ->
                               FStar_Tactics_Result.Success
                                 ((a, a1),
                                   (FStar_Tactics_Types.decr_depth
                                      (FStar_Tactics_Types.set_proofstate_range
                                         ps'1
                                         (FStar_Range.prims_to_fstar_range
                                            (Prims.mk_range
                                               "FStar.Tactics.Derived.fst"
                                               (Prims.of_int (328))
                                               (Prims.of_int (16))
                                               (Prims.of_int (328))
                                               (Prims.of_int (38))))))))
                      | FStar_Tactics_Result.Failed (e,ps'1) ->
                          FStar_Tactics_Result.Failed (e, ps'1)))
            | FStar_Tactics_Result.Failed (e,ps') ->
                FStar_Tactics_Result.Failed (e, ps')
      with
      | FStar_Tactics_Result.Success (a,ps') ->
          (match () with
           | () ->
               ((match a with
                 | (gs,sgs) ->
                     (fun ps1  ->
                        match (FStar_Tactics_Builtins.set_smt_goals [])
                                (FStar_Tactics_Types.incr_depth
                                   (FStar_Tactics_Types.set_proofstate_range
                                      ps1
                                      (FStar_Range.prims_to_fstar_range
                                         (Prims.mk_range
                                            "FStar.Tactics.Derived.fst"
                                            (Prims.of_int (329))
                                            (Prims.of_int (2))
                                            (Prims.of_int (329))
                                            (Prims.of_int (18))))))
                        with
                        | FStar_Tactics_Result.Success (a1,ps'1) ->
                            (match () with
                             | () ->
                                 (match (FStar_Tactics_Builtins.set_goals sgs)
                                          (FStar_Tactics_Types.incr_depth
                                             (FStar_Tactics_Types.set_proofstate_range
                                                (FStar_Tactics_Types.decr_depth
                                                   (FStar_Tactics_Types.set_proofstate_range
                                                      ps'1
                                                      (FStar_Range.prims_to_fstar_range
                                                         (Prims.mk_range
                                                            "FStar.Tactics.Derived.fst"
                                                            (Prims.of_int (330))
                                                            (Prims.of_int (2))
                                                            (Prims.of_int (334))
                                                            (Prims.of_int (20))))))
                                                (FStar_Range.prims_to_fstar_range
                                                   (Prims.mk_range
                                                      "FStar.Tactics.Derived.fst"
                                                      (Prims.of_int (330))
                                                      (Prims.of_int (2))
                                                      (Prims.of_int (330))
                                                      (Prims.of_int (15))))))
                                  with
                                  | FStar_Tactics_Result.Success (a2,ps'2) ->
                                      (match () with
                                       | () ->
                                           (match (repeat'
                                                     FStar_Tactics_Builtins.join)
                                                    (FStar_Tactics_Types.incr_depth
                                                       (FStar_Tactics_Types.set_proofstate_range
                                                          (FStar_Tactics_Types.decr_depth
                                                             (FStar_Tactics_Types.set_proofstate_range
                                                                ps'2
                                                                (FStar_Range.prims_to_fstar_range
                                                                   (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (331))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (334))
                                                                    (Prims.of_int (20))))))
                                                          (FStar_Range.prims_to_fstar_range
                                                             (Prims.mk_range
                                                                "FStar.Tactics.Derived.fst"
                                                                (Prims.of_int (331))
                                                                (Prims.of_int (2))
                                                                (Prims.of_int (331))
                                                                (Prims.of_int (14))))))
                                            with
                                            | FStar_Tactics_Result.Success
                                                (a3,ps'3) ->
                                                (match () with
                                                 | () ->
                                                     (match (goals ())
                                                              (FStar_Tactics_Types.incr_depth
                                                                 (FStar_Tactics_Types.set_proofstate_range
                                                                    (
                                                                    FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (332))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (334))
                                                                    (Prims.of_int (20))))))
                                                                    (
                                                                    FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (332))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (332))
                                                                    (Prims.of_int (21))))))
                                                      with
                                                      | FStar_Tactics_Result.Success
                                                          (a4,ps'4) ->
                                                          (match () with
                                                           | () ->
                                                               (match 
                                                                  (FStar_Tactics_Builtins.set_goals
                                                                    gs)
                                                                    (
                                                                    FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'4
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (333))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (334))
                                                                    (Prims.of_int (20))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (333))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (333))
                                                                    (Prims.of_int (14))))))
                                                                with
                                                                | FStar_Tactics_Result.Success
                                                                    (a5,ps'5)
                                                                    ->
                                                                    (
                                                                    match ()
                                                                    with
                                                                    | 
                                                                    () ->
                                                                    (FStar_Tactics_Builtins.set_smt_goals
                                                                    a4)
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'5
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (334))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (334))
                                                                    (Prims.of_int (20)))))))
                                                                | FStar_Tactics_Result.Failed
                                                                    (e,ps'5)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'5)))
                                                      | FStar_Tactics_Result.Failed
                                                          (e,ps'4) ->
                                                          FStar_Tactics_Result.Failed
                                                            (e, ps'4)))
                                            | FStar_Tactics_Result.Failed
                                                (e,ps'3) ->
                                                FStar_Tactics_Result.Failed
                                                  (e, ps'3)))
                                  | FStar_Tactics_Result.Failed (e,ps'2) ->
                                      FStar_Tactics_Result.Failed (e, ps'2)))
                        | FStar_Tactics_Result.Failed (e,ps'1) ->
                            FStar_Tactics_Result.Failed (e, ps'1))))
                 (FStar_Tactics_Types.decr_depth
                    (FStar_Tactics_Types.set_proofstate_range ps'
                       (FStar_Range.prims_to_fstar_range
                          (Prims.mk_range "FStar.Tactics.Derived.fst"
                             (Prims.of_int (328)) (Prims.of_int (2))
                             (Prims.of_int (334)) (Prims.of_int (20)))))))
      | FStar_Tactics_Result.Failed (e,ps') ->
          FStar_Tactics_Result.Failed (e, ps')
  
let discard :
  'a .
    (unit -> ('a,unit) FStar_Tactics_Effect._dm4f_TAC_repr) ->
      unit -> (unit,unit) FStar_Tactics_Effect._dm4f_TAC_repr
  =
  fun tau  ->
    fun uu____8636  ->
      fun ps  ->
        match (tau ())
                (FStar_Tactics_Types.incr_depth
                   (FStar_Tactics_Types.set_proofstate_range ps
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range "FStar.Tactics.Derived.fst"
                            (Prims.of_int (337)) (Prims.of_int (22))
                            (Prims.of_int (337)) (Prims.of_int (28))))))
        with
        | FStar_Tactics_Result.Success (a,ps') ->
            (match () with
             | () ->
                 FStar_Tactics_Result.Success
                   ((),
                     (FStar_Tactics_Types.decr_depth
                        (FStar_Tactics_Types.set_proofstate_range ps'
                           (FStar_Range.prims_to_fstar_range
                              (Prims.mk_range "FStar.Tactics.Derived.fst"
                                 (Prims.of_int (337)) (Prims.of_int (32))
                                 (Prims.of_int (337)) (Prims.of_int (34))))))))
        | FStar_Tactics_Result.Failed (e,ps') ->
            FStar_Tactics_Result.Failed (e, ps')
  
let rec repeatseq :
  'Aa .
    (unit -> ('Aa,unit) FStar_Tactics_Effect._dm4f_TAC_repr) ->
      (unit,unit) FStar_Tactics_Effect._dm4f_TAC_repr
  =
  fun t  ->
    fun ps  ->
      match (trytac
               (fun uu____8823  ->
                  seq (discard t) (discard (fun uu____8828  -> repeatseq t))))
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.Derived.fst"
                          (Prims.of_int (341)) (Prims.of_int (12))
                          (Prims.of_int (341)) (Prims.of_int (82))))))
      with
      | FStar_Tactics_Result.Success (a,ps') ->
          (match () with
           | () ->
               FStar_Tactics_Result.Success
                 ((),
                   (FStar_Tactics_Types.decr_depth
                      (FStar_Tactics_Types.set_proofstate_range ps'
                         (FStar_Range.prims_to_fstar_range
                            (Prims.mk_range "FStar.Tactics.Derived.fst"
                               (Prims.of_int (341)) (Prims.of_int (86))
                               (Prims.of_int (341)) (Prims.of_int (88))))))))
      | FStar_Tactics_Result.Failed (e,ps') ->
          FStar_Tactics_Result.Failed (e, ps')
  
let (tadmit : unit -> (unit,unit) FStar_Tactics_Effect._dm4f_TAC_repr) =
  fun uu____8865  ->
    FStar_Tactics_Builtins.tadmit_t
      (FStar_Reflection_Basic.pack_ln
         (FStar_Reflection_Data.Tv_Const FStar_Reflection_Data.C_Unit))
  
let (admit1 : unit -> (unit,unit) FStar_Tactics_Effect._dm4f_TAC_repr) =
  fun uu____8888  -> tadmit () 
let (admit_all : unit -> (unit,unit) FStar_Tactics_Effect._dm4f_TAC_repr) =
  fun uu____8912  ->
    fun ps  ->
      match (repeat tadmit)
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.Derived.fst"
                          (Prims.of_int (349)) (Prims.of_int (12))
                          (Prims.of_int (349)) (Prims.of_int (25))))))
      with
      | FStar_Tactics_Result.Success (a,ps') ->
          (match () with
           | () ->
               FStar_Tactics_Result.Success
                 ((),
                   (FStar_Tactics_Types.decr_depth
                      (FStar_Tactics_Types.set_proofstate_range ps'
                         (FStar_Range.prims_to_fstar_range
                            (Prims.mk_range "FStar.Tactics.Derived.fst"
                               (Prims.of_int (350)) (Prims.of_int (4))
                               (Prims.of_int (350)) (Prims.of_int (6))))))))
      | FStar_Tactics_Result.Failed (e,ps') ->
          FStar_Tactics_Result.Failed (e, ps')
  
let (is_guard :
  unit -> (Prims.bool,unit) FStar_Tactics_Effect._dm4f_TAC_repr) =
  fun uu____8993  ->
    fun ps  ->
      match (_cur_goal ())
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.Derived.fst"
                          (Prims.of_int (354)) (Prims.of_int (27))
                          (Prims.of_int (354)) (Prims.of_int (41))))))
      with
      | FStar_Tactics_Result.Success (a,ps') ->
          (match () with
           | () ->
               FStar_Tactics_Result.Success
                 ((FStar_Tactics_Types.is_guard a),
                   (FStar_Tactics_Types.decr_depth
                      (FStar_Tactics_Types.set_proofstate_range ps'
                         (FStar_Range.prims_to_fstar_range
                            (Prims.mk_range "FStar.Tactics.Derived.fst"
                               (Prims.of_int (354)) (Prims.of_int (4))
                               (Prims.of_int (354)) (Prims.of_int (41))))))))
      | FStar_Tactics_Result.Failed (e,ps') ->
          FStar_Tactics_Result.Failed (e, ps')
  
let (skip_guard : unit -> (unit,unit) FStar_Tactics_Effect._dm4f_TAC_repr) =
  fun uu____9072  ->
    fun ps  ->
      match (is_guard ())
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.Derived.fst"
                          (Prims.of_int (357)) (Prims.of_int (7))
                          (Prims.of_int (357)) (Prims.of_int (18))))))
      with
      | FStar_Tactics_Result.Success (a,ps') ->
          (match () with
           | () ->
               (if a then smt () else fail "")
                 (FStar_Tactics_Types.decr_depth
                    (FStar_Tactics_Types.set_proofstate_range ps'
                       (FStar_Range.prims_to_fstar_range
                          (Prims.mk_range "FStar.Tactics.Derived.fst"
                             (Prims.of_int (357)) (Prims.of_int (4))
                             (Prims.of_int (359)) (Prims.of_int (16)))))))
      | FStar_Tactics_Result.Failed (e,ps') ->
          FStar_Tactics_Result.Failed (e, ps')
  
let (guards_to_smt : unit -> (unit,unit) FStar_Tactics_Effect._dm4f_TAC_repr)
  =
  fun uu____9150  ->
    fun ps  ->
      match (repeat skip_guard)
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.Derived.fst"
                          (Prims.of_int (362)) (Prims.of_int (12))
                          (Prims.of_int (362)) (Prims.of_int (29))))))
      with
      | FStar_Tactics_Result.Success (a,ps') ->
          (match () with
           | () ->
               FStar_Tactics_Result.Success
                 ((),
                   (FStar_Tactics_Types.decr_depth
                      (FStar_Tactics_Types.set_proofstate_range ps'
                         (FStar_Range.prims_to_fstar_range
                            (Prims.mk_range "FStar.Tactics.Derived.fst"
                               (Prims.of_int (363)) (Prims.of_int (4))
                               (Prims.of_int (363)) (Prims.of_int (6))))))))
      | FStar_Tactics_Result.Failed (e,ps') ->
          FStar_Tactics_Result.Failed (e, ps')
  
let (simpl : unit -> (unit,unit) FStar_Tactics_Effect._dm4f_TAC_repr) =
  fun uu____9229  ->
    FStar_Tactics_Builtins.norm
      [FStar_Pervasives.simplify; FStar_Pervasives.primops]
  
let (whnf : unit -> (unit,unit) FStar_Tactics_Effect._dm4f_TAC_repr) =
  fun uu____9252  ->
    FStar_Tactics_Builtins.norm
      [FStar_Pervasives.weak;
      FStar_Pervasives.hnf;
      FStar_Pervasives.primops;
      FStar_Pervasives.delta]
  
let (compute : unit -> (unit,unit) FStar_Tactics_Effect._dm4f_TAC_repr) =
  fun uu____9275  ->
    FStar_Tactics_Builtins.norm
      [FStar_Pervasives.primops;
      FStar_Pervasives.iota;
      FStar_Pervasives.delta;
      FStar_Pervasives.zeta]
  
let (intros :
  unit ->
    (FStar_Reflection_Types.binder Prims.list,unit)
      FStar_Tactics_Effect._dm4f_TAC_repr)
  = fun uu____9300  -> repeat FStar_Tactics_Builtins.intro 
let (intros' : unit -> (unit,unit) FStar_Tactics_Effect._dm4f_TAC_repr) =
  fun uu____9324  ->
    fun ps  ->
      match (intros ())
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.Derived.fst"
                          (Prims.of_int (371)) (Prims.of_int (36))
                          (Prims.of_int (371)) (Prims.of_int (45))))))
      with
      | FStar_Tactics_Result.Success (a,ps') ->
          (match () with
           | () ->
               FStar_Tactics_Result.Success
                 ((),
                   (FStar_Tactics_Types.decr_depth
                      (FStar_Tactics_Types.set_proofstate_range ps'
                         (FStar_Range.prims_to_fstar_range
                            (Prims.mk_range "FStar.Tactics.Derived.fst"
                               (Prims.of_int (371)) (Prims.of_int (49))
                               (Prims.of_int (371)) (Prims.of_int (51))))))))
      | FStar_Tactics_Result.Failed (e,ps') ->
          FStar_Tactics_Result.Failed (e, ps')
  
let (destruct :
  FStar_Reflection_Types.term ->
    (unit,unit) FStar_Tactics_Effect._dm4f_TAC_repr)
  =
  fun tm  ->
    fun ps  ->
      match (FStar_Tactics_Builtins.t_destruct tm)
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.Derived.fst"
                          (Prims.of_int (372)) (Prims.of_int (37))
                          (Prims.of_int (372)) (Prims.of_int (50))))))
      with
      | FStar_Tactics_Result.Success (a,ps') ->
          (match () with
           | () ->
               FStar_Tactics_Result.Success
                 ((),
                   (FStar_Tactics_Types.decr_depth
                      (FStar_Tactics_Types.set_proofstate_range ps'
                         (FStar_Range.prims_to_fstar_range
                            (Prims.mk_range "FStar.Tactics.Derived.fst"
                               (Prims.of_int (372)) (Prims.of_int (54))
                               (Prims.of_int (372)) (Prims.of_int (56))))))))
      | FStar_Tactics_Result.Failed (e,ps') ->
          FStar_Tactics_Result.Failed (e, ps')
  
let (destruct_intros :
  FStar_Reflection_Types.term ->
    (unit,unit) FStar_Tactics_Effect._dm4f_TAC_repr)
  =
  fun tm  ->
    seq
      (fun uu____9508  ->
         fun ps  ->
           match (FStar_Tactics_Builtins.t_destruct tm)
                   (FStar_Tactics_Types.incr_depth
                      (FStar_Tactics_Types.set_proofstate_range ps
                         (FStar_Range.prims_to_fstar_range
                            (Prims.mk_range "FStar.Tactics.Derived.fst"
                               (Prims.of_int (373)) (Prims.of_int (59))
                               (Prims.of_int (373)) (Prims.of_int (72))))))
           with
           | FStar_Tactics_Result.Success (a,ps') ->
               (match () with
                | () ->
                    FStar_Tactics_Result.Success
                      ((),
                        (FStar_Tactics_Types.decr_depth
                           (FStar_Tactics_Types.set_proofstate_range ps'
                              (FStar_Range.prims_to_fstar_range
                                 (Prims.mk_range "FStar.Tactics.Derived.fst"
                                    (Prims.of_int (373)) (Prims.of_int (76))
                                    (Prims.of_int (373)) (Prims.of_int (78))))))))
           | FStar_Tactics_Result.Failed (e,ps') ->
               FStar_Tactics_Result.Failed (e, ps')) intros'
  
let __cut : 'Aa 'Ab . ('Aa -> 'Ab) -> 'Aa -> 'Ab = fun f  -> fun x  -> f x 
let (tcut :
  FStar_Reflection_Types.term ->
    (FStar_Reflection_Types.binder,unit) FStar_Tactics_Effect._dm4f_TAC_repr)
  =
  fun t  ->
    fun ps  ->
      match (cur_goal ())
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.Derived.fst"
                          (Prims.of_int (379)) (Prims.of_int (12))
                          (Prims.of_int (379)) (Prims.of_int (23))))))
      with
      | FStar_Tactics_Result.Success (a,ps') ->
          (match () with
           | () ->
               (match () with
                | () ->
                    (match (apply
                              (FStar_Reflection_Derived.mk_e_app
                                 (FStar_Reflection_Basic.pack_ln
                                    (FStar_Reflection_Data.Tv_FVar
                                       (FStar_Reflection_Basic.pack_fv
                                          ["FStar";
                                          "Tactics";
                                          "Derived";
                                          "__cut"]))) [t; a]))
                             (FStar_Tactics_Types.incr_depth
                                (FStar_Tactics_Types.set_proofstate_range
                                   (FStar_Tactics_Types.decr_depth
                                      (FStar_Tactics_Types.set_proofstate_range
                                         (FStar_Tactics_Types.incr_depth
                                            (FStar_Tactics_Types.set_proofstate_range
                                               (FStar_Tactics_Types.decr_depth
                                                  (FStar_Tactics_Types.set_proofstate_range
                                                     ps'
                                                     (FStar_Range.prims_to_fstar_range
                                                        (Prims.mk_range
                                                           "FStar.Tactics.Derived.fst"
                                                           (Prims.of_int (380))
                                                           (Prims.of_int (4))
                                                           (Prims.of_int (382))
                                                           (Prims.of_int (12))))))
                                               (FStar_Range.prims_to_fstar_range
                                                  (Prims.mk_range
                                                     "FStar.Tactics.Derived.fst"
                                                     (Prims.of_int (380))
                                                     (Prims.of_int (13))
                                                     (Prims.of_int (380))
                                                     (Prims.of_int (37))))))
                                         (FStar_Range.prims_to_fstar_range
                                            (Prims.mk_range
                                               "FStar.Tactics.Derived.fst"
                                               (Prims.of_int (381))
                                               (Prims.of_int (4))
                                               (Prims.of_int (382))
                                               (Prims.of_int (12))))))
                                   (FStar_Range.prims_to_fstar_range
                                      (Prims.mk_range
                                         "FStar.Tactics.Derived.fst"
                                         (Prims.of_int (381))
                                         (Prims.of_int (4))
                                         (Prims.of_int (381))
                                         (Prims.of_int (12))))))
                     with
                     | FStar_Tactics_Result.Success (a1,ps'1) ->
                         (match () with
                          | () ->
                              (FStar_Tactics_Builtins.intro ())
                                (FStar_Tactics_Types.decr_depth
                                   (FStar_Tactics_Types.set_proofstate_range
                                      ps'1
                                      (FStar_Range.prims_to_fstar_range
                                         (Prims.mk_range
                                            "FStar.Tactics.Derived.fst"
                                            (Prims.of_int (382))
                                            (Prims.of_int (4))
                                            (Prims.of_int (382))
                                            (Prims.of_int (12)))))))
                     | FStar_Tactics_Result.Failed (e,ps'1) ->
                         FStar_Tactics_Result.Failed (e, ps'1))))
      | FStar_Tactics_Result.Failed (e,ps') ->
          FStar_Tactics_Result.Failed (e, ps')
  
let (pose :
  FStar_Reflection_Types.term ->
    (FStar_Reflection_Types.binder,unit) FStar_Tactics_Effect._dm4f_TAC_repr)
  =
  fun t  ->
    fun ps  ->
      match (apply
               (FStar_Reflection_Basic.pack_ln
                  (FStar_Reflection_Data.Tv_FVar
                     (FStar_Reflection_Basic.pack_fv
                        ["FStar"; "Tactics"; "Derived"; "__cut"]))))
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.Derived.fst"
                          (Prims.of_int (385)) (Prims.of_int (4))
                          (Prims.of_int (385)) (Prims.of_int (18))))))
      with
      | FStar_Tactics_Result.Success (a,ps') ->
          (match () with
           | () ->
               (match (flip ())
                        (FStar_Tactics_Types.incr_depth
                           (FStar_Tactics_Types.set_proofstate_range
                              (FStar_Tactics_Types.decr_depth
                                 (FStar_Tactics_Types.set_proofstate_range
                                    ps'
                                    (FStar_Range.prims_to_fstar_range
                                       (Prims.mk_range
                                          "FStar.Tactics.Derived.fst"
                                          (Prims.of_int (386))
                                          (Prims.of_int (4))
                                          (Prims.of_int (388))
                                          (Prims.of_int (12))))))
                              (FStar_Range.prims_to_fstar_range
                                 (Prims.mk_range "FStar.Tactics.Derived.fst"
                                    (Prims.of_int (386)) (Prims.of_int (4))
                                    (Prims.of_int (386)) (Prims.of_int (11))))))
                with
                | FStar_Tactics_Result.Success (a1,ps'1) ->
                    (match () with
                     | () ->
                         (match (exact t)
                                  (FStar_Tactics_Types.incr_depth
                                     (FStar_Tactics_Types.set_proofstate_range
                                        (FStar_Tactics_Types.decr_depth
                                           (FStar_Tactics_Types.set_proofstate_range
                                              ps'1
                                              (FStar_Range.prims_to_fstar_range
                                                 (Prims.mk_range
                                                    "FStar.Tactics.Derived.fst"
                                                    (Prims.of_int (387))
                                                    (Prims.of_int (4))
                                                    (Prims.of_int (388))
                                                    (Prims.of_int (12))))))
                                        (FStar_Range.prims_to_fstar_range
                                           (Prims.mk_range
                                              "FStar.Tactics.Derived.fst"
                                              (Prims.of_int (387))
                                              (Prims.of_int (4))
                                              (Prims.of_int (387))
                                              (Prims.of_int (11))))))
                          with
                          | FStar_Tactics_Result.Success (a2,ps'2) ->
                              (match () with
                               | () ->
                                   (FStar_Tactics_Builtins.intro ())
                                     (FStar_Tactics_Types.decr_depth
                                        (FStar_Tactics_Types.set_proofstate_range
                                           ps'2
                                           (FStar_Range.prims_to_fstar_range
                                              (Prims.mk_range
                                                 "FStar.Tactics.Derived.fst"
                                                 (Prims.of_int (388))
                                                 (Prims.of_int (4))
                                                 (Prims.of_int (388))
                                                 (Prims.of_int (12)))))))
                          | FStar_Tactics_Result.Failed (e,ps'2) ->
                              FStar_Tactics_Result.Failed (e, ps'2)))
                | FStar_Tactics_Result.Failed (e,ps'1) ->
                    FStar_Tactics_Result.Failed (e, ps'1)))
      | FStar_Tactics_Result.Failed (e,ps') ->
          FStar_Tactics_Result.Failed (e, ps')
  
let (intro_as :
  Prims.string ->
    (FStar_Reflection_Types.binder,unit) FStar_Tactics_Effect._dm4f_TAC_repr)
  =
  fun s  ->
    fun ps  ->
      match (FStar_Tactics_Builtins.intro ())
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.Derived.fst"
                          (Prims.of_int (391)) (Prims.of_int (12))
                          (Prims.of_int (391)) (Prims.of_int (20))))))
      with
      | FStar_Tactics_Result.Success (a,ps') ->
          (match () with
           | () ->
               (match (FStar_Tactics_Builtins.rename_to a s)
                        (FStar_Tactics_Types.incr_depth
                           (FStar_Tactics_Types.set_proofstate_range
                              (FStar_Tactics_Types.decr_depth
                                 (FStar_Tactics_Types.set_proofstate_range
                                    ps'
                                    (FStar_Range.prims_to_fstar_range
                                       (Prims.mk_range
                                          "FStar.Tactics.Derived.fst"
                                          (Prims.of_int (392))
                                          (Prims.of_int (4))
                                          (Prims.of_int (393))
                                          (Prims.of_int (5))))))
                              (FStar_Range.prims_to_fstar_range
                                 (Prims.mk_range "FStar.Tactics.Derived.fst"
                                    (Prims.of_int (392)) (Prims.of_int (4))
                                    (Prims.of_int (392)) (Prims.of_int (17))))))
                with
                | FStar_Tactics_Result.Success (a1,ps'1) ->
                    (match () with
                     | () ->
                         FStar_Tactics_Result.Success
                           (a,
                             (FStar_Tactics_Types.decr_depth
                                (FStar_Tactics_Types.set_proofstate_range
                                   ps'1
                                   (FStar_Range.prims_to_fstar_range
                                      (Prims.mk_range
                                         "FStar.Tactics.Derived.fst"
                                         (Prims.of_int (391))
                                         (Prims.of_int (8))
                                         (Prims.of_int (391))
                                         (Prims.of_int (9))))))))
                | FStar_Tactics_Result.Failed (e,ps'1) ->
                    FStar_Tactics_Result.Failed (e, ps'1)))
      | FStar_Tactics_Result.Failed (e,ps') ->
          FStar_Tactics_Result.Failed (e, ps')
  
let (pose_as :
  Prims.string ->
    FStar_Reflection_Types.term ->
      (FStar_Reflection_Types.binder,unit)
        FStar_Tactics_Effect._dm4f_TAC_repr)
  =
  fun s  ->
    fun t  ->
      fun ps  ->
        match (pose t)
                (FStar_Tactics_Types.incr_depth
                   (FStar_Tactics_Types.set_proofstate_range ps
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range "FStar.Tactics.Derived.fst"
                            (Prims.of_int (396)) (Prims.of_int (12))
                            (Prims.of_int (396)) (Prims.of_int (18))))))
        with
        | FStar_Tactics_Result.Success (a,ps') ->
            (match () with
             | () ->
                 (match (FStar_Tactics_Builtins.rename_to a s)
                          (FStar_Tactics_Types.incr_depth
                             (FStar_Tactics_Types.set_proofstate_range
                                (FStar_Tactics_Types.decr_depth
                                   (FStar_Tactics_Types.set_proofstate_range
                                      ps'
                                      (FStar_Range.prims_to_fstar_range
                                         (Prims.mk_range
                                            "FStar.Tactics.Derived.fst"
                                            (Prims.of_int (397))
                                            (Prims.of_int (4))
                                            (Prims.of_int (398))
                                            (Prims.of_int (5))))))
                                (FStar_Range.prims_to_fstar_range
                                   (Prims.mk_range
                                      "FStar.Tactics.Derived.fst"
                                      (Prims.of_int (397)) (Prims.of_int (4))
                                      (Prims.of_int (397))
                                      (Prims.of_int (17))))))
                  with
                  | FStar_Tactics_Result.Success (a1,ps'1) ->
                      (match () with
                       | () ->
                           FStar_Tactics_Result.Success
                             (a,
                               (FStar_Tactics_Types.decr_depth
                                  (FStar_Tactics_Types.set_proofstate_range
                                     ps'1
                                     (FStar_Range.prims_to_fstar_range
                                        (Prims.mk_range
                                           "FStar.Tactics.Derived.fst"
                                           (Prims.of_int (396))
                                           (Prims.of_int (8))
                                           (Prims.of_int (396))
                                           (Prims.of_int (9))))))))
                  | FStar_Tactics_Result.Failed (e,ps'1) ->
                      FStar_Tactics_Result.Failed (e, ps'1)))
        | FStar_Tactics_Result.Failed (e,ps') ->
            FStar_Tactics_Result.Failed (e, ps')
  
let for_each_binder :
  'a .
    (FStar_Reflection_Types.binder ->
       ('a,unit) FStar_Tactics_Effect._dm4f_TAC_repr)
      -> ('a Prims.list,unit) FStar_Tactics_Effect._dm4f_TAC_repr
  =
  fun f  ->
    fun ps  ->
      match (cur_binders ())
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.Derived.fst"
                          (Prims.of_int (401)) (Prims.of_int (10))
                          (Prims.of_int (401)) (Prims.of_int (26))))))
      with
      | FStar_Tactics_Result.Success (a,ps') ->
          (match () with
           | () ->
               (FStar_Tactics_Util.map f a)
                 (FStar_Tactics_Types.decr_depth
                    (FStar_Tactics_Types.set_proofstate_range ps'
                       (FStar_Range.prims_to_fstar_range
                          (Prims.mk_range "FStar.Tactics.Derived.fst"
                             (Prims.of_int (401)) (Prims.of_int (4))
                             (Prims.of_int (401)) (Prims.of_int (26)))))))
      | FStar_Tactics_Result.Failed (e,ps') ->
          FStar_Tactics_Result.Failed (e, ps')
  
let rec (revert_all :
  FStar_Reflection_Types.binders ->
    (unit,unit) FStar_Tactics_Effect._dm4f_TAC_repr)
  =
  fun bs  ->
    match bs with
    | [] -> (fun s  -> FStar_Tactics_Result.Success ((), s))
    | uu____10229::tl1 ->
        (fun ps  ->
           match (FStar_Tactics_Builtins.revert ())
                   (FStar_Tactics_Types.incr_depth
                      (FStar_Tactics_Types.set_proofstate_range ps
                         (FStar_Range.prims_to_fstar_range
                            (Prims.mk_range "FStar.Tactics.Derived.fst"
                               (Prims.of_int (406)) (Prims.of_int (15))
                               (Prims.of_int (406)) (Prims.of_int (24))))))
           with
           | FStar_Tactics_Result.Success (a,ps') ->
               (match () with
                | () ->
                    (revert_all tl1)
                      (FStar_Tactics_Types.decr_depth
                         (FStar_Tactics_Types.set_proofstate_range ps'
                            (FStar_Range.prims_to_fstar_range
                               (Prims.mk_range "FStar.Tactics.Derived.fst"
                                  (Prims.of_int (407)) (Prims.of_int (15))
                                  (Prims.of_int (407)) (Prims.of_int (28)))))))
           | FStar_Tactics_Result.Failed (e,ps') ->
               FStar_Tactics_Result.Failed (e, ps'))
  
let (bv_to_term :
  FStar_Reflection_Types.bv ->
    (FStar_Reflection_Types.term,unit) FStar_Tactics_Effect._dm4f_TAC_repr)
  = fun bv  -> FStar_Tactics_Builtins.pack (FStar_Reflection_Data.Tv_Var bv) 
let (binder_to_term :
  FStar_Reflection_Types.binder ->
    (FStar_Reflection_Types.term,unit) FStar_Tactics_Effect._dm4f_TAC_repr)
  =
  fun b  ->
    fun ps  ->
      match () with
      | () ->
          ((match FStar_Reflection_Basic.inspect_binder b with
            | (bv,uu____10352) -> bv_to_term bv))
            (FStar_Tactics_Types.decr_depth
               (FStar_Tactics_Types.set_proofstate_range
                  (FStar_Tactics_Types.incr_depth
                     (FStar_Tactics_Types.set_proofstate_range ps
                        (FStar_Range.prims_to_fstar_range
                           (Prims.mk_range "FStar.Tactics.Derived.fst"
                              (Prims.of_int (411)) (Prims.of_int (57))
                              (Prims.of_int (411)) (Prims.of_int (73))))))
                  (FStar_Range.prims_to_fstar_range
                     (Prims.mk_range "FStar.Tactics.Derived.fst"
                        (Prims.of_int (411)) (Prims.of_int (45))
                        (Prims.of_int (411)) (Prims.of_int (90))))))
  
let rec (__assumption_aux :
  FStar_Reflection_Types.binders ->
    (unit,unit) FStar_Tactics_Effect._dm4f_TAC_repr)
  =
  fun bs  ->
    match bs with
    | [] -> fail "no assumption matches goal"
    | b::bs1 ->
        (fun ps  ->
           match (binder_to_term b)
                   (FStar_Tactics_Types.incr_depth
                      (FStar_Tactics_Types.set_proofstate_range ps
                         (FStar_Range.prims_to_fstar_range
                            (Prims.mk_range "FStar.Tactics.Derived.fst"
                               (Prims.of_int (420)) (Prims.of_int (16))
                               (Prims.of_int (420)) (Prims.of_int (32))))))
           with
           | FStar_Tactics_Result.Success (a,ps') ->
               (match () with
                | () ->
                    (try_with
                       (fun uu___320_10461  -> match () with | () -> exact a)
                       (fun uu___319_10463  ->
                          try_with
                            (fun uu___324_10475  ->
                               match () with
                               | () ->
                                   (fun ps1  ->
                                      match (apply
                                               (FStar_Reflection_Basic.pack_ln
                                                  (FStar_Reflection_Data.Tv_FVar
                                                     (FStar_Reflection_Basic.pack_fv
                                                        ["FStar";
                                                        "Squash";
                                                        "return_squash"]))))
                                              (FStar_Tactics_Types.incr_depth
                                                 (FStar_Tactics_Types.set_proofstate_range
                                                    ps1
                                                    (FStar_Range.prims_to_fstar_range
                                                       (Prims.mk_range
                                                          "FStar.Tactics.Derived.fst"
                                                          (Prims.of_int (422))
                                                          (Prims.of_int (13))
                                                          (Prims.of_int (422))
                                                          (Prims.of_int (48))))))
                                      with
                                      | FStar_Tactics_Result.Success
                                          (a1,ps'1) ->
                                          (match () with
                                           | () ->
                                               (exact a)
                                                 (FStar_Tactics_Types.decr_depth
                                                    (FStar_Tactics_Types.set_proofstate_range
                                                       ps'1
                                                       (FStar_Range.prims_to_fstar_range
                                                          (Prims.mk_range
                                                             "FStar.Tactics.Derived.fst"
                                                             (Prims.of_int (423))
                                                             (Prims.of_int (13))
                                                             (Prims.of_int (423))
                                                             (Prims.of_int (20)))))))
                                      | FStar_Tactics_Result.Failed (e,ps'1)
                                          ->
                                          FStar_Tactics_Result.Failed
                                            (e, ps'1)))
                            (fun uu___323_10529  -> __assumption_aux bs1)))
                      (FStar_Tactics_Types.decr_depth
                         (FStar_Tactics_Types.set_proofstate_range ps'
                            (FStar_Range.prims_to_fstar_range
                               (Prims.mk_range "FStar.Tactics.Derived.fst"
                                  (Prims.of_int (421)) (Prims.of_int (8))
                                  (Prims.of_int (424)) (Prims.of_int (27)))))))
           | FStar_Tactics_Result.Failed (e,ps') ->
               FStar_Tactics_Result.Failed (e, ps'))
  
let (assumption : unit -> (unit,unit) FStar_Tactics_Effect._dm4f_TAC_repr) =
  fun uu____10555  ->
    fun ps  ->
      match (cur_binders ())
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.Derived.fst"
                          (Prims.of_int (427)) (Prims.of_int (21))
                          (Prims.of_int (427)) (Prims.of_int (37))))))
      with
      | FStar_Tactics_Result.Success (a,ps') ->
          (match () with
           | () ->
               (__assumption_aux a)
                 (FStar_Tactics_Types.decr_depth
                    (FStar_Tactics_Types.set_proofstate_range ps'
                       (FStar_Range.prims_to_fstar_range
                          (Prims.mk_range "FStar.Tactics.Derived.fst"
                             (Prims.of_int (427)) (Prims.of_int (4))
                             (Prims.of_int (427)) (Prims.of_int (37)))))))
      | FStar_Tactics_Result.Failed (e,ps') ->
          FStar_Tactics_Result.Failed (e, ps')
  
let (destruct_equality_implication :
  FStar_Reflection_Types.term ->
    ((FStar_Reflection_Formula.formula * FStar_Reflection_Types.term)
       FStar_Pervasives_Native.option,unit)
      FStar_Tactics_Effect._dm4f_TAC_repr)
  =
  fun t  ->
    fun ps  ->
      match (FStar_Reflection_Formula.term_as_formula t)
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.Derived.fst"
                          (Prims.of_int (430)) (Prims.of_int (10))
                          (Prims.of_int (430)) (Prims.of_int (27))))))
      with
      | FStar_Tactics_Result.Success (a,ps') ->
          (match () with
           | () ->
               ((match a with
                 | FStar_Reflection_Formula.Implies (lhs,rhs) ->
                     (fun ps1  ->
                        match (FStar_Reflection_Formula.term_as_formula' lhs)
                                (FStar_Tactics_Types.incr_depth
                                   (FStar_Tactics_Types.set_proofstate_range
                                      ps1
                                      (FStar_Range.prims_to_fstar_range
                                         (Prims.mk_range
                                            "FStar.Tactics.Derived.fst"
                                            (Prims.of_int (432))
                                            (Prims.of_int (18))
                                            (Prims.of_int (432))
                                            (Prims.of_int (38))))))
                        with
                        | FStar_Tactics_Result.Success (a1,ps'1) ->
                            (match () with
                             | () ->
                                 FStar_Tactics_Result.Success
                                   (((match a1 with
                                      | FStar_Reflection_Formula.Comp
                                          (FStar_Reflection_Formula.Eq
                                           uu____10825,uu____10826,uu____10827)
                                          ->
                                          FStar_Pervasives_Native.Some
                                            (a1, rhs)
                                      | uu____10834 ->
                                          FStar_Pervasives_Native.None)),
                                     (FStar_Tactics_Types.decr_depth
                                        (FStar_Tactics_Types.set_proofstate_range
                                           ps'1
                                           (FStar_Range.prims_to_fstar_range
                                              (Prims.mk_range
                                                 "FStar.Tactics.Derived.fst"
                                                 (Prims.of_int (433))
                                                 (Prims.of_int (14))
                                                 (Prims.of_int (435))
                                                 (Prims.of_int (19))))))))
                        | FStar_Tactics_Result.Failed (e,ps'1) ->
                            FStar_Tactics_Result.Failed (e, ps'1))
                 | uu____10847 ->
                     (fun s  ->
                        FStar_Tactics_Result.Success
                          (FStar_Pervasives_Native.None, s))))
                 (FStar_Tactics_Types.decr_depth
                    (FStar_Tactics_Types.set_proofstate_range ps'
                       (FStar_Range.prims_to_fstar_range
                          (Prims.mk_range "FStar.Tactics.Derived.fst"
                             (Prims.of_int (430)) (Prims.of_int (4))
                             (Prims.of_int (437)) (Prims.of_int (15)))))))
      | FStar_Tactics_Result.Failed (e,ps') ->
          FStar_Tactics_Result.Failed (e, ps')
  

let (rewrite' :
  FStar_Reflection_Types.binder ->
    (unit,unit) FStar_Tactics_Effect._dm4f_TAC_repr)
  =
  fun b  ->
    op_Less_Bar_Greater
      (op_Less_Bar_Greater
         (fun uu____10923  -> FStar_Tactics_Builtins.rewrite b)
         (fun uu____10927  ->
            fun ps  ->
              match (FStar_Tactics_Builtins.binder_retype b)
                      (FStar_Tactics_Types.incr_depth
                         (FStar_Tactics_Types.set_proofstate_range ps
                            (FStar_Range.prims_to_fstar_range
                               (Prims.mk_range "FStar.Tactics.Derived.fst"
                                  (Prims.of_int (446)) (Prims.of_int (20))
                                  (Prims.of_int (446)) (Prims.of_int (35))))))
              with
              | FStar_Tactics_Result.Success (a,ps') ->
                  (match () with
                   | () ->
                       (match (FStar_Tactics_Builtins.apply_lemma
                                 (FStar_Reflection_Basic.pack_ln
                                    (FStar_Reflection_Data.Tv_FVar
                                       (FStar_Reflection_Basic.pack_fv
                                          ["FStar";
                                          "Tactics";
                                          "Derived";
                                          "__eq_sym"]))))
                                (FStar_Tactics_Types.incr_depth
                                   (FStar_Tactics_Types.set_proofstate_range
                                      (FStar_Tactics_Types.decr_depth
                                         (FStar_Tactics_Types.set_proofstate_range
                                            ps'
                                            (FStar_Range.prims_to_fstar_range
                                               (Prims.mk_range
                                                  "FStar.Tactics.Derived.fst"
                                                  (Prims.of_int (447))
                                                  (Prims.of_int (20))
                                                  (Prims.of_int (448))
                                                  (Prims.of_int (29))))))
                                      (FStar_Range.prims_to_fstar_range
                                         (Prims.mk_range
                                            "FStar.Tactics.Derived.fst"
                                            (Prims.of_int (447))
                                            (Prims.of_int (20))
                                            (Prims.of_int (447))
                                            (Prims.of_int (43))))))
                        with
                        | FStar_Tactics_Result.Success (a1,ps'1) ->
                            (match () with
                             | () ->
                                 (FStar_Tactics_Builtins.rewrite b)
                                   (FStar_Tactics_Types.decr_depth
                                      (FStar_Tactics_Types.set_proofstate_range
                                         ps'1
                                         (FStar_Range.prims_to_fstar_range
                                            (Prims.mk_range
                                               "FStar.Tactics.Derived.fst"
                                               (Prims.of_int (448))
                                               (Prims.of_int (20))
                                               (Prims.of_int (448))
                                               (Prims.of_int (29)))))))
                        | FStar_Tactics_Result.Failed (e,ps'1) ->
                            FStar_Tactics_Result.Failed (e, ps'1)))
              | FStar_Tactics_Result.Failed (e,ps') ->
                  FStar_Tactics_Result.Failed (e, ps')))
      (fun uu____11005  -> fail "rewrite' failed") ()
  
let rec (try_rewrite_equality :
  FStar_Reflection_Types.term ->
    FStar_Reflection_Types.binders ->
      (unit,unit) FStar_Tactics_Effect._dm4f_TAC_repr)
  =
  fun x  ->
    fun bs  ->
      match bs with
      | [] -> (fun s  -> FStar_Tactics_Result.Success ((), s))
      | x_t::bs1 ->
          (fun ps  ->
             match (FStar_Reflection_Formula.term_as_formula
                      (FStar_Reflection_Derived.type_of_binder x_t))
                     (FStar_Tactics_Types.incr_depth
                        (FStar_Tactics_Types.set_proofstate_range ps
                           (FStar_Range.prims_to_fstar_range
                              (Prims.mk_range "FStar.Tactics.Derived.fst"
                                 (Prims.of_int (456)) (Prims.of_int (20))
                                 (Prims.of_int (456)) (Prims.of_int (56))))))
             with
             | FStar_Tactics_Result.Success (a,ps') ->
                 (match () with
                  | () ->
                      ((match a with
                        | FStar_Reflection_Formula.Comp
                            (FStar_Reflection_Formula.Eq
                             uu____11125,y,uu____11127)
                            ->
                            if FStar_Reflection_Basic.term_eq x y
                            then FStar_Tactics_Builtins.rewrite x_t
                            else try_rewrite_equality x bs1
                        | uu____11133 -> try_rewrite_equality x bs1))
                        (FStar_Tactics_Types.decr_depth
                           (FStar_Tactics_Types.set_proofstate_range ps'
                              (FStar_Range.prims_to_fstar_range
                                 (Prims.mk_range "FStar.Tactics.Derived.fst"
                                    (Prims.of_int (456)) (Prims.of_int (14))
                                    (Prims.of_int (462)) (Prims.of_int (37)))))))
             | FStar_Tactics_Result.Failed (e,ps') ->
                 FStar_Tactics_Result.Failed (e, ps'))
  
let rec (rewrite_all_context_equalities :
  FStar_Reflection_Types.binders ->
    (unit,unit) FStar_Tactics_Effect._dm4f_TAC_repr)
  =
  fun bs  ->
    match bs with
    | [] -> (fun s  -> FStar_Tactics_Result.Success ((), s))
    | x_t::bs1 ->
        (fun ps  ->
           match (try_with
                    (fun uu___374_11227  ->
                       match () with
                       | () -> FStar_Tactics_Builtins.rewrite x_t)
                    (fun uu___373_11229  ->
                       fun s  -> FStar_Tactics_Result.Success ((), s)))
                   (FStar_Tactics_Types.incr_depth
                      (FStar_Tactics_Types.set_proofstate_range ps
                         (FStar_Range.prims_to_fstar_range
                            (Prims.mk_range "FStar.Tactics.Derived.fst"
                               (Prims.of_int (469)) (Prims.of_int (8))
                               (Prims.of_int (469)) (Prims.of_int (40))))))
           with
           | FStar_Tactics_Result.Success (a,ps') ->
               (match () with
                | () ->
                    (rewrite_all_context_equalities bs1)
                      (FStar_Tactics_Types.decr_depth
                         (FStar_Tactics_Types.set_proofstate_range ps'
                            (FStar_Range.prims_to_fstar_range
                               (Prims.mk_range "FStar.Tactics.Derived.fst"
                                  (Prims.of_int (470)) (Prims.of_int (8))
                                  (Prims.of_int (470)) (Prims.of_int (41)))))))
           | FStar_Tactics_Result.Failed (e,ps') ->
               FStar_Tactics_Result.Failed (e, ps'))
  
let (rewrite_eqs_from_context :
  unit -> (unit,unit) FStar_Tactics_Effect._dm4f_TAC_repr) =
  fun uu____11266  ->
    fun ps  ->
      match (cur_binders ())
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.Derived.fst"
                          (Prims.of_int (474)) (Prims.of_int (35))
                          (Prims.of_int (474)) (Prims.of_int (51))))))
      with
      | FStar_Tactics_Result.Success (a,ps') ->
          (match () with
           | () ->
               (rewrite_all_context_equalities a)
                 (FStar_Tactics_Types.decr_depth
                    (FStar_Tactics_Types.set_proofstate_range ps'
                       (FStar_Range.prims_to_fstar_range
                          (Prims.mk_range "FStar.Tactics.Derived.fst"
                             (Prims.of_int (474)) (Prims.of_int (4))
                             (Prims.of_int (474)) (Prims.of_int (51)))))))
      | FStar_Tactics_Result.Failed (e,ps') ->
          FStar_Tactics_Result.Failed (e, ps')
  
let (rewrite_equality :
  FStar_Reflection_Types.term ->
    (unit,unit) FStar_Tactics_Effect._dm4f_TAC_repr)
  =
  fun t  ->
    fun ps  ->
      match (cur_binders ())
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.Derived.fst"
                          (Prims.of_int (477)) (Prims.of_int (27))
                          (Prims.of_int (477)) (Prims.of_int (43))))))
      with
      | FStar_Tactics_Result.Success (a,ps') ->
          (match () with
           | () ->
               (try_rewrite_equality t a)
                 (FStar_Tactics_Types.decr_depth
                    (FStar_Tactics_Types.set_proofstate_range ps'
                       (FStar_Range.prims_to_fstar_range
                          (Prims.mk_range "FStar.Tactics.Derived.fst"
                             (Prims.of_int (477)) (Prims.of_int (4))
                             (Prims.of_int (477)) (Prims.of_int (43)))))))
      | FStar_Tactics_Result.Failed (e,ps') ->
          FStar_Tactics_Result.Failed (e, ps')
  
let (unfold_def :
  FStar_Reflection_Types.term ->
    (unit,unit) FStar_Tactics_Effect._dm4f_TAC_repr)
  =
  fun t  ->
    fun ps  ->
      match (FStar_Tactics_Builtins.inspect t)
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.Derived.fst"
                          (Prims.of_int (480)) (Prims.of_int (10))
                          (Prims.of_int (480)) (Prims.of_int (19))))))
      with
      | FStar_Tactics_Result.Success (a,ps') ->
          (match () with
           | () ->
               ((match a with
                 | FStar_Reflection_Data.Tv_FVar fv ->
                     (fun ps1  ->
                        match () with
                        | () ->
                            (FStar_Tactics_Builtins.norm
                               [FStar_Pervasives.delta_fully
                                  [FStar_String.concat "."
                                     (FStar_Reflection_Basic.inspect_fv fv)]])
                              (FStar_Tactics_Types.decr_depth
                                 (FStar_Tactics_Types.set_proofstate_range
                                    (FStar_Tactics_Types.incr_depth
                                       (FStar_Tactics_Types.set_proofstate_range
                                          ps1
                                          (FStar_Range.prims_to_fstar_range
                                             (Prims.mk_range
                                                "FStar.Tactics.Derived.fst"
                                                (Prims.of_int (482))
                                                (Prims.of_int (16))
                                                (Prims.of_int (482))
                                                (Prims.of_int (49))))))
                                    (FStar_Range.prims_to_fstar_range
                                       (Prims.mk_range
                                          "FStar.Tactics.Derived.fst"
                                          (Prims.of_int (483))
                                          (Prims.of_int (8))
                                          (Prims.of_int (483))
                                          (Prims.of_int (30)))))))
                 | uu____11494 -> fail "unfold_def: term is not a fv"))
                 (FStar_Tactics_Types.decr_depth
                    (FStar_Tactics_Types.set_proofstate_range ps'
                       (FStar_Range.prims_to_fstar_range
                          (Prims.mk_range "FStar.Tactics.Derived.fst"
                             (Prims.of_int (480)) (Prims.of_int (4))
                             (Prims.of_int (484)) (Prims.of_int (46)))))))
      | FStar_Tactics_Result.Failed (e,ps') ->
          FStar_Tactics_Result.Failed (e, ps')
  
let (l_to_r :
  FStar_Reflection_Types.term Prims.list ->
    (unit,unit) FStar_Tactics_Effect._dm4f_TAC_repr)
  =
  fun lems  ->
    fun ps  ->
      match () with
      | () ->
          (pointwise
             (fun uu____11640  ->
                fun ps1  ->
                  match (FStar_Tactics_Util.fold_left
                           (fun k  ->
                              fun l  ->
                                fun s  ->
                                  FStar_Tactics_Result.Success
                                    ((fun uu____11821  ->
                                        or_else
                                          (fun uu____11826  ->
                                             FStar_Tactics_Builtins.apply_lemma
                                               l) k), s))
                           FStar_Tactics_Builtins.trefl lems)
                          (FStar_Tactics_Types.incr_depth
                             (FStar_Tactics_Types.set_proofstate_range ps1
                                (FStar_Range.prims_to_fstar_range
                                   (Prims.mk_range
                                      "FStar.Tactics.Derived.fst"
                                      (Prims.of_int (490)) (Prims.of_int (8))
                                      (Prims.of_int (493))
                                      (Prims.of_int (31))))))
                  with
                  | FStar_Tactics_Result.Success (a,ps') ->
                      (match () with
                       | () ->
                           (a ())
                             (FStar_Tactics_Types.decr_depth
                                (FStar_Tactics_Types.set_proofstate_range ps'
                                   (FStar_Range.prims_to_fstar_range
                                      (Prims.mk_range
                                         "FStar.Tactics.Derived.fst"
                                         (Prims.of_int (490))
                                         (Prims.of_int (8))
                                         (Prims.of_int (493))
                                         (Prims.of_int (31)))))))
                  | FStar_Tactics_Result.Failed (e,ps') ->
                      FStar_Tactics_Result.Failed (e, ps')))
            (FStar_Tactics_Types.decr_depth
               (FStar_Tactics_Types.set_proofstate_range
                  (FStar_Tactics_Types.incr_depth
                     (FStar_Tactics_Types.set_proofstate_range ps
                        (FStar_Range.prims_to_fstar_range
                           (Prims.mk_range "FStar.Tactics.Derived.fst"
                              (Prims.of_int (490)) (Prims.of_int (8))
                              (Prims.of_int (493)) (Prims.of_int (31))))))
                  (FStar_Range.prims_to_fstar_range
                     (Prims.mk_range "FStar.Tactics.Derived.fst"
                        (Prims.of_int (494)) (Prims.of_int (4))
                        (Prims.of_int (494)) (Prims.of_int (28))))))
  
let (mk_squash : FStar_Reflection_Types.term -> FStar_Reflection_Types.term)
  =
  fun t  ->
    let sq =
      FStar_Reflection_Basic.pack_ln
        (FStar_Reflection_Data.Tv_FVar
           (FStar_Reflection_Basic.pack_fv FStar_Reflection_Const.squash_qn))
       in
    FStar_Reflection_Derived.mk_e_app sq [t]
  
let (mk_sq_eq :
  FStar_Reflection_Types.term ->
    FStar_Reflection_Types.term -> FStar_Reflection_Types.term)
  =
  fun t1  ->
    fun t2  ->
      let eq1 =
        FStar_Reflection_Basic.pack_ln
          (FStar_Reflection_Data.Tv_FVar
             (FStar_Reflection_Basic.pack_fv FStar_Reflection_Const.eq2_qn))
         in
      mk_squash (FStar_Reflection_Derived.mk_e_app eq1 [t1; t2])
  
let (grewrite :
  FStar_Reflection_Types.term ->
    FStar_Reflection_Types.term ->
      (unit,unit) FStar_Tactics_Effect._dm4f_TAC_repr)
  =
  fun t1  ->
    fun t2  ->
      fun ps  ->
        match (tcut (mk_sq_eq t1 t2))
                (FStar_Tactics_Types.incr_depth
                   (FStar_Tactics_Types.set_proofstate_range ps
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range "FStar.Tactics.Derived.fst"
                            (Prims.of_int (505)) (Prims.of_int (12))
                            (Prims.of_int (505)) (Prims.of_int (33))))))
        with
        | FStar_Tactics_Result.Success (a,ps') ->
            (match () with
             | () ->
                 (match () with
                  | () ->
                      (pointwise
                         (fun uu____12018  ->
                            try_with
                              (fun uu___405_12026  ->
                                 match () with
                                 | () ->
                                     exact
                                       (FStar_Reflection_Basic.pack_ln
                                          (FStar_Reflection_Data.Tv_Var
                                             (FStar_Reflection_Derived.bv_of_binder
                                                a))))
                              (fun uu___404_12028  ->
                                 FStar_Tactics_Builtins.trefl ())))
                        (FStar_Tactics_Types.decr_depth
                           (FStar_Tactics_Types.set_proofstate_range
                              (FStar_Tactics_Types.incr_depth
                                 (FStar_Tactics_Types.set_proofstate_range
                                    (FStar_Tactics_Types.decr_depth
                                       (FStar_Tactics_Types.set_proofstate_range
                                          ps'
                                          (FStar_Range.prims_to_fstar_range
                                             (Prims.mk_range
                                                "FStar.Tactics.Derived.fst"
                                                (Prims.of_int (506))
                                                (Prims.of_int (4))
                                                (Prims.of_int (507))
                                                (Prims.of_int (58))))))
                                    (FStar_Range.prims_to_fstar_range
                                       (Prims.mk_range
                                          "FStar.Tactics.Derived.fst"
                                          (Prims.of_int (506))
                                          (Prims.of_int (12))
                                          (Prims.of_int (506))
                                          (Prims.of_int (45))))))
                              (FStar_Range.prims_to_fstar_range
                                 (Prims.mk_range "FStar.Tactics.Derived.fst"
                                    (Prims.of_int (507)) (Prims.of_int (4))
                                    (Prims.of_int (507)) (Prims.of_int (58))))))))
        | FStar_Tactics_Result.Failed (e,ps') ->
            FStar_Tactics_Result.Failed (e, ps')
  
let rec (iseq :
  (unit -> (unit,unit) FStar_Tactics_Effect._dm4f_TAC_repr) Prims.list ->
    (unit,unit) FStar_Tactics_Effect._dm4f_TAC_repr)
  =
  fun ts  ->
    match ts with
    | t::ts1 ->
        (fun ps  ->
           match (divide Prims.int_one t (fun uu____12232  -> iseq ts1))
                   (FStar_Tactics_Types.incr_depth
                      (FStar_Tactics_Types.set_proofstate_range ps
                         (FStar_Range.prims_to_fstar_range
                            (Prims.mk_range "FStar.Tactics.Derived.fst"
                               (Prims.of_int (511)) (Prims.of_int (23))
                               (Prims.of_int (511)) (Prims.of_int (53))))))
           with
           | FStar_Tactics_Result.Success (a,ps') ->
               (match () with
                | () ->
                    FStar_Tactics_Result.Success
                      ((),
                        (FStar_Tactics_Types.decr_depth
                           (FStar_Tactics_Types.set_proofstate_range ps'
                              (FStar_Range.prims_to_fstar_range
                                 (Prims.mk_range "FStar.Tactics.Derived.fst"
                                    (Prims.of_int (511)) (Prims.of_int (57))
                                    (Prims.of_int (511)) (Prims.of_int (59))))))))
           | FStar_Tactics_Result.Failed (e,ps') ->
               FStar_Tactics_Result.Failed (e, ps'))
    | [] -> (fun s  -> FStar_Tactics_Result.Success ((), s))
  


let rec (apply_squash_or_lem :
  Prims.nat ->
    FStar_Reflection_Types.term ->
      (unit,unit) FStar_Tactics_Effect._dm4f_TAC_repr)
  =
  fun d  ->
    fun t  ->
      try_with (fun uu___433_12467  -> match () with | () -> apply t)
        (fun uu___432_12469  ->
           try_with
             (fun uu___437_12580  ->
                match () with
                | () ->
                    (fun ps  ->
                       match (apply
                                (FStar_Reflection_Basic.pack_ln
                                   (FStar_Reflection_Data.Tv_FVar
                                      (FStar_Reflection_Basic.pack_fv
                                         ["FStar"; "Squash"; "return_squash"]))))
                               (FStar_Tactics_Types.incr_depth
                                  (FStar_Tactics_Types.set_proofstate_range
                                     ps
                                     (FStar_Range.prims_to_fstar_range
                                        (Prims.mk_range
                                           "FStar.Tactics.Derived.fst"
                                           (Prims.of_int (534))
                                           (Prims.of_int (8))
                                           (Prims.of_int (534))
                                           (Prims.of_int (43))))))
                       with
                       | FStar_Tactics_Result.Success (a,ps') ->
                           (match () with
                            | () ->
                                (apply t)
                                  (FStar_Tactics_Types.decr_depth
                                     (FStar_Tactics_Types.set_proofstate_range
                                        ps'
                                        (FStar_Range.prims_to_fstar_range
                                           (Prims.mk_range
                                              "FStar.Tactics.Derived.fst"
                                              (Prims.of_int (534))
                                              (Prims.of_int (45))
                                              (Prims.of_int (534))
                                              (Prims.of_int (52)))))))
                       | FStar_Tactics_Result.Failed (e,ps') ->
                           FStar_Tactics_Result.Failed (e, ps')))
             (fun uu___436_12634  ->
                try_with
                  (fun uu___441_12735  ->
                     match () with
                     | () -> FStar_Tactics_Builtins.apply_lemma t)
                  (fun uu___440_12737  ->
                     if d <= Prims.int_zero
                     then fail "mapply: out of fuel"
                     else
                       (fun ps  ->
                          match match (cur_env ())
                                        (FStar_Tactics_Types.incr_depth
                                           (FStar_Tactics_Types.set_proofstate_range
                                              (FStar_Tactics_Types.incr_depth
                                                 (FStar_Tactics_Types.set_proofstate_range
                                                    ps
                                                    (FStar_Range.prims_to_fstar_range
                                                       (Prims.mk_range
                                                          "FStar.Tactics.Derived.fst"
                                                          (Prims.of_int (540))
                                                          (Prims.of_int (13))
                                                          (Prims.of_int (540))
                                                          (Prims.of_int (30))))))
                                              (FStar_Range.prims_to_fstar_range
                                                 (Prims.mk_range
                                                    "FStar.Tactics.Derived.fst"
                                                    (Prims.of_int (540))
                                                    (Prims.of_int (16))
                                                    (Prims.of_int (540))
                                                    (Prims.of_int (28))))))
                                with
                                | FStar_Tactics_Result.Success (a,ps') ->
                                    (match () with
                                     | () ->
                                         (FStar_Tactics_Builtins.tc a t)
                                           (FStar_Tactics_Types.decr_depth
                                              (FStar_Tactics_Types.set_proofstate_range
                                                 ps'
                                                 (FStar_Range.prims_to_fstar_range
                                                    (Prims.mk_range
                                                       "FStar.Tactics.Derived.fst"
                                                       (Prims.of_int (540))
                                                       (Prims.of_int (13))
                                                       (Prims.of_int (540))
                                                       (Prims.of_int (30)))))))
                                | FStar_Tactics_Result.Failed (e,ps') ->
                                    FStar_Tactics_Result.Failed (e, ps')
                          with
                          | FStar_Tactics_Result.Success (a,ps') ->
                              (match () with
                               | () ->
                                   (match (FStar_Tactics_SyntaxHelpers.collect_arr
                                             a)
                                            (FStar_Tactics_Types.incr_depth
                                               (FStar_Tactics_Types.set_proofstate_range
                                                  (FStar_Tactics_Types.decr_depth
                                                     (FStar_Tactics_Types.set_proofstate_range
                                                        ps'
                                                        (FStar_Range.prims_to_fstar_range
                                                           (Prims.mk_range
                                                              "FStar.Tactics.Derived.fst"
                                                              (Prims.of_int (541))
                                                              (Prims.of_int (4))
                                                              (Prims.of_int (588))
                                                              (Prims.of_int (41))))))
                                                  (FStar_Range.prims_to_fstar_range
                                                     (Prims.mk_range
                                                        "FStar.Tactics.Derived.fst"
                                                        (Prims.of_int (541))
                                                        (Prims.of_int (17))
                                                        (Prims.of_int (541))
                                                        (Prims.of_int (31))))))
                                    with
                                    | FStar_Tactics_Result.Success (a1,ps'1)
                                        ->
                                        (match () with
                                         | () ->
                                             ((match a1 with
                                               | (tys,c) ->
                                                   (match FStar_Reflection_Basic.inspect_comp
                                                            c
                                                    with
                                                    | FStar_Reflection_Data.C_Lemma
                                                        (pre,post) ->
                                                        (fun ps1  ->
                                                           match (norm_term
                                                                    [] post)
                                                                   (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps1
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (545))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (545))
                                                                    (Prims.of_int (35))))))
                                                           with
                                                           | FStar_Tactics_Result.Success
                                                               (a2,ps'2) ->
                                                               (match () with
                                                                | () ->
                                                                    (
                                                                    match 
                                                                    (FStar_Reflection_Formula.term_as_formula'
                                                                    a2)
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (547))
                                                                    (Prims.of_int (7))
                                                                    (Prims.of_int (553))
                                                                    (Prims.of_int (41))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (547))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (547))
                                                                    (Prims.of_int (34))))))
                                                                    with
                                                                    | 
                                                                    FStar_Tactics_Result.Success
                                                                    (a3,ps'3)
                                                                    ->
                                                                    (match ()
                                                                    with
                                                                    | 
                                                                    () ->
                                                                    ((match a3
                                                                    with
                                                                    | FStar_Reflection_Formula.Implies
                                                                    (p,q) ->
                                                                    (fun ps2 
                                                                    ->
                                                                    match 
                                                                    (FStar_Tactics_Builtins.apply_lemma
                                                                    (FStar_Reflection_Basic.pack_ln
                                                                    (FStar_Reflection_Data.Tv_FVar
                                                                    (FStar_Reflection_Basic.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "Derived";
                                                                    "push1"]))))
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (549))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (549))
                                                                    (Prims.of_int (31))))))
                                                                    with
                                                                    | 
                                                                    FStar_Tactics_Result.Success
                                                                    (a4,ps'4)
                                                                    ->
                                                                    (match ()
                                                                    with
                                                                    | 
                                                                    () ->
                                                                    (apply_squash_or_lem
                                                                    (d -
                                                                    Prims.int_one)
                                                                    t)
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'4
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (550))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (550))
                                                                    (Prims.of_int (38)))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e,ps'4)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'4))
                                                                    | uu____13328
                                                                    ->
                                                                    fail
                                                                    "mapply: can't apply (1)"))
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (547))
                                                                    (Prims.of_int (7))
                                                                    (Prims.of_int (553))
                                                                    (Prims.of_int (41)))))))
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
                                                    | FStar_Reflection_Data.C_Total
                                                        (rt,uu____13335) ->
                                                        (match FStar_Reflection_Formula.unsquash
                                                                 rt
                                                         with
                                                         | FStar_Pervasives_Native.Some
                                                             rt1 ->
                                                             (fun ps1  ->
                                                                match 
                                                                  (norm_term
                                                                    [] rt1)
                                                                    (
                                                                    FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps1
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (561))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (561))
                                                                    (Prims.of_int (33))))))
                                                                with
                                                                | FStar_Tactics_Result.Success
                                                                    (a2,ps'2)
                                                                    ->
                                                                    (
                                                                    match ()
                                                                    with
                                                                    | 
                                                                    () ->
                                                                    (match 
                                                                    (FStar_Reflection_Formula.term_as_formula'
                                                                    a2)
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (563))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (569))
                                                                    (Prims.of_int (43))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (563))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (563))
                                                                    (Prims.of_int (34))))))
                                                                    with
                                                                    | 
                                                                    FStar_Tactics_Result.Success
                                                                    (a3,ps'3)
                                                                    ->
                                                                    (match ()
                                                                    with
                                                                    | 
                                                                    () ->
                                                                    ((match a3
                                                                    with
                                                                    | FStar_Reflection_Formula.Implies
                                                                    (p,q) ->
                                                                    (fun ps2 
                                                                    ->
                                                                    match 
                                                                    (FStar_Tactics_Builtins.apply_lemma
                                                                    (FStar_Reflection_Basic.pack_ln
                                                                    (FStar_Reflection_Data.Tv_FVar
                                                                    (FStar_Reflection_Basic.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "Derived";
                                                                    "push1"]))))
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (565))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (565))
                                                                    (Prims.of_int (33))))))
                                                                    with
                                                                    | 
                                                                    FStar_Tactics_Result.Success
                                                                    (a4,ps'4)
                                                                    ->
                                                                    (match ()
                                                                    with
                                                                    | 
                                                                    () ->
                                                                    (apply_squash_or_lem
                                                                    (d -
                                                                    Prims.int_one)
                                                                    t)
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'4
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (566))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (566))
                                                                    (Prims.of_int (40)))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e,ps'4)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'4))
                                                                    | uu____13402
                                                                    ->
                                                                    fail
                                                                    "mapply: can't apply (1)"))
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (563))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (569))
                                                                    (Prims.of_int (43)))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e,ps'3)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'3)))
                                                                | FStar_Tactics_Result.Failed
                                                                    (e,ps'2)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'2))
                                                         | FStar_Pervasives_Native.None
                                                              ->
                                                             (fun ps1  ->
                                                                match 
                                                                  (norm_term
                                                                    [] rt)
                                                                    (
                                                                    FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps1
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (576))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (576))
                                                                    (Prims.of_int (33))))))
                                                                with
                                                                | FStar_Tactics_Result.Success
                                                                    (a2,ps'2)
                                                                    ->
                                                                    (
                                                                    match ()
                                                                    with
                                                                    | 
                                                                    () ->
                                                                    (match 
                                                                    (FStar_Reflection_Formula.term_as_formula'
                                                                    a2)
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (578))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (585))
                                                                    (Prims.of_int (20))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (578))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (578))
                                                                    (Prims.of_int (34))))))
                                                                    with
                                                                    | 
                                                                    FStar_Tactics_Result.Success
                                                                    (a3,ps'3)
                                                                    ->
                                                                    (match ()
                                                                    with
                                                                    | 
                                                                    () ->
                                                                    ((match a3
                                                                    with
                                                                    | FStar_Reflection_Formula.Implies
                                                                    (p,q) ->
                                                                    (fun ps2 
                                                                    ->
                                                                    match 
                                                                    (FStar_Tactics_Builtins.apply_lemma
                                                                    (FStar_Reflection_Basic.pack_ln
                                                                    (FStar_Reflection_Data.Tv_FVar
                                                                    (FStar_Reflection_Basic.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "Derived";
                                                                    "push1"]))))
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (580))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (580))
                                                                    (Prims.of_int (33))))))
                                                                    with
                                                                    | 
                                                                    FStar_Tactics_Result.Success
                                                                    (a4,ps'4)
                                                                    ->
                                                                    (match ()
                                                                    with
                                                                    | 
                                                                    () ->
                                                                    (apply_squash_or_lem
                                                                    (d -
                                                                    Prims.int_one)
                                                                    t)
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'4
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (581))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (581))
                                                                    (Prims.of_int (40)))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e,ps'4)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'4))
                                                                    | uu____13471
                                                                    ->
                                                                    (fun ps2 
                                                                    ->
                                                                    match 
                                                                    (apply
                                                                    (FStar_Reflection_Basic.pack_ln
                                                                    (FStar_Reflection_Data.Tv_FVar
                                                                    (FStar_Reflection_Basic.pack_fv
                                                                    ["FStar";
                                                                    "Squash";
                                                                    "return_squash"]))))
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (584))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (584))
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
                                                                    (apply t)
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'4
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (585))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (585))
                                                                    (Prims.of_int (20)))))))
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
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (578))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (585))
                                                                    (Prims.of_int (20)))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e,ps'3)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'3)))
                                                                | FStar_Tactics_Result.Failed
                                                                    (e,ps'2)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'2)))
                                                    | uu____13504 ->
                                                        fail
                                                          "mapply: can't apply (2)")))
                                               (FStar_Tactics_Types.decr_depth
                                                  (FStar_Tactics_Types.set_proofstate_range
                                                     ps'1
                                                     (FStar_Range.prims_to_fstar_range
                                                        (Prims.mk_range
                                                           "FStar.Tactics.Derived.fst"
                                                           (Prims.of_int (541))
                                                           (Prims.of_int (4))
                                                           (Prims.of_int (588))
                                                           (Prims.of_int (41)))))))
                                    | FStar_Tactics_Result.Failed (e,ps'1) ->
                                        FStar_Tactics_Result.Failed (e, ps'1)))
                          | FStar_Tactics_Result.Failed (e,ps') ->
                              FStar_Tactics_Result.Failed (e, ps')))))
  
let (mapply :
  FStar_Reflection_Types.term ->
    (unit,unit) FStar_Tactics_Effect._dm4f_TAC_repr)
  = fun t  -> apply_squash_or_lem (Prims.of_int (10)) t 
let admit_dump : 'Aa . (unit -> 'Aa) -> unit -> 'Aa =
  fun x  -> fun uu____13564  -> x () 
let magic_dump : 'Aa . 'Aa -> unit -> 'Aa = fun x  -> fun uu____13587  -> x 
let (change_with :
  FStar_Reflection_Types.term ->
    FStar_Reflection_Types.term ->
      (unit,unit) FStar_Tactics_Effect._dm4f_TAC_repr)
  =
  fun t1  ->
    fun t2  ->
      focus
        (fun uu____13639  ->
           fun ps  ->
             match (grewrite t1 t2)
                     (FStar_Tactics_Types.incr_depth
                        (FStar_Tactics_Types.set_proofstate_range ps
                           (FStar_Range.prims_to_fstar_range
                              (Prims.mk_range "FStar.Tactics.Derived.fst"
                                 (Prims.of_int (603)) (Prims.of_int (8))
                                 (Prims.of_int (603)) (Prims.of_int (22))))))
             with
             | FStar_Tactics_Result.Success (a,ps') ->
                 (match () with
                  | () ->
                      (iseq [idtac; FStar_Tactics_Builtins.trivial])
                        (FStar_Tactics_Types.decr_depth
                           (FStar_Tactics_Types.set_proofstate_range ps'
                              (FStar_Range.prims_to_fstar_range
                                 (Prims.mk_range "FStar.Tactics.Derived.fst"
                                    (Prims.of_int (604)) (Prims.of_int (8))
                                    (Prims.of_int (604)) (Prims.of_int (29)))))))
             | FStar_Tactics_Result.Failed (e,ps') ->
                 FStar_Tactics_Result.Failed (e, ps'))
  
let (change_sq :
  FStar_Reflection_Types.term ->
    (unit,unit) FStar_Tactics_Effect._dm4f_TAC_repr)
  =
  fun t1  ->
    FStar_Tactics_Builtins.change
      (FStar_Reflection_Derived.mk_e_app
         (FStar_Reflection_Basic.pack_ln
            (FStar_Reflection_Data.Tv_FVar
               (FStar_Reflection_Basic.pack_fv ["Prims"; "squash"]))) 
         [t1])
  
let finish_by :
  'a .
    (unit -> ('a,unit) FStar_Tactics_Effect._dm4f_TAC_repr) ->
      ('a,unit) FStar_Tactics_Effect._dm4f_TAC_repr
  =
  fun t  ->
    fun ps  ->
      match (t ())
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.Derived.fst"
                          (Prims.of_int (611)) (Prims.of_int (12))
                          (Prims.of_int (611)) (Prims.of_int (16))))))
      with
      | FStar_Tactics_Result.Success (a,ps') ->
          (match () with
           | () ->
               (match (or_else qed
                         (fun uu____13914  -> fail "finish_by: not finished"))
                        (FStar_Tactics_Types.incr_depth
                           (FStar_Tactics_Types.set_proofstate_range
                              (FStar_Tactics_Types.decr_depth
                                 (FStar_Tactics_Types.set_proofstate_range
                                    ps'
                                    (FStar_Range.prims_to_fstar_range
                                       (Prims.mk_range
                                          "FStar.Tactics.Derived.fst"
                                          (Prims.of_int (612))
                                          (Prims.of_int (4))
                                          (Prims.of_int (613))
                                          (Prims.of_int (5))))))
                              (FStar_Range.prims_to_fstar_range
                                 (Prims.mk_range "FStar.Tactics.Derived.fst"
                                    (Prims.of_int (612)) (Prims.of_int (4))
                                    (Prims.of_int (612)) (Prims.of_int (58))))))
                with
                | FStar_Tactics_Result.Success (a1,ps'1) ->
                    (match () with
                     | () ->
                         FStar_Tactics_Result.Success
                           (a,
                             (FStar_Tactics_Types.decr_depth
                                (FStar_Tactics_Types.set_proofstate_range
                                   ps'1
                                   (FStar_Range.prims_to_fstar_range
                                      (Prims.mk_range
                                         "FStar.Tactics.Derived.fst"
                                         (Prims.of_int (611))
                                         (Prims.of_int (8))
                                         (Prims.of_int (611))
                                         (Prims.of_int (9))))))))
                | FStar_Tactics_Result.Failed (e,ps'1) ->
                    FStar_Tactics_Result.Failed (e, ps'1)))
      | FStar_Tactics_Result.Failed (e,ps') ->
          FStar_Tactics_Result.Failed (e, ps')
  
let solve_then :
  'Aa 'Ab .
    (unit -> ('Aa,unit) FStar_Tactics_Effect._dm4f_TAC_repr) ->
      ('Aa -> ('Ab,unit) FStar_Tactics_Effect._dm4f_TAC_repr) ->
        ('Ab,unit) FStar_Tactics_Effect._dm4f_TAC_repr
  =
  fun t1  ->
    fun t2  ->
      fun ps  ->
        match (FStar_Tactics_Builtins.dup ())
                (FStar_Tactics_Types.incr_depth
                   (FStar_Tactics_Types.set_proofstate_range ps
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range "FStar.Tactics.Derived.fst"
                            (Prims.of_int (616)) (Prims.of_int (4))
                            (Prims.of_int (616)) (Prims.of_int (10))))))
        with
        | FStar_Tactics_Result.Success (a,ps') ->
            (match () with
             | () ->
                 (match (focus (fun uu____14141  -> finish_by t1))
                          (FStar_Tactics_Types.incr_depth
                             (FStar_Tactics_Types.set_proofstate_range
                                (FStar_Tactics_Types.decr_depth
                                   (FStar_Tactics_Types.set_proofstate_range
                                      ps'
                                      (FStar_Range.prims_to_fstar_range
                                         (Prims.mk_range
                                            "FStar.Tactics.Derived.fst"
                                            (Prims.of_int (617))
                                            (Prims.of_int (4))
                                            (Prims.of_int (620))
                                            (Prims.of_int (5))))))
                                (FStar_Range.prims_to_fstar_range
                                   (Prims.mk_range
                                      "FStar.Tactics.Derived.fst"
                                      (Prims.of_int (617))
                                      (Prims.of_int (12))
                                      (Prims.of_int (617))
                                      (Prims.of_int (42))))))
                  with
                  | FStar_Tactics_Result.Success (a1,ps'1) ->
                      (match () with
                       | () ->
                           (match (t2 a1)
                                    (FStar_Tactics_Types.incr_depth
                                       (FStar_Tactics_Types.set_proofstate_range
                                          (FStar_Tactics_Types.decr_depth
                                             (FStar_Tactics_Types.set_proofstate_range
                                                ps'1
                                                (FStar_Range.prims_to_fstar_range
                                                   (Prims.mk_range
                                                      "FStar.Tactics.Derived.fst"
                                                      (Prims.of_int (618))
                                                      (Prims.of_int (4))
                                                      (Prims.of_int (620))
                                                      (Prims.of_int (5))))))
                                          (FStar_Range.prims_to_fstar_range
                                             (Prims.mk_range
                                                "FStar.Tactics.Derived.fst"
                                                (Prims.of_int (618))
                                                (Prims.of_int (12))
                                                (Prims.of_int (618))
                                                (Prims.of_int (16))))))
                            with
                            | FStar_Tactics_Result.Success (a2,ps'2) ->
                                (match () with
                                 | () ->
                                     (match (FStar_Tactics_Builtins.trefl ())
                                              (FStar_Tactics_Types.incr_depth
                                                 (FStar_Tactics_Types.set_proofstate_range
                                                    (FStar_Tactics_Types.decr_depth
                                                       (FStar_Tactics_Types.set_proofstate_range
                                                          ps'2
                                                          (FStar_Range.prims_to_fstar_range
                                                             (Prims.mk_range
                                                                "FStar.Tactics.Derived.fst"
                                                                (Prims.of_int (619))
                                                                (Prims.of_int (4))
                                                                (Prims.of_int (620))
                                                                (Prims.of_int (5))))))
                                                    (FStar_Range.prims_to_fstar_range
                                                       (Prims.mk_range
                                                          "FStar.Tactics.Derived.fst"
                                                          (Prims.of_int (619))
                                                          (Prims.of_int (4))
                                                          (Prims.of_int (619))
                                                          (Prims.of_int (12))))))
                                      with
                                      | FStar_Tactics_Result.Success
                                          (a3,ps'3) ->
                                          (match () with
                                           | () ->
                                               FStar_Tactics_Result.Success
                                                 (a2,
                                                   (FStar_Tactics_Types.decr_depth
                                                      (FStar_Tactics_Types.set_proofstate_range
                                                         ps'3
                                                         (FStar_Range.prims_to_fstar_range
                                                            (Prims.mk_range
                                                               "FStar.Tactics.Derived.fst"
                                                               (Prims.of_int (618))
                                                               (Prims.of_int (8))
                                                               (Prims.of_int (618))
                                                               (Prims.of_int (9))))))))
                                      | FStar_Tactics_Result.Failed (e,ps'3)
                                          ->
                                          FStar_Tactics_Result.Failed
                                            (e, ps'3)))
                            | FStar_Tactics_Result.Failed (e,ps'2) ->
                                FStar_Tactics_Result.Failed (e, ps'2)))
                  | FStar_Tactics_Result.Failed (e,ps'1) ->
                      FStar_Tactics_Result.Failed (e, ps'1)))
        | FStar_Tactics_Result.Failed (e,ps') ->
            FStar_Tactics_Result.Failed (e, ps')
  
let add_elem :
  'a .
    (unit -> ('a,unit) FStar_Tactics_Effect._dm4f_TAC_repr) ->
      ('a,unit) FStar_Tactics_Effect._dm4f_TAC_repr
  =
  fun t  ->
    focus
      (fun uu____14257  ->
         fun ps  ->
           match (apply
                    (FStar_Reflection_Basic.pack_ln
                       (FStar_Reflection_Data.Tv_FVar
                          (FStar_Reflection_Basic.pack_fv ["Prims"; "Cons"]))))
                   (FStar_Tactics_Types.incr_depth
                      (FStar_Tactics_Types.set_proofstate_range ps
                         (FStar_Range.prims_to_fstar_range
                            (Prims.mk_range "FStar.Tactics.Derived.fst"
                               (Prims.of_int (623)) (Prims.of_int (4))
                               (Prims.of_int (623)) (Prims.of_int (17))))))
           with
           | FStar_Tactics_Result.Success (a,ps') ->
               (match () with
                | () ->
                    (focus
                       (fun uu____14319  ->
                          fun ps1  ->
                            match (t ())
                                    (FStar_Tactics_Types.incr_depth
                                       (FStar_Tactics_Types.set_proofstate_range
                                          ps1
                                          (FStar_Range.prims_to_fstar_range
                                             (Prims.mk_range
                                                "FStar.Tactics.Derived.fst"
                                                (Prims.of_int (625))
                                                (Prims.of_int (14))
                                                (Prims.of_int (625))
                                                (Prims.of_int (18))))))
                            with
                            | FStar_Tactics_Result.Success (a1,ps'1) ->
                                (match () with
                                 | () ->
                                     (match (qed ())
                                              (FStar_Tactics_Types.incr_depth
                                                 (FStar_Tactics_Types.set_proofstate_range
                                                    (FStar_Tactics_Types.decr_depth
                                                       (FStar_Tactics_Types.set_proofstate_range
                                                          ps'1
                                                          (FStar_Range.prims_to_fstar_range
                                                             (Prims.mk_range
                                                                "FStar.Tactics.Derived.fst"
                                                                (Prims.of_int (626))
                                                                (Prims.of_int (6))
                                                                (Prims.of_int (627))
                                                                (Prims.of_int (7))))))
                                                    (FStar_Range.prims_to_fstar_range
                                                       (Prims.mk_range
                                                          "FStar.Tactics.Derived.fst"
                                                          (Prims.of_int (626))
                                                          (Prims.of_int (6))
                                                          (Prims.of_int (626))
                                                          (Prims.of_int (12))))))
                                      with
                                      | FStar_Tactics_Result.Success
                                          (a2,ps'2) ->
                                          (match () with
                                           | () ->
                                               FStar_Tactics_Result.Success
                                                 (a1,
                                                   (FStar_Tactics_Types.decr_depth
                                                      (FStar_Tactics_Types.set_proofstate_range
                                                         ps'2
                                                         (FStar_Range.prims_to_fstar_range
                                                            (Prims.mk_range
                                                               "FStar.Tactics.Derived.fst"
                                                               (Prims.of_int (625))
                                                               (Prims.of_int (10))
                                                               (Prims.of_int (625))
                                                               (Prims.of_int (11))))))))
                                      | FStar_Tactics_Result.Failed (e,ps'2)
                                          ->
                                          FStar_Tactics_Result.Failed
                                            (e, ps'2)))
                            | FStar_Tactics_Result.Failed (e,ps'1) ->
                                FStar_Tactics_Result.Failed (e, ps'1)))
                      (FStar_Tactics_Types.decr_depth
                         (FStar_Tactics_Types.set_proofstate_range ps'
                            (FStar_Range.prims_to_fstar_range
                               (Prims.mk_range "FStar.Tactics.Derived.fst"
                                  (Prims.of_int (624)) (Prims.of_int (4))
                                  (Prims.of_int (628)) (Prims.of_int (5)))))))
           | FStar_Tactics_Result.Failed (e,ps') ->
               FStar_Tactics_Result.Failed (e, ps'))
  
let specialize :
  'Aa .
    'Aa ->
      Prims.string Prims.list ->
        unit -> (unit,unit) FStar_Tactics_Effect._dm4f_TAC_repr
  =
  fun f  ->
    fun l  ->
      fun uu____14440  ->
        solve_then
          (fun uu____14455  ->
             fun ps  ->
               match () with
               | () ->
                   (exact
                      (Obj.magic
                         (failwith
                            "Cannot evaluate open quotation at runtime")))
                     (FStar_Tactics_Types.decr_depth
                        (FStar_Tactics_Types.set_proofstate_range
                           (FStar_Tactics_Types.incr_depth
                              (FStar_Tactics_Types.set_proofstate_range ps
                                 (FStar_Range.prims_to_fstar_range
                                    (Prims.mk_range
                                       "FStar.Tactics.Derived.fst"
                                       (Prims.of_int (647))
                                       (Prims.of_int (42))
                                       (Prims.of_int (647))
                                       (Prims.of_int (51))))))
                           (FStar_Range.prims_to_fstar_range
                              (Prims.mk_range "FStar.Tactics.Derived.fst"
                                 (Prims.of_int (647)) (Prims.of_int (36))
                                 (Prims.of_int (647)) (Prims.of_int (51)))))))
          (fun uu____14490  ->
             FStar_Tactics_Builtins.norm
               [FStar_Pervasives.delta_only l;
               FStar_Pervasives.iota;
               FStar_Pervasives.zeta])
  
let (tlabel :
  Prims.string -> (unit,unit) FStar_Tactics_Effect._dm4f_TAC_repr) =
  fun l  ->
    fun ps  ->
      match (goals ())
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.Derived.fst"
                          (Prims.of_int (650)) (Prims.of_int (10))
                          (Prims.of_int (650)) (Prims.of_int (18))))))
      with
      | FStar_Tactics_Result.Success (a,ps') ->
          (match () with
           | () ->
               ((match a with
                 | [] -> fail "tlabel: no goals"
                 | h::t ->
                     FStar_Tactics_Builtins.set_goals
                       ((FStar_Tactics_Types.set_label l h) :: t)))
                 (FStar_Tactics_Types.decr_depth
                    (FStar_Tactics_Types.set_proofstate_range ps'
                       (FStar_Range.prims_to_fstar_range
                          (Prims.mk_range "FStar.Tactics.Derived.fst"
                             (Prims.of_int (650)) (Prims.of_int (4))
                             (Prims.of_int (653)) (Prims.of_int (38)))))))
      | FStar_Tactics_Result.Failed (e,ps') ->
          FStar_Tactics_Result.Failed (e, ps')
  
let (tlabel' :
  Prims.string -> (unit,unit) FStar_Tactics_Effect._dm4f_TAC_repr) =
  fun l  ->
    fun ps  ->
      match (goals ())
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.Derived.fst"
                          (Prims.of_int (656)) (Prims.of_int (10))
                          (Prims.of_int (656)) (Prims.of_int (18))))))
      with
      | FStar_Tactics_Result.Success (a,ps') ->
          (match () with
           | () ->
               ((match a with
                 | [] -> fail "tlabel': no goals"
                 | h::t ->
                     (fun ps1  ->
                        match () with
                        | () ->
                            (FStar_Tactics_Builtins.set_goals
                               ((FStar_Tactics_Types.set_label
                                   (Prims.strcat l
                                      (FStar_Tactics_Types.get_label h)) h)
                               :: t))
                              (FStar_Tactics_Types.decr_depth
                                 (FStar_Tactics_Types.set_proofstate_range
                                    (FStar_Tactics_Types.incr_depth
                                       (FStar_Tactics_Types.set_proofstate_range
                                          ps1
                                          (FStar_Range.prims_to_fstar_range
                                             (Prims.mk_range
                                                "FStar.Tactics.Derived.fst"
                                                (Prims.of_int (659))
                                                (Prims.of_int (16))
                                                (Prims.of_int (659))
                                                (Prims.of_int (45))))))
                                    (FStar_Range.prims_to_fstar_range
                                       (Prims.mk_range
                                          "FStar.Tactics.Derived.fst"
                                          (Prims.of_int (660))
                                          (Prims.of_int (8))
                                          (Prims.of_int (660))
                                          (Prims.of_int (26)))))))))
                 (FStar_Tactics_Types.decr_depth
                    (FStar_Tactics_Types.set_proofstate_range ps'
                       (FStar_Range.prims_to_fstar_range
                          (Prims.mk_range "FStar.Tactics.Derived.fst"
                             (Prims.of_int (656)) (Prims.of_int (4))
                             (Prims.of_int (660)) (Prims.of_int (26)))))))
      | FStar_Tactics_Result.Failed (e,ps') ->
          FStar_Tactics_Result.Failed (e, ps')
  
let (focus_all : unit -> (unit,unit) FStar_Tactics_Effect._dm4f_TAC_repr) =
  fun uu____14755  ->
    fun ps  ->
      match match match (goals ())
                          (FStar_Tactics_Types.incr_depth
                             (FStar_Tactics_Types.set_proofstate_range
                                (FStar_Tactics_Types.incr_depth
                                   (FStar_Tactics_Types.set_proofstate_range
                                      (FStar_Tactics_Types.incr_depth
                                         (FStar_Tactics_Types.set_proofstate_range
                                            ps
                                            (FStar_Range.prims_to_fstar_range
                                               (Prims.mk_range
                                                  "FStar.Tactics.Derived.fst"
                                                  (Prims.of_int (663))
                                                  (Prims.of_int (4))
                                                  (Prims.of_int (663))
                                                  (Prims.of_int (39))))))
                                      (FStar_Range.prims_to_fstar_range
                                         (Prims.mk_range
                                            "FStar.Tactics.Derived.fst"
                                            (Prims.of_int (663))
                                            (Prims.of_int (14))
                                            (Prims.of_int (663))
                                            (Prims.of_int (39))))))
                                (FStar_Range.prims_to_fstar_range
                                   (Prims.mk_range
                                      "FStar.Tactics.Derived.fst"
                                      (Prims.of_int (663))
                                      (Prims.of_int (15))
                                      (Prims.of_int (663))
                                      (Prims.of_int (23))))))
                  with
                  | FStar_Tactics_Result.Success (a,ps') ->
                      (match () with
                       | () ->
                           (match (smt_goals ())
                                    (FStar_Tactics_Types.incr_depth
                                       (FStar_Tactics_Types.set_proofstate_range
                                          (FStar_Tactics_Types.decr_depth
                                             (FStar_Tactics_Types.set_proofstate_range
                                                ps'
                                                (FStar_Range.prims_to_fstar_range
                                                   (Prims.mk_range
                                                      "FStar.Tactics.Derived.fst"
                                                      (Prims.of_int (663))
                                                      (Prims.of_int (14))
                                                      (Prims.of_int (663))
                                                      (Prims.of_int (39))))))
                                          (FStar_Range.prims_to_fstar_range
                                             (Prims.mk_range
                                                "FStar.Tactics.Derived.fst"
                                                (Prims.of_int (663))
                                                (Prims.of_int (26))
                                                (Prims.of_int (663))
                                                (Prims.of_int (38))))))
                            with
                            | FStar_Tactics_Result.Success (a1,ps'1) ->
                                (match () with
                                 | () ->
                                     FStar_Tactics_Result.Success
                                       ((FStar_List_Tot_Base.append a a1),
                                         (FStar_Tactics_Types.decr_depth
                                            (FStar_Tactics_Types.set_proofstate_range
                                               ps'1
                                               (FStar_Range.prims_to_fstar_range
                                                  (Prims.mk_range
                                                     "FStar.Tactics.Derived.fst"
                                                     (Prims.of_int (663))
                                                     (Prims.of_int (14))
                                                     (Prims.of_int (663))
                                                     (Prims.of_int (39))))))))
                            | FStar_Tactics_Result.Failed (e,ps'1) ->
                                FStar_Tactics_Result.Failed (e, ps'1)))
                  | FStar_Tactics_Result.Failed (e,ps') ->
                      FStar_Tactics_Result.Failed (e, ps')
            with
            | FStar_Tactics_Result.Success (a,ps') ->
                (match () with
                 | () ->
                     (FStar_Tactics_Builtins.set_goals a)
                       (FStar_Tactics_Types.decr_depth
                          (FStar_Tactics_Types.set_proofstate_range ps'
                             (FStar_Range.prims_to_fstar_range
                                (Prims.mk_range "FStar.Tactics.Derived.fst"
                                   (Prims.of_int (663)) (Prims.of_int (4))
                                   (Prims.of_int (663)) (Prims.of_int (39)))))))
            | FStar_Tactics_Result.Failed (e,ps') ->
                FStar_Tactics_Result.Failed (e, ps')
      with
      | FStar_Tactics_Result.Success (a,ps') ->
          (match () with
           | () ->
               (FStar_Tactics_Builtins.set_smt_goals [])
                 (FStar_Tactics_Types.decr_depth
                    (FStar_Tactics_Types.set_proofstate_range ps'
                       (FStar_Range.prims_to_fstar_range
                          (Prims.mk_range "FStar.Tactics.Derived.fst"
                             (Prims.of_int (664)) (Prims.of_int (4))
                             (Prims.of_int (664)) (Prims.of_int (20)))))))
      | FStar_Tactics_Result.Failed (e,ps') ->
          FStar_Tactics_Result.Failed (e, ps')
  
let rec extract_nth :
  'a .
    Prims.nat ->
      'a Prims.list -> ('a * 'a Prims.list) FStar_Pervasives_Native.option
  =
  fun n1  ->
    fun l  ->
      match (n1, l) with
      | (uu____14945,[]) -> FStar_Pervasives_Native.None
      | (_14961,hd1::tl1) when _14961 = Prims.int_zero ->
          FStar_Pervasives_Native.Some (hd1, tl1)
      | (uu____14972,hd1::tl1) ->
          (match extract_nth (n1 - Prims.int_one) tl1 with
           | FStar_Pervasives_Native.Some (hd',tl') ->
               FStar_Pervasives_Native.Some (hd', (hd1 :: tl'))
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
  
let (bump_nth : Prims.pos -> (unit,unit) FStar_Tactics_Effect._dm4f_TAC_repr)
  =
  fun n1  ->
    fun ps  ->
      match match (goals ())
                    (FStar_Tactics_Types.incr_depth
                       (FStar_Tactics_Types.set_proofstate_range
                          (FStar_Tactics_Types.incr_depth
                             (FStar_Tactics_Types.set_proofstate_range ps
                                (FStar_Range.prims_to_fstar_range
                                   (Prims.mk_range
                                      "FStar.Tactics.Derived.fst"
                                      (Prims.of_int (679)) (Prims.of_int (8))
                                      (Prims.of_int (679))
                                      (Prims.of_int (38))))))
                          (FStar_Range.prims_to_fstar_range
                             (Prims.mk_range "FStar.Tactics.Derived.fst"
                                (Prims.of_int (679)) (Prims.of_int (28))
                                (Prims.of_int (679)) (Prims.of_int (38))))))
            with
            | FStar_Tactics_Result.Success (a,ps') ->
                (match () with
                 | () ->
                     FStar_Tactics_Result.Success
                       ((extract_nth (n1 - Prims.int_one) a),
                         (FStar_Tactics_Types.decr_depth
                            (FStar_Tactics_Types.set_proofstate_range ps'
                               (FStar_Range.prims_to_fstar_range
                                  (Prims.mk_range "FStar.Tactics.Derived.fst"
                                     (Prims.of_int (679)) (Prims.of_int (8))
                                     (Prims.of_int (679)) (Prims.of_int (38))))))))
            | FStar_Tactics_Result.Failed (e,ps') ->
                FStar_Tactics_Result.Failed (e, ps')
      with
      | FStar_Tactics_Result.Success (a,ps') ->
          (match () with
           | () ->
               ((match a with
                 | FStar_Pervasives_Native.None  ->
                     fail "bump_nth: not that many goals"
                 | FStar_Pervasives_Native.Some (h,t) ->
                     FStar_Tactics_Builtins.set_goals (h :: t)))
                 (FStar_Tactics_Types.decr_depth
                    (FStar_Tactics_Types.set_proofstate_range ps'
                       (FStar_Range.prims_to_fstar_range
                          (Prims.mk_range "FStar.Tactics.Derived.fst"
                             (Prims.of_int (679)) (Prims.of_int (2))
                             (Prims.of_int (681)) (Prims.of_int (37)))))))
      | FStar_Tactics_Result.Failed (e,ps') ->
          FStar_Tactics_Result.Failed (e, ps')
  
let (on_sort_bv :
  (FStar_Reflection_Types.term ->
     (FStar_Reflection_Types.term,unit) FStar_Tactics_Effect._dm4f_TAC_repr)
    ->
    FStar_Reflection_Types.bv ->
      (FStar_Reflection_Types.bv,unit) FStar_Tactics_Effect._dm4f_TAC_repr)
  =
  fun f  ->
    fun xbv  ->
      fun ps  ->
        match () with
        | () ->
            (match match () with
                   | () ->
                       (match (f
                                 (FStar_Reflection_Basic.inspect_bv xbv).FStar_Reflection_Data.bv_sort)
                                (FStar_Tactics_Types.incr_depth
                                   (FStar_Tactics_Types.set_proofstate_range
                                      (FStar_Tactics_Types.decr_depth
                                         (FStar_Tactics_Types.set_proofstate_range
                                            (FStar_Tactics_Types.incr_depth
                                               (FStar_Tactics_Types.set_proofstate_range
                                                  (FStar_Tactics_Types.incr_depth
                                                     (FStar_Tactics_Types.set_proofstate_range
                                                        (FStar_Tactics_Types.decr_depth
                                                           (FStar_Tactics_Types.set_proofstate_range
                                                              (FStar_Tactics_Types.incr_depth
                                                                 (FStar_Tactics_Types.set_proofstate_range
                                                                    ps
                                                                    (
                                                                    FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (684))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (684))
                                                                    (Prims.of_int (26))))))
                                                              (FStar_Range.prims_to_fstar_range
                                                                 (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (685))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (687))
                                                                    (Prims.of_int (4))))))
                                                        (FStar_Range.prims_to_fstar_range
                                                           (Prims.mk_range
                                                              "FStar.Tactics.Derived.fst"
                                                              (Prims.of_int (685))
                                                              (Prims.of_int (14))
                                                              (Prims.of_int (685))
                                                              (Prims.of_int (46))))))
                                                  (FStar_Range.prims_to_fstar_range
                                                     (Prims.mk_range
                                                        "FStar.Tactics.Derived.fst"
                                                        (Prims.of_int (685))
                                                        (Prims.of_int (14))
                                                        (Prims.of_int (685))
                                                        (Prims.of_int (17))))))
                                            (FStar_Range.prims_to_fstar_range
                                               (Prims.mk_range
                                                  "FStar.Tactics.Derived.fst"
                                                  (Prims.of_int (685))
                                                  (Prims.of_int (14))
                                                  (Prims.of_int (685))
                                                  (Prims.of_int (46))))))
                                      (FStar_Range.prims_to_fstar_range
                                         (Prims.mk_range
                                            "FStar.Tactics.Derived.fst"
                                            (Prims.of_int (685))
                                            (Prims.of_int (33))
                                            (Prims.of_int (685))
                                            (Prims.of_int (46))))))
                        with
                        | FStar_Tactics_Result.Success (a,ps') ->
                            (match () with
                             | () ->
                                 FStar_Tactics_Result.Success
                                   ({
                                      FStar_Reflection_Data.bv_ppname =
                                        ((FStar_Reflection_Basic.inspect_bv
                                            xbv).FStar_Reflection_Data.bv_ppname);
                                      FStar_Reflection_Data.bv_index =
                                        ((FStar_Reflection_Basic.inspect_bv
                                            xbv).FStar_Reflection_Data.bv_index);
                                      FStar_Reflection_Data.bv_sort = a
                                    },
                                     (FStar_Tactics_Types.decr_depth
                                        (FStar_Tactics_Types.set_proofstate_range
                                           ps'
                                           (FStar_Range.prims_to_fstar_range
                                              (Prims.mk_range
                                                 "FStar.Tactics.Derived.fst"
                                                 (Prims.of_int (685))
                                                 (Prims.of_int (14))
                                                 (Prims.of_int (685))
                                                 (Prims.of_int (46))))))))
                        | FStar_Tactics_Result.Failed (e,ps') ->
                            FStar_Tactics_Result.Failed (e, ps'))
             with
             | FStar_Tactics_Result.Success (a,ps') ->
                 (match () with
                  | () ->
                      FStar_Tactics_Result.Success
                        ((FStar_Reflection_Basic.pack_bv a),
                          (FStar_Tactics_Types.decr_depth
                             (FStar_Tactics_Types.set_proofstate_range ps'
                                (FStar_Range.prims_to_fstar_range
                                   (Prims.mk_range
                                      "FStar.Tactics.Derived.fst"
                                      (Prims.of_int (686))
                                      (Prims.of_int (11))
                                      (Prims.of_int (686))
                                      (Prims.of_int (22))))))))
             | FStar_Tactics_Result.Failed (e,ps') ->
                 FStar_Tactics_Result.Failed (e, ps'))
  
let (on_sort_binder :
  (FStar_Reflection_Types.term ->
     (FStar_Reflection_Types.term,unit) FStar_Tactics_Effect._dm4f_TAC_repr)
    ->
    FStar_Reflection_Types.binder ->
      (FStar_Reflection_Types.binder,unit)
        FStar_Tactics_Effect._dm4f_TAC_repr)
  =
  fun f  ->
    fun b  ->
      fun ps  ->
        match () with
        | () ->
            ((match FStar_Reflection_Basic.inspect_binder b with
              | (bv,q) ->
                  (fun ps1  ->
                     match (on_sort_bv f bv)
                             (FStar_Tactics_Types.incr_depth
                                (FStar_Tactics_Types.set_proofstate_range ps1
                                   (FStar_Range.prims_to_fstar_range
                                      (Prims.mk_range
                                         "FStar.Tactics.Derived.fst"
                                         (Prims.of_int (691))
                                         (Prims.of_int (11))
                                         (Prims.of_int (691))
                                         (Prims.of_int (26))))))
                     with
                     | FStar_Tactics_Result.Success (a,ps') ->
                         (match () with
                          | () ->
                              FStar_Tactics_Result.Success
                                ((FStar_Reflection_Basic.pack_binder a q),
                                  (FStar_Tactics_Types.decr_depth
                                     (FStar_Tactics_Types.set_proofstate_range
                                        ps'
                                        (FStar_Range.prims_to_fstar_range
                                           (Prims.mk_range
                                              "FStar.Tactics.Derived.fst"
                                              (Prims.of_int (692))
                                              (Prims.of_int (10))
                                              (Prims.of_int (692))
                                              (Prims.of_int (26))))))))
                     | FStar_Tactics_Result.Failed (e,ps') ->
                         FStar_Tactics_Result.Failed (e, ps'))))
              (FStar_Tactics_Types.decr_depth
                 (FStar_Tactics_Types.set_proofstate_range
                    (FStar_Tactics_Types.incr_depth
                       (FStar_Tactics_Types.set_proofstate_range ps
                          (FStar_Range.prims_to_fstar_range
                             (Prims.mk_range "FStar.Tactics.Derived.fst"
                                (Prims.of_int (690)) (Prims.of_int (16))
                                (Prims.of_int (690)) (Prims.of_int (32))))))
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.Derived.fst"
                          (Prims.of_int (690)) (Prims.of_int (2))
                          (Prims.of_int (693)) (Prims.of_int (3))))))
  
let rec (visit_tm :
  (FStar_Reflection_Types.term ->
     (FStar_Reflection_Types.term,unit) FStar_Tactics_Effect._dm4f_TAC_repr)
    ->
    FStar_Reflection_Types.term ->
      (FStar_Reflection_Types.term,unit) FStar_Tactics_Effect._dm4f_TAC_repr)
  =
  fun ff  ->
    fun t  ->
      fun ps  ->
        match () with
        | () ->
            (match (match FStar_Reflection_Basic.inspect_ln t with
                    | FStar_Reflection_Data.Tv_FVar uu____16296 ->
                        (fun s  ->
                           FStar_Tactics_Result.Success
                             ((FStar_Reflection_Basic.inspect_ln t), s))
                    | FStar_Reflection_Data.Tv_Var bv ->
                        (fun ps1  ->
                           match (on_sort_bv (visit_tm ff) bv)
                                   (FStar_Tactics_Types.incr_depth
                                      (FStar_Tactics_Types.set_proofstate_range
                                         ps1
                                         (FStar_Range.prims_to_fstar_range
                                            (Prims.mk_range
                                               "FStar.Tactics.Derived.fst"
                                               (Prims.of_int (701))
                                               (Prims.of_int (17))
                                               (Prims.of_int (701))
                                               (Prims.of_int (44))))))
                           with
                           | FStar_Tactics_Result.Success (a,ps') ->
                               (match () with
                                | () ->
                                    FStar_Tactics_Result.Success
                                      ((FStar_Reflection_Data.Tv_Var a),
                                        (FStar_Tactics_Types.decr_depth
                                           (FStar_Tactics_Types.set_proofstate_range
                                              ps'
                                              (FStar_Range.prims_to_fstar_range
                                                 (Prims.mk_range
                                                    "FStar.Tactics.Derived.fst"
                                                    (Prims.of_int (702))
                                                    (Prims.of_int (8))
                                                    (Prims.of_int (702))
                                                    (Prims.of_int (17))))))))
                           | FStar_Tactics_Result.Failed (e,ps') ->
                               FStar_Tactics_Result.Failed (e, ps'))
                    | FStar_Reflection_Data.Tv_BVar bv ->
                        (fun ps1  ->
                           match (on_sort_bv (visit_tm ff) bv)
                                   (FStar_Tactics_Types.incr_depth
                                      (FStar_Tactics_Types.set_proofstate_range
                                         ps1
                                         (FStar_Range.prims_to_fstar_range
                                            (Prims.mk_range
                                               "FStar.Tactics.Derived.fst"
                                               (Prims.of_int (705))
                                               (Prims.of_int (17))
                                               (Prims.of_int (705))
                                               (Prims.of_int (44))))))
                           with
                           | FStar_Tactics_Result.Success (a,ps') ->
                               (match () with
                                | () ->
                                    FStar_Tactics_Result.Success
                                      ((FStar_Reflection_Data.Tv_BVar a),
                                        (FStar_Tactics_Types.decr_depth
                                           (FStar_Tactics_Types.set_proofstate_range
                                              ps'
                                              (FStar_Range.prims_to_fstar_range
                                                 (Prims.mk_range
                                                    "FStar.Tactics.Derived.fst"
                                                    (Prims.of_int (706))
                                                    (Prims.of_int (8))
                                                    (Prims.of_int (706))
                                                    (Prims.of_int (18))))))))
                           | FStar_Tactics_Result.Failed (e,ps') ->
                               FStar_Tactics_Result.Failed (e, ps'))
                    | FStar_Reflection_Data.Tv_Type () ->
                        (fun s  ->
                           FStar_Tactics_Result.Success
                             ((FStar_Reflection_Data.Tv_Type ()), s))
                    | FStar_Reflection_Data.Tv_Const c ->
                        (fun s  ->
                           FStar_Tactics_Result.Success
                             ((FStar_Reflection_Data.Tv_Const c), s))
                    | FStar_Reflection_Data.Tv_Uvar (i,u) ->
                        (fun s  ->
                           FStar_Tactics_Result.Success
                             ((FStar_Reflection_Data.Tv_Uvar (i, u)), s))
                    | FStar_Reflection_Data.Tv_Unknown  ->
                        (fun s  ->
                           FStar_Tactics_Result.Success
                             (FStar_Reflection_Data.Tv_Unknown, s))
                    | FStar_Reflection_Data.Tv_Arrow (b,c) ->
                        (fun ps1  ->
                           match (on_sort_binder (visit_tm ff) b)
                                   (FStar_Tactics_Types.incr_depth
                                      (FStar_Tactics_Types.set_proofstate_range
                                         ps1
                                         (FStar_Range.prims_to_fstar_range
                                            (Prims.mk_range
                                               "FStar.Tactics.Derived.fst"
                                               (Prims.of_int (713))
                                               (Prims.of_int (16))
                                               (Prims.of_int (713))
                                               (Prims.of_int (46))))))
                           with
                           | FStar_Tactics_Result.Success (a,ps') ->
                               (match () with
                                | () ->
                                    (match (visit_comp ff c)
                                             (FStar_Tactics_Types.incr_depth
                                                (FStar_Tactics_Types.set_proofstate_range
                                                   (FStar_Tactics_Types.decr_depth
                                                      (FStar_Tactics_Types.set_proofstate_range
                                                         ps'
                                                         (FStar_Range.prims_to_fstar_range
                                                            (Prims.mk_range
                                                               "FStar.Tactics.Derived.fst"
                                                               (Prims.of_int (714))
                                                               (Prims.of_int (8))
                                                               (Prims.of_int (715))
                                                               (Prims.of_int (20))))))
                                                   (FStar_Range.prims_to_fstar_range
                                                      (Prims.mk_range
                                                         "FStar.Tactics.Derived.fst"
                                                         (Prims.of_int (714))
                                                         (Prims.of_int (16))
                                                         (Prims.of_int (714))
                                                         (Prims.of_int (31))))))
                                     with
                                     | FStar_Tactics_Result.Success (a1,ps'1)
                                         ->
                                         (match () with
                                          | () ->
                                              FStar_Tactics_Result.Success
                                                ((FStar_Reflection_Data.Tv_Arrow
                                                    (a, a1)),
                                                  (FStar_Tactics_Types.decr_depth
                                                     (FStar_Tactics_Types.set_proofstate_range
                                                        ps'1
                                                        (FStar_Range.prims_to_fstar_range
                                                           (Prims.mk_range
                                                              "FStar.Tactics.Derived.fst"
                                                              (Prims.of_int (715))
                                                              (Prims.of_int (8))
                                                              (Prims.of_int (715))
                                                              (Prims.of_int (20))))))))
                                     | FStar_Tactics_Result.Failed (e,ps'1)
                                         ->
                                         FStar_Tactics_Result.Failed
                                           (e, ps'1)))
                           | FStar_Tactics_Result.Failed (e,ps') ->
                               FStar_Tactics_Result.Failed (e, ps'))
                    | FStar_Reflection_Data.Tv_Abs (b,t1) ->
                        (fun ps1  ->
                           match (on_sort_binder (visit_tm ff) b)
                                   (FStar_Tactics_Types.incr_depth
                                      (FStar_Tactics_Types.set_proofstate_range
                                         ps1
                                         (FStar_Range.prims_to_fstar_range
                                            (Prims.mk_range
                                               "FStar.Tactics.Derived.fst"
                                               (Prims.of_int (717))
                                               (Prims.of_int (16))
                                               (Prims.of_int (717))
                                               (Prims.of_int (46))))))
                           with
                           | FStar_Tactics_Result.Success (a,ps') ->
                               (match () with
                                | () ->
                                    (match (visit_tm ff t1)
                                             (FStar_Tactics_Types.incr_depth
                                                (FStar_Tactics_Types.set_proofstate_range
                                                   (FStar_Tactics_Types.decr_depth
                                                      (FStar_Tactics_Types.set_proofstate_range
                                                         ps'
                                                         (FStar_Range.prims_to_fstar_range
                                                            (Prims.mk_range
                                                               "FStar.Tactics.Derived.fst"
                                                               (Prims.of_int (718))
                                                               (Prims.of_int (8))
                                                               (Prims.of_int (719))
                                                               (Prims.of_int (18))))))
                                                   (FStar_Range.prims_to_fstar_range
                                                      (Prims.mk_range
                                                         "FStar.Tactics.Derived.fst"
                                                         (Prims.of_int (718))
                                                         (Prims.of_int (16))
                                                         (Prims.of_int (718))
                                                         (Prims.of_int (29))))))
                                     with
                                     | FStar_Tactics_Result.Success (a1,ps'1)
                                         ->
                                         (match () with
                                          | () ->
                                              FStar_Tactics_Result.Success
                                                ((FStar_Reflection_Data.Tv_Abs
                                                    (a, a1)),
                                                  (FStar_Tactics_Types.decr_depth
                                                     (FStar_Tactics_Types.set_proofstate_range
                                                        ps'1
                                                        (FStar_Range.prims_to_fstar_range
                                                           (Prims.mk_range
                                                              "FStar.Tactics.Derived.fst"
                                                              (Prims.of_int (719))
                                                              (Prims.of_int (8))
                                                              (Prims.of_int (719))
                                                              (Prims.of_int (18))))))))
                                     | FStar_Tactics_Result.Failed (e,ps'1)
                                         ->
                                         FStar_Tactics_Result.Failed
                                           (e, ps'1)))
                           | FStar_Tactics_Result.Failed (e,ps') ->
                               FStar_Tactics_Result.Failed (e, ps'))
                    | FStar_Reflection_Data.Tv_App (l,(r,q)) ->
                        (fun ps1  ->
                           match (visit_tm ff l)
                                   (FStar_Tactics_Types.incr_depth
                                      (FStar_Tactics_Types.set_proofstate_range
                                         ps1
                                         (FStar_Range.prims_to_fstar_range
                                            (Prims.mk_range
                                               "FStar.Tactics.Derived.fst"
                                               (Prims.of_int (721))
                                               (Prims.of_int (17))
                                               (Prims.of_int (721))
                                               (Prims.of_int (30))))))
                           with
                           | FStar_Tactics_Result.Success (a,ps') ->
                               (match () with
                                | () ->
                                    (match (visit_tm ff r)
                                             (FStar_Tactics_Types.incr_depth
                                                (FStar_Tactics_Types.set_proofstate_range
                                                   (FStar_Tactics_Types.decr_depth
                                                      (FStar_Tactics_Types.set_proofstate_range
                                                         ps'
                                                         (FStar_Range.prims_to_fstar_range
                                                            (Prims.mk_range
                                                               "FStar.Tactics.Derived.fst"
                                                               (Prims.of_int (722))
                                                               (Prims.of_int (9))
                                                               (Prims.of_int (723))
                                                               (Prims.of_int (24))))))
                                                   (FStar_Range.prims_to_fstar_range
                                                      (Prims.mk_range
                                                         "FStar.Tactics.Derived.fst"
                                                         (Prims.of_int (722))
                                                         (Prims.of_int (17))
                                                         (Prims.of_int (722))
                                                         (Prims.of_int (30))))))
                                     with
                                     | FStar_Tactics_Result.Success (a1,ps'1)
                                         ->
                                         (match () with
                                          | () ->
                                              FStar_Tactics_Result.Success
                                                ((FStar_Reflection_Data.Tv_App
                                                    (a, (a1, q))),
                                                  (FStar_Tactics_Types.decr_depth
                                                     (FStar_Tactics_Types.set_proofstate_range
                                                        ps'1
                                                        (FStar_Range.prims_to_fstar_range
                                                           (Prims.mk_range
                                                              "FStar.Tactics.Derived.fst"
                                                              (Prims.of_int (723))
                                                              (Prims.of_int (9))
                                                              (Prims.of_int (723))
                                                              (Prims.of_int (24))))))))
                                     | FStar_Tactics_Result.Failed (e,ps'1)
                                         ->
                                         FStar_Tactics_Result.Failed
                                           (e, ps'1)))
                           | FStar_Tactics_Result.Failed (e,ps') ->
                               FStar_Tactics_Result.Failed (e, ps'))
                    | FStar_Reflection_Data.Tv_Refine (b,r) ->
                        (fun ps1  ->
                           match (visit_tm ff r)
                                   (FStar_Tactics_Types.incr_depth
                                      (FStar_Tactics_Types.set_proofstate_range
                                         ps1
                                         (FStar_Range.prims_to_fstar_range
                                            (Prims.mk_range
                                               "FStar.Tactics.Derived.fst"
                                               (Prims.of_int (725))
                                               (Prims.of_int (16))
                                               (Prims.of_int (725))
                                               (Prims.of_int (29))))))
                           with
                           | FStar_Tactics_Result.Success (a,ps') ->
                               (match () with
                                | () ->
                                    FStar_Tactics_Result.Success
                                      ((FStar_Reflection_Data.Tv_Refine
                                          (b, a)),
                                        (FStar_Tactics_Types.decr_depth
                                           (FStar_Tactics_Types.set_proofstate_range
                                              ps'
                                              (FStar_Range.prims_to_fstar_range
                                                 (Prims.mk_range
                                                    "FStar.Tactics.Derived.fst"
                                                    (Prims.of_int (726))
                                                    (Prims.of_int (8))
                                                    (Prims.of_int (726))
                                                    (Prims.of_int (21))))))))
                           | FStar_Tactics_Result.Failed (e,ps') ->
                               FStar_Tactics_Result.Failed (e, ps'))
                    | FStar_Reflection_Data.Tv_Let (r,attrs,b,def,t1) ->
                        (fun ps1  ->
                           match (visit_tm ff def)
                                   (FStar_Tactics_Types.incr_depth
                                      (FStar_Tactics_Types.set_proofstate_range
                                         ps1
                                         (FStar_Range.prims_to_fstar_range
                                            (Prims.mk_range
                                               "FStar.Tactics.Derived.fst"
                                               (Prims.of_int (728))
                                               (Prims.of_int (18))
                                               (Prims.of_int (728))
                                               (Prims.of_int (33))))))
                           with
                           | FStar_Tactics_Result.Success (a,ps') ->
                               (match () with
                                | () ->
                                    (match (visit_tm ff t1)
                                             (FStar_Tactics_Types.incr_depth
                                                (FStar_Tactics_Types.set_proofstate_range
                                                   (FStar_Tactics_Types.decr_depth
                                                      (FStar_Tactics_Types.set_proofstate_range
                                                         ps'
                                                         (FStar_Range.prims_to_fstar_range
                                                            (Prims.mk_range
                                                               "FStar.Tactics.Derived.fst"
                                                               (Prims.of_int (729))
                                                               (Prims.of_int (8))
                                                               (Prims.of_int (730))
                                                               (Prims.of_int (30))))))
                                                   (FStar_Range.prims_to_fstar_range
                                                      (Prims.mk_range
                                                         "FStar.Tactics.Derived.fst"
                                                         (Prims.of_int (729))
                                                         (Prims.of_int (16))
                                                         (Prims.of_int (729))
                                                         (Prims.of_int (29))))))
                                     with
                                     | FStar_Tactics_Result.Success (a1,ps'1)
                                         ->
                                         (match () with
                                          | () ->
                                              FStar_Tactics_Result.Success
                                                ((FStar_Reflection_Data.Tv_Let
                                                    (r, attrs, b, a, a1)),
                                                  (FStar_Tactics_Types.decr_depth
                                                     (FStar_Tactics_Types.set_proofstate_range
                                                        ps'1
                                                        (FStar_Range.prims_to_fstar_range
                                                           (Prims.mk_range
                                                              "FStar.Tactics.Derived.fst"
                                                              (Prims.of_int (730))
                                                              (Prims.of_int (8))
                                                              (Prims.of_int (730))
                                                              (Prims.of_int (30))))))))
                                     | FStar_Tactics_Result.Failed (e,ps'1)
                                         ->
                                         FStar_Tactics_Result.Failed
                                           (e, ps'1)))
                           | FStar_Tactics_Result.Failed (e,ps') ->
                               FStar_Tactics_Result.Failed (e, ps'))
                    | FStar_Reflection_Data.Tv_Match (sc,brs) ->
                        (fun ps1  ->
                           match (visit_tm ff sc)
                                   (FStar_Tactics_Types.incr_depth
                                      (FStar_Tactics_Types.set_proofstate_range
                                         ps1
                                         (FStar_Range.prims_to_fstar_range
                                            (Prims.mk_range
                                               "FStar.Tactics.Derived.fst"
                                               (Prims.of_int (732))
                                               (Prims.of_int (17))
                                               (Prims.of_int (732))
                                               (Prims.of_int (31))))))
                           with
                           | FStar_Tactics_Result.Success (a,ps') ->
                               (match () with
                                | () ->
                                    (match (FStar_Tactics_Util.map
                                              (visit_br ff) brs)
                                             (FStar_Tactics_Types.incr_depth
                                                (FStar_Tactics_Types.set_proofstate_range
                                                   (FStar_Tactics_Types.decr_depth
                                                      (FStar_Tactics_Types.set_proofstate_range
                                                         ps'
                                                         (FStar_Range.prims_to_fstar_range
                                                            (Prims.mk_range
                                                               "FStar.Tactics.Derived.fst"
                                                               (Prims.of_int (733))
                                                               (Prims.of_int (8))
                                                               (Prims.of_int (734))
                                                               (Prims.of_int (23))))))
                                                   (FStar_Range.prims_to_fstar_range
                                                      (Prims.mk_range
                                                         "FStar.Tactics.Derived.fst"
                                                         (Prims.of_int (733))
                                                         (Prims.of_int (18))
                                                         (Prims.of_int (733))
                                                         (Prims.of_int (39))))))
                                     with
                                     | FStar_Tactics_Result.Success (a1,ps'1)
                                         ->
                                         (match () with
                                          | () ->
                                              FStar_Tactics_Result.Success
                                                ((FStar_Reflection_Data.Tv_Match
                                                    (a, a1)),
                                                  (FStar_Tactics_Types.decr_depth
                                                     (FStar_Tactics_Types.set_proofstate_range
                                                        ps'1
                                                        (FStar_Range.prims_to_fstar_range
                                                           (Prims.mk_range
                                                              "FStar.Tactics.Derived.fst"
                                                              (Prims.of_int (734))
                                                              (Prims.of_int (8))
                                                              (Prims.of_int (734))
                                                              (Prims.of_int (23))))))))
                                     | FStar_Tactics_Result.Failed (e,ps'1)
                                         ->
                                         FStar_Tactics_Result.Failed
                                           (e, ps'1)))
                           | FStar_Tactics_Result.Failed (e,ps') ->
                               FStar_Tactics_Result.Failed (e, ps'))
                    | FStar_Reflection_Data.Tv_AscribedT (e,t1,topt) ->
                        (fun ps1  ->
                           match (visit_tm ff e)
                                   (FStar_Tactics_Types.incr_depth
                                      (FStar_Tactics_Types.set_proofstate_range
                                         ps1
                                         (FStar_Range.prims_to_fstar_range
                                            (Prims.mk_range
                                               "FStar.Tactics.Derived.fst"
                                               (Prims.of_int (736))
                                               (Prims.of_int (16))
                                               (Prims.of_int (736))
                                               (Prims.of_int (29))))))
                           with
                           | FStar_Tactics_Result.Success (a,ps') ->
                               (match () with
                                | () ->
                                    (match (visit_tm ff t1)
                                             (FStar_Tactics_Types.incr_depth
                                                (FStar_Tactics_Types.set_proofstate_range
                                                   (FStar_Tactics_Types.decr_depth
                                                      (FStar_Tactics_Types.set_proofstate_range
                                                         ps'
                                                         (FStar_Range.prims_to_fstar_range
                                                            (Prims.mk_range
                                                               "FStar.Tactics.Derived.fst"
                                                               (Prims.of_int (737))
                                                               (Prims.of_int (8))
                                                               (Prims.of_int (738))
                                                               (Prims.of_int (29))))))
                                                   (FStar_Range.prims_to_fstar_range
                                                      (Prims.mk_range
                                                         "FStar.Tactics.Derived.fst"
                                                         (Prims.of_int (737))
                                                         (Prims.of_int (16))
                                                         (Prims.of_int (737))
                                                         (Prims.of_int (29))))))
                                     with
                                     | FStar_Tactics_Result.Success (a1,ps'1)
                                         ->
                                         (match () with
                                          | () ->
                                              FStar_Tactics_Result.Success
                                                ((FStar_Reflection_Data.Tv_AscribedT
                                                    (a, a1, topt)),
                                                  (FStar_Tactics_Types.decr_depth
                                                     (FStar_Tactics_Types.set_proofstate_range
                                                        ps'1
                                                        (FStar_Range.prims_to_fstar_range
                                                           (Prims.mk_range
                                                              "FStar.Tactics.Derived.fst"
                                                              (Prims.of_int (738))
                                                              (Prims.of_int (8))
                                                              (Prims.of_int (738))
                                                              (Prims.of_int (29))))))))
                                     | FStar_Tactics_Result.Failed (e1,ps'1)
                                         ->
                                         FStar_Tactics_Result.Failed
                                           (e1, ps'1)))
                           | FStar_Tactics_Result.Failed (e1,ps') ->
                               FStar_Tactics_Result.Failed (e1, ps'))
                    | FStar_Reflection_Data.Tv_AscribedC (e,c,topt) ->
                        (fun ps1  ->
                           match (visit_tm ff e)
                                   (FStar_Tactics_Types.incr_depth
                                      (FStar_Tactics_Types.set_proofstate_range
                                         ps1
                                         (FStar_Range.prims_to_fstar_range
                                            (Prims.mk_range
                                               "FStar.Tactics.Derived.fst"
                                               (Prims.of_int (740))
                                               (Prims.of_int (16))
                                               (Prims.of_int (740))
                                               (Prims.of_int (29))))))
                           with
                           | FStar_Tactics_Result.Success (a,ps') ->
                               (match () with
                                | () ->
                                    FStar_Tactics_Result.Success
                                      ((FStar_Reflection_Data.Tv_AscribedC
                                          (a, c, topt)),
                                        (FStar_Tactics_Types.decr_depth
                                           (FStar_Tactics_Types.set_proofstate_range
                                              ps'
                                              (FStar_Range.prims_to_fstar_range
                                                 (Prims.mk_range
                                                    "FStar.Tactics.Derived.fst"
                                                    (Prims.of_int (741))
                                                    (Prims.of_int (8))
                                                    (Prims.of_int (741))
                                                    (Prims.of_int (29))))))))
                           | FStar_Tactics_Result.Failed (e1,ps') ->
                               FStar_Tactics_Result.Failed (e1, ps')))
                     (FStar_Tactics_Types.incr_depth
                        (FStar_Tactics_Types.set_proofstate_range
                           (FStar_Tactics_Types.decr_depth
                              (FStar_Tactics_Types.set_proofstate_range
                                 (FStar_Tactics_Types.incr_depth
                                    (FStar_Tactics_Types.set_proofstate_range
                                       ps
                                       (FStar_Range.prims_to_fstar_range
                                          (Prims.mk_range
                                             "FStar.Tactics.Derived.fst"
                                             (Prims.of_int (696))
                                             (Prims.of_int (11))
                                             (Prims.of_int (696))
                                             (Prims.of_int (23))))))
                                 (FStar_Range.prims_to_fstar_range
                                    (Prims.mk_range
                                       "FStar.Tactics.Derived.fst"
                                       (Prims.of_int (697))
                                       (Prims.of_int (2))
                                       (Prims.of_int (743))
                                       (Prims.of_int (18))))))
                           (FStar_Range.prims_to_fstar_range
                              (Prims.mk_range "FStar.Tactics.Derived.fst"
                                 (Prims.of_int (698)) (Prims.of_int (4))
                                 (Prims.of_int (741)) (Prims.of_int (29))))))
             with
             | FStar_Tactics_Result.Success (a,ps') ->
                 (match () with
                  | () ->
                      (ff (FStar_Reflection_Basic.pack_ln a))
                        (FStar_Tactics_Types.decr_depth
                           (FStar_Tactics_Types.set_proofstate_range ps'
                              (FStar_Range.prims_to_fstar_range
                                 (Prims.mk_range "FStar.Tactics.Derived.fst"
                                    (Prims.of_int (743)) (Prims.of_int (2))
                                    (Prims.of_int (743)) (Prims.of_int (18)))))))
             | FStar_Tactics_Result.Failed (e,ps') ->
                 FStar_Tactics_Result.Failed (e, ps'))

and (visit_br :
  (FStar_Reflection_Types.term ->
     (FStar_Reflection_Types.term,unit) FStar_Tactics_Effect._dm4f_TAC_repr)
    ->
    FStar_Reflection_Data.branch ->
      (FStar_Reflection_Data.branch,unit) FStar_Tactics_Effect._dm4f_TAC_repr)
  =
  fun ff  ->
    fun b  ->
      fun ps  ->
        match () with
        | () ->
            ((match b with
              | (p,t) ->
                  (fun ps1  ->
                     match (visit_tm ff t)
                             (FStar_Tactics_Types.incr_depth
                                (FStar_Tactics_Types.set_proofstate_range ps1
                                   (FStar_Range.prims_to_fstar_range
                                      (Prims.mk_range
                                         "FStar.Tactics.Derived.fst"
                                         (Prims.of_int (746))
                                         (Prims.of_int (6))
                                         (Prims.of_int (746))
                                         (Prims.of_int (19))))))
                     with
                     | FStar_Tactics_Result.Success (a,ps') ->
                         (match () with
                          | () ->
                              FStar_Tactics_Result.Success
                                ((p, a),
                                  (FStar_Tactics_Types.decr_depth
                                     (FStar_Tactics_Types.set_proofstate_range
                                        ps'
                                        (FStar_Range.prims_to_fstar_range
                                           (Prims.mk_range
                                              "FStar.Tactics.Derived.fst"
                                              (Prims.of_int (746))
                                              (Prims.of_int (2))
                                              (Prims.of_int (746))
                                              (Prims.of_int (20))))))))
                     | FStar_Tactics_Result.Failed (e,ps') ->
                         FStar_Tactics_Result.Failed (e, ps'))))
              (FStar_Tactics_Types.decr_depth
                 (FStar_Tactics_Types.set_proofstate_range
                    (FStar_Tactics_Types.incr_depth
                       (FStar_Tactics_Types.set_proofstate_range ps
                          (FStar_Range.prims_to_fstar_range
                             (Prims.mk_range "FStar.Tactics.Derived.fst"
                                (Prims.of_int (745)) (Prims.of_int (15))
                                (Prims.of_int (745)) (Prims.of_int (16))))))
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.Derived.fst"
                          (Prims.of_int (745)) (Prims.of_int (2))
                          (Prims.of_int (746)) (Prims.of_int (20))))))

and (visit_comp :
  (FStar_Reflection_Types.term ->
     (FStar_Reflection_Types.term,unit) FStar_Tactics_Effect._dm4f_TAC_repr)
    ->
    FStar_Reflection_Types.comp ->
      (FStar_Reflection_Types.comp,unit) FStar_Tactics_Effect._dm4f_TAC_repr)
  =
  fun ff  ->
    fun c  ->
      fun ps  ->
        match () with
        | () ->
            (match (match FStar_Reflection_Basic.inspect_comp c with
                    | FStar_Reflection_Data.C_Total (ret,decr1) ->
                        (fun ps1  ->
                           match (visit_tm ff ret)
                                   (FStar_Tactics_Types.incr_depth
                                      (FStar_Tactics_Types.set_proofstate_range
                                         ps1
                                         (FStar_Range.prims_to_fstar_range
                                            (Prims.mk_range
                                               "FStar.Tactics.Derived.fst"
                                               (Prims.of_int (752))
                                               (Prims.of_int (18))
                                               (Prims.of_int (752))
                                               (Prims.of_int (33))))))
                           with
                           | FStar_Tactics_Result.Success (a,ps') ->
                               (match () with
                                | () ->
                                    (match (match decr1 with
                                            | FStar_Pervasives_Native.None 
                                                ->
                                                (fun s  ->
                                                   FStar_Tactics_Result.Success
                                                     (FStar_Pervasives_Native.None,
                                                       s))
                                            | FStar_Pervasives_Native.Some d
                                                ->
                                                (fun ps2  ->
                                                   match (visit_tm ff d)
                                                           (FStar_Tactics_Types.incr_depth
                                                              (FStar_Tactics_Types.set_proofstate_range
                                                                 ps2
                                                                 (FStar_Range.prims_to_fstar_range
                                                                    (
                                                                    Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (756))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (756))
                                                                    (Prims.of_int (44))))))
                                                   with
                                                   | FStar_Tactics_Result.Success
                                                       (a1,ps'1) ->
                                                       (match () with
                                                        | () ->
                                                            FStar_Tactics_Result.Success
                                                              ((FStar_Pervasives_Native.Some
                                                                  a1),
                                                                (FStar_Tactics_Types.decr_depth
                                                                   (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'1
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Derived.fst"
                                                                    (Prims.of_int (756))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (756))
                                                                    (Prims.of_int (44))))))))
                                                   | FStar_Tactics_Result.Failed
                                                       (e,ps'1) ->
                                                       FStar_Tactics_Result.Failed
                                                         (e, ps'1)))
                                             (FStar_Tactics_Types.incr_depth
                                                (FStar_Tactics_Types.set_proofstate_range
                                                   (FStar_Tactics_Types.decr_depth
                                                      (FStar_Tactics_Types.set_proofstate_range
                                                         ps'
                                                         (FStar_Range.prims_to_fstar_range
                                                            (Prims.mk_range
                                                               "FStar.Tactics.Derived.fst"
                                                               (Prims.of_int (753))
                                                               (Prims.of_int (8))
                                                               (Prims.of_int (758))
                                                               (Prims.of_int (24))))))
                                                   (FStar_Range.prims_to_fstar_range
                                                      (Prims.mk_range
                                                         "FStar.Tactics.Derived.fst"
                                                         (Prims.of_int (754))
                                                         (Prims.of_int (12))
                                                         (Prims.of_int (756))
                                                         (Prims.of_int (44))))))
                                     with
                                     | FStar_Tactics_Result.Success (a1,ps'1)
                                         ->
                                         (match () with
                                          | () ->
                                              FStar_Tactics_Result.Success
                                                ((FStar_Reflection_Data.C_Total
                                                    (a, a1)),
                                                  (FStar_Tactics_Types.decr_depth
                                                     (FStar_Tactics_Types.set_proofstate_range
                                                        ps'1
                                                        (FStar_Range.prims_to_fstar_range
                                                           (Prims.mk_range
                                                              "FStar.Tactics.Derived.fst"
                                                              (Prims.of_int (758))
                                                              (Prims.of_int (8))
                                                              (Prims.of_int (758))
                                                              (Prims.of_int (24))))))))
                                     | FStar_Tactics_Result.Failed (e,ps'1)
                                         ->
                                         FStar_Tactics_Result.Failed
                                           (e, ps'1)))
                           | FStar_Tactics_Result.Failed (e,ps') ->
                               FStar_Tactics_Result.Failed (e, ps'))
                    | FStar_Reflection_Data.C_Lemma (pre,post) ->
                        (fun ps1  ->
                           match (visit_tm ff pre)
                                   (FStar_Tactics_Types.incr_depth
                                      (FStar_Tactics_Types.set_proofstate_range
                                         ps1
                                         (FStar_Range.prims_to_fstar_range
                                            (Prims.mk_range
                                               "FStar.Tactics.Derived.fst"
                                               (Prims.of_int (760))
                                               (Prims.of_int (18))
                                               (Prims.of_int (760))
                                               (Prims.of_int (33))))))
                           with
                           | FStar_Tactics_Result.Success (a,ps') ->
                               (match () with
                                | () ->
                                    (match (visit_tm ff post)
                                             (FStar_Tactics_Types.incr_depth
                                                (FStar_Tactics_Types.set_proofstate_range
                                                   (FStar_Tactics_Types.decr_depth
                                                      (FStar_Tactics_Types.set_proofstate_range
                                                         ps'
                                                         (FStar_Range.prims_to_fstar_range
                                                            (Prims.mk_range
                                                               "FStar.Tactics.Derived.fst"
                                                               (Prims.of_int (761))
                                                               (Prims.of_int (8))
                                                               (Prims.of_int (762))
                                                               (Prims.of_int (24))))))
                                                   (FStar_Range.prims_to_fstar_range
                                                      (Prims.mk_range
                                                         "FStar.Tactics.Derived.fst"
                                                         (Prims.of_int (761))
                                                         (Prims.of_int (19))
                                                         (Prims.of_int (761))
                                                         (Prims.of_int (35))))))
                                     with
                                     | FStar_Tactics_Result.Success (a1,ps'1)
                                         ->
                                         (match () with
                                          | () ->
                                              FStar_Tactics_Result.Success
                                                ((FStar_Reflection_Data.C_Lemma
                                                    (a, a1)),
                                                  (FStar_Tactics_Types.decr_depth
                                                     (FStar_Tactics_Types.set_proofstate_range
                                                        ps'1
                                                        (FStar_Range.prims_to_fstar_range
                                                           (Prims.mk_range
                                                              "FStar.Tactics.Derived.fst"
                                                              (Prims.of_int (762))
                                                              (Prims.of_int (8))
                                                              (Prims.of_int (762))
                                                              (Prims.of_int (24))))))))
                                     | FStar_Tactics_Result.Failed (e,ps'1)
                                         ->
                                         FStar_Tactics_Result.Failed
                                           (e, ps'1)))
                           | FStar_Tactics_Result.Failed (e,ps') ->
                               FStar_Tactics_Result.Failed (e, ps'))
                    | FStar_Reflection_Data.C_Unknown  ->
                        (fun s  ->
                           FStar_Tactics_Result.Success
                             (FStar_Reflection_Data.C_Unknown, s)))
                     (FStar_Tactics_Types.incr_depth
                        (FStar_Tactics_Types.set_proofstate_range
                           (FStar_Tactics_Types.decr_depth
                              (FStar_Tactics_Types.set_proofstate_range
                                 (FStar_Tactics_Types.incr_depth
                                    (FStar_Tactics_Types.set_proofstate_range
                                       ps
                                       (FStar_Range.prims_to_fstar_range
                                          (Prims.mk_range
                                             "FStar.Tactics.Derived.fst"
                                             (Prims.of_int (748))
                                             (Prims.of_int (11))
                                             (Prims.of_int (748))
                                             (Prims.of_int (25))))))
                                 (FStar_Range.prims_to_fstar_range
                                    (Prims.mk_range
                                       "FStar.Tactics.Derived.fst"
                                       (Prims.of_int (749))
                                       (Prims.of_int (2))
                                       (Prims.of_int (765))
                                       (Prims.of_int (15))))))
                           (FStar_Range.prims_to_fstar_range
                              (Prims.mk_range "FStar.Tactics.Derived.fst"
                                 (Prims.of_int (750)) (Prims.of_int (4))
                                 (Prims.of_int (763)) (Prims.of_int (28))))))
             with
             | FStar_Tactics_Result.Success (a,ps') ->
                 (match () with
                  | () ->
                      FStar_Tactics_Result.Success
                        ((FStar_Reflection_Basic.pack_comp a),
                          (FStar_Tactics_Types.decr_depth
                             (FStar_Tactics_Types.set_proofstate_range ps'
                                (FStar_Range.prims_to_fstar_range
                                   (Prims.mk_range
                                      "FStar.Tactics.Derived.fst"
                                      (Prims.of_int (765)) (Prims.of_int (2))
                                      (Prims.of_int (765))
                                      (Prims.of_int (15))))))))
             | FStar_Tactics_Result.Failed (e,ps') ->
                 FStar_Tactics_Result.Failed (e, ps'))

exception NotAListLiteral 
let (uu___is_NotAListLiteral : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | NotAListLiteral  -> true | uu____17147 -> false
  
let rec (destruct_list :
  FStar_Reflection_Types.term ->
    (FStar_Reflection_Types.term Prims.list,unit)
      FStar_Tactics_Effect._dm4f_TAC_repr)
  =
  fun t  ->
    fun ps  ->
      match () with
      | () ->
          ((match FStar_Reflection_Derived.collect_app t with
            | (head1,args) ->
                (match ((FStar_Reflection_Basic.inspect_ln head1), args) with
                 | (FStar_Reflection_Data.Tv_FVar
                    fv,(a1,FStar_Reflection_Data.Q_Explicit )::(a2,FStar_Reflection_Data.Q_Explicit
                                                                )::[])
                     ->
                     if
                       (FStar_Reflection_Basic.inspect_fv fv) =
                         FStar_Reflection_Const.cons_qn
                     then
                       (fun ps1  ->
                          match (destruct_list a2)
                                  (FStar_Tactics_Types.incr_depth
                                     (FStar_Tactics_Types.set_proofstate_range
                                        ps1
                                        (FStar_Range.prims_to_fstar_range
                                           (Prims.mk_range
                                              "FStar.Tactics.Derived.fst"
                                              (Prims.of_int (775))
                                              (Prims.of_int (17))
                                              (Prims.of_int (775))
                                              (Prims.of_int (33))))))
                          with
                          | FStar_Tactics_Result.Success (a,ps') ->
                              (match () with
                               | () ->
                                   FStar_Tactics_Result.Success
                                     ((a1 :: a),
                                       (FStar_Tactics_Types.decr_depth
                                          (FStar_Tactics_Types.set_proofstate_range
                                             ps'
                                             (FStar_Range.prims_to_fstar_range
                                                (Prims.mk_range
                                                   "FStar.Tactics.Derived.fst"
                                                   (Prims.of_int (775))
                                                   (Prims.of_int (14))
                                                   (Prims.of_int (775))
                                                   (Prims.of_int (16))))))))
                          | FStar_Tactics_Result.Failed (e,ps') ->
                              FStar_Tactics_Result.Failed (e, ps'))
                     else FStar_Tactics_Effect.raise NotAListLiteral
                 | (FStar_Reflection_Data.Tv_FVar
                    fv,(uu____17461,FStar_Reflection_Data.Q_Implicit )::
                    (a1,FStar_Reflection_Data.Q_Explicit )::(a2,FStar_Reflection_Data.Q_Explicit
                                                             )::[])
                     ->
                     if
                       (FStar_Reflection_Basic.inspect_fv fv) =
                         FStar_Reflection_Const.cons_qn
                     then
                       (fun ps1  ->
                          match (destruct_list a2)
                                  (FStar_Tactics_Types.incr_depth
                                     (FStar_Tactics_Types.set_proofstate_range
                                        ps1
                                        (FStar_Range.prims_to_fstar_range
                                           (Prims.mk_range
                                              "FStar.Tactics.Derived.fst"
                                              (Prims.of_int (775))
                                              (Prims.of_int (17))
                                              (Prims.of_int (775))
                                              (Prims.of_int (33))))))
                          with
                          | FStar_Tactics_Result.Success (a,ps') ->
                              (match () with
                               | () ->
                                   FStar_Tactics_Result.Success
                                     ((a1 :: a),
                                       (FStar_Tactics_Types.decr_depth
                                          (FStar_Tactics_Types.set_proofstate_range
                                             ps'
                                             (FStar_Range.prims_to_fstar_range
                                                (Prims.mk_range
                                                   "FStar.Tactics.Derived.fst"
                                                   (Prims.of_int (775))
                                                   (Prims.of_int (14))
                                                   (Prims.of_int (775))
                                                   (Prims.of_int (16))))))))
                          | FStar_Tactics_Result.Failed (e,ps') ->
                              FStar_Tactics_Result.Failed (e, ps'))
                     else FStar_Tactics_Effect.raise NotAListLiteral
                 | (FStar_Reflection_Data.Tv_FVar fv,uu____17536) ->
                     if
                       (FStar_Reflection_Basic.inspect_fv fv) =
                         FStar_Reflection_Const.nil_qn
                     then (fun s  -> FStar_Tactics_Result.Success ([], s))
                     else FStar_Tactics_Effect.raise NotAListLiteral
                 | uu____17564 -> FStar_Tactics_Effect.raise NotAListLiteral)))
            (FStar_Tactics_Types.decr_depth
               (FStar_Tactics_Types.set_proofstate_range
                  (FStar_Tactics_Types.incr_depth
                     (FStar_Tactics_Types.set_proofstate_range ps
                        (FStar_Range.prims_to_fstar_range
                           (Prims.mk_range "FStar.Tactics.Derived.fst"
                              (Prims.of_int (770)) (Prims.of_int (21))
                              (Prims.of_int (770)) (Prims.of_int (34))))))
                  (FStar_Range.prims_to_fstar_range
                     (Prims.mk_range "FStar.Tactics.Derived.fst"
                        (Prims.of_int (770)) (Prims.of_int (4))
                        (Prims.of_int (782)) (Prims.of_int (27))))))
  