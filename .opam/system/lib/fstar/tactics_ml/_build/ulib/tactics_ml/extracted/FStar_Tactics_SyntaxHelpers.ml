open Prims
let rec (collect_arr' :
  FStar_Reflection_Types.binder Prims.list ->
    FStar_Reflection_Types.comp ->
      ((FStar_Reflection_Types.binder Prims.list *
         FStar_Reflection_Types.comp),unit)
        FStar_Tactics_Effect._dm4f_TAC_repr)
  =
  fun bs  ->
    fun c  ->
      match FStar_Reflection_Basic.inspect_comp c with
      | FStar_Reflection_Data.C_Total (t,uu____104) ->
          (fun ps  ->
             match (FStar_Tactics_Builtins.inspect t)
                     (FStar_Tactics_Types.incr_depth
                        (FStar_Tactics_Types.set_proofstate_range ps
                           (FStar_Range.prims_to_fstar_range
                              (Prims.mk_range
                                 "FStar.Tactics.SyntaxHelpers.fst"
                                 (Prims.of_int (13)) (Prims.of_int (20))
                                 (Prims.of_int (13)) (Prims.of_int (29))))))
             with
             | FStar_Tactics_Result.Success (a,ps') ->
                 (match () with
                  | () ->
                      ((match a with
                        | FStar_Reflection_Data.Tv_Arrow (b,c1) ->
                            collect_arr' (b :: bs) c1
                        | uu____148 ->
                            (fun s  ->
                               FStar_Tactics_Result.Success ((bs, c), s))))
                        (FStar_Tactics_Types.decr_depth
                           (FStar_Tactics_Types.set_proofstate_range ps'
                              (FStar_Range.prims_to_fstar_range
                                 (Prims.mk_range
                                    "FStar.Tactics.SyntaxHelpers.fst"
                                    (Prims.of_int (13)) (Prims.of_int (14))
                                    (Prims.of_int (17)) (Prims.of_int (19)))))))
             | FStar_Tactics_Result.Failed (e,ps') ->
                 FStar_Tactics_Result.Failed (e, ps'))
      | uu____174 -> (fun s  -> FStar_Tactics_Result.Success ((bs, c), s))
  
let (collect_arr_bs :
  FStar_Reflection_Types.typ ->
    ((FStar_Reflection_Types.binder Prims.list * FStar_Reflection_Types.comp),
      unit) FStar_Tactics_Effect._dm4f_TAC_repr)
  =
  fun t  ->
    fun ps  ->
      match (collect_arr' []
               (FStar_Reflection_Basic.pack_comp
                  (FStar_Reflection_Data.C_Total
                     (t, FStar_Pervasives_Native.None))))
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.SyntaxHelpers.fst"
                          (Prims.of_int (24)) (Prims.of_int (18))
                          (Prims.of_int (24)) (Prims.of_int (62))))))
      with
      | FStar_Tactics_Result.Success (a,ps') ->
          (match () with
           | () ->
               FStar_Tactics_Result.Success
                 (((match a with
                    | (bs,c) -> ((FStar_List_Tot_Base.rev bs), c))),
                   (FStar_Tactics_Types.decr_depth
                      (FStar_Tactics_Types.set_proofstate_range ps'
                         (FStar_Range.prims_to_fstar_range
                            (Prims.mk_range "FStar.Tactics.SyntaxHelpers.fst"
                               (Prims.of_int (24)) (Prims.of_int (4))
                               (Prims.of_int (25)) (Prims.of_int (24))))))))
      | FStar_Tactics_Result.Failed (e,ps') ->
          FStar_Tactics_Result.Failed (e, ps')
  
let (collect_arr :
  FStar_Reflection_Types.typ ->
    ((FStar_Reflection_Types.typ Prims.list * FStar_Reflection_Types.comp),
      unit) FStar_Tactics_Effect._dm4f_TAC_repr)
  =
  fun t  ->
    fun ps  ->
      match (collect_arr' []
               (FStar_Reflection_Basic.pack_comp
                  (FStar_Reflection_Data.C_Total
                     (t, FStar_Pervasives_Native.None))))
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.SyntaxHelpers.fst"
                          (Prims.of_int (29)) (Prims.of_int (18))
                          (Prims.of_int (29)) (Prims.of_int (62))))))
      with
      | FStar_Tactics_Result.Success (a,ps') ->
          (match () with
           | () ->
               FStar_Tactics_Result.Success
                 (((match a with
                    | (bs,c) ->
                        ((FStar_List_Tot_Base.rev
                            (FStar_List_Tot_Base.map
                               FStar_Reflection_Derived.type_of_binder bs)),
                          c))),
                   (FStar_Tactics_Types.decr_depth
                      (FStar_Tactics_Types.set_proofstate_range ps'
                         (FStar_Range.prims_to_fstar_range
                            (Prims.mk_range "FStar.Tactics.SyntaxHelpers.fst"
                               (Prims.of_int (29)) (Prims.of_int (4))
                               (Prims.of_int (31)) (Prims.of_int (24))))))))
      | FStar_Tactics_Result.Failed (e,ps') ->
          FStar_Tactics_Result.Failed (e, ps')
  
let rec (collect_abs' :
  FStar_Reflection_Types.binder Prims.list ->
    FStar_Reflection_Types.term ->
      ((FStar_Reflection_Types.binder Prims.list *
         FStar_Reflection_Types.term),unit)
        FStar_Tactics_Effect._dm4f_TAC_repr)
  =
  fun bs  ->
    fun t  ->
      fun ps  ->
        match (FStar_Tactics_Builtins.inspect t)
                (FStar_Tactics_Types.incr_depth
                   (FStar_Tactics_Types.set_proofstate_range ps
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range "FStar.Tactics.SyntaxHelpers.fst"
                            (Prims.of_int (35)) (Prims.of_int (10))
                            (Prims.of_int (35)) (Prims.of_int (19))))))
        with
        | FStar_Tactics_Result.Success (a,ps') ->
            (match () with
             | () ->
                 ((match a with
                   | FStar_Reflection_Data.Tv_Abs (b,t') ->
                       collect_abs' (b :: bs) t'
                   | uu____642 ->
                       (fun s  -> FStar_Tactics_Result.Success ((bs, t), s))))
                   (FStar_Tactics_Types.decr_depth
                      (FStar_Tactics_Types.set_proofstate_range ps'
                         (FStar_Range.prims_to_fstar_range
                            (Prims.mk_range "FStar.Tactics.SyntaxHelpers.fst"
                               (Prims.of_int (35)) (Prims.of_int (4))
                               (Prims.of_int (38)) (Prims.of_int (18)))))))
        | FStar_Tactics_Result.Failed (e,ps') ->
            FStar_Tactics_Result.Failed (e, ps')
  
let (collect_abs :
  FStar_Reflection_Types.term ->
    ((FStar_Reflection_Types.binder Prims.list * FStar_Reflection_Types.term),
      unit) FStar_Tactics_Effect._dm4f_TAC_repr)
  =
  fun t  ->
    fun ps  ->
      match (collect_abs' [] t)
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.SyntaxHelpers.fst"
                          (Prims.of_int (42)) (Prims.of_int (19))
                          (Prims.of_int (42)) (Prims.of_int (36))))))
      with
      | FStar_Tactics_Result.Success (a,ps') ->
          (match () with
           | () ->
               FStar_Tactics_Result.Success
                 (((match a with
                    | (bs,t') -> ((FStar_List_Tot_Base.rev bs), t'))),
                   (FStar_Tactics_Types.decr_depth
                      (FStar_Tactics_Types.set_proofstate_range ps'
                         (FStar_Range.prims_to_fstar_range
                            (Prims.mk_range "FStar.Tactics.SyntaxHelpers.fst"
                               (Prims.of_int (42)) (Prims.of_int (4))
                               (Prims.of_int (43)) (Prims.of_int (25))))))))
      | FStar_Tactics_Result.Failed (e,ps') ->
          FStar_Tactics_Result.Failed (e, ps')
  
let rec (mk_tot_arr :
  FStar_Reflection_Types.binder Prims.list ->
    FStar_Reflection_Types.term ->
      (FStar_Reflection_Types.term,unit) FStar_Tactics_Effect._dm4f_TAC_repr)
  =
  fun bs  ->
    fun cod  ->
      match bs with
      | [] -> (fun s  -> FStar_Tactics_Result.Success (cod, s))
      | b::bs1 ->
          (fun ps  ->
             match match match match (mk_tot_arr bs1 cod)
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
                                                                  (Prims.mk_range
                                                                    "FStar.Tactics.SyntaxHelpers.fst"
                                                                    (Prims.of_int (48))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (48))
                                                                    (Prims.of_int (81))))))
                                                         (FStar_Range.prims_to_fstar_range
                                                            (Prims.mk_range
                                                               "FStar.Tactics.SyntaxHelpers.fst"
                                                               (Prims.of_int (48))
                                                               (Prims.of_int (34))
                                                               (Prims.of_int (48))
                                                               (Prims.of_int (80))))))
                                                   (FStar_Range.prims_to_fstar_range
                                                      (Prims.mk_range
                                                         "FStar.Tactics.SyntaxHelpers.fst"
                                                         (Prims.of_int (48))
                                                         (Prims.of_int (45))
                                                         (Prims.of_int (48))
                                                         (Prims.of_int (79))))))
                                             (FStar_Range.prims_to_fstar_range
                                                (Prims.mk_range
                                                   "FStar.Tactics.SyntaxHelpers.fst"
                                                   (Prims.of_int (48))
                                                   (Prims.of_int (54))
                                                   (Prims.of_int (48))
                                                   (Prims.of_int (73))))))
                               with
                               | FStar_Tactics_Result.Success (a,ps') ->
                                   (match () with
                                    | () ->
                                        FStar_Tactics_Result.Success
                                          ((FStar_Reflection_Data.C_Total
                                              (a,
                                                FStar_Pervasives_Native.None)),
                                            (FStar_Tactics_Types.decr_depth
                                               (FStar_Tactics_Types.set_proofstate_range
                                                  ps'
                                                  (FStar_Range.prims_to_fstar_range
                                                     (Prims.mk_range
                                                        "FStar.Tactics.SyntaxHelpers.fst"
                                                        (Prims.of_int (48))
                                                        (Prims.of_int (45))
                                                        (Prims.of_int (48))
                                                        (Prims.of_int (79))))))))
                               | FStar_Tactics_Result.Failed (e,ps') ->
                                   FStar_Tactics_Result.Failed (e, ps')
                         with
                         | FStar_Tactics_Result.Success (a,ps') ->
                             (match () with
                              | () ->
                                  FStar_Tactics_Result.Success
                                    ((FStar_Reflection_Basic.pack_comp a),
                                      (FStar_Tactics_Types.decr_depth
                                         (FStar_Tactics_Types.set_proofstate_range
                                            ps'
                                            (FStar_Range.prims_to_fstar_range
                                               (Prims.mk_range
                                                  "FStar.Tactics.SyntaxHelpers.fst"
                                                  (Prims.of_int (48))
                                                  (Prims.of_int (34))
                                                  (Prims.of_int (48))
                                                  (Prims.of_int (80))))))))
                         | FStar_Tactics_Result.Failed (e,ps') ->
                             FStar_Tactics_Result.Failed (e, ps')
                   with
                   | FStar_Tactics_Result.Success (a,ps') ->
                       (match () with
                        | () ->
                            FStar_Tactics_Result.Success
                              ((FStar_Reflection_Data.Tv_Arrow (b, a)),
                                (FStar_Tactics_Types.decr_depth
                                   (FStar_Tactics_Types.set_proofstate_range
                                      ps'
                                      (FStar_Range.prims_to_fstar_range
                                         (Prims.mk_range
                                            "FStar.Tactics.SyntaxHelpers.fst"
                                            (Prims.of_int (48))
                                            (Prims.of_int (22))
                                            (Prims.of_int (48))
                                            (Prims.of_int (81))))))))
                   | FStar_Tactics_Result.Failed (e,ps') ->
                       FStar_Tactics_Result.Failed (e, ps')
             with
             | FStar_Tactics_Result.Success (a,ps') ->
                 (match () with
                  | () ->
                      (FStar_Tactics_Builtins.pack a)
                        (FStar_Tactics_Types.decr_depth
                           (FStar_Tactics_Types.set_proofstate_range ps'
                              (FStar_Range.prims_to_fstar_range
                                 (Prims.mk_range
                                    "FStar.Tactics.SyntaxHelpers.fst"
                                    (Prims.of_int (48)) (Prims.of_int (17))
                                    (Prims.of_int (48)) (Prims.of_int (81)))))))
             | FStar_Tactics_Result.Failed (e,ps') ->
                 FStar_Tactics_Result.Failed (e, ps'))
  