open Prims
let (cur_formula :
  unit ->
    (FStar_Reflection_Formula.formula,unit)
      FStar_Tactics_Effect._dm4f_TAC_repr)
  =
  fun uu____22  ->
    fun ps  ->
      match (FStar_Tactics_Derived.cur_goal ())
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.Logic.fst"
                          (Prims.of_int (25)) (Prims.of_int (51))
                          (Prims.of_int (25)) (Prims.of_int (64))))))
      with
      | FStar_Tactics_Result.Success (a,ps') ->
          (match () with
           | () ->
               (FStar_Reflection_Formula.term_as_formula a)
                 (FStar_Tactics_Types.decr_depth
                    (FStar_Tactics_Types.set_proofstate_range ps'
                       (FStar_Range.prims_to_fstar_range
                          (Prims.mk_range "FStar.Tactics.Logic.fst"
                             (Prims.of_int (25)) (Prims.of_int (35))
                             (Prims.of_int (25)) (Prims.of_int (64)))))))
      | FStar_Tactics_Result.Failed (e,ps') ->
          FStar_Tactics_Result.Failed (e, ps')
  

let (l_revert : unit -> (unit,unit) FStar_Tactics_Effect._dm4f_TAC_repr) =
  fun uu____95  ->
    fun ps  ->
      match (FStar_Tactics_Builtins.revert ())
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.Logic.fst"
                          (Prims.of_int (33)) (Prims.of_int (4))
                          (Prims.of_int (33)) (Prims.of_int (13))))))
      with
      | FStar_Tactics_Result.Success (a,ps') ->
          (match () with
           | () ->
               (FStar_Tactics_Derived.apply
                  (FStar_Reflection_Basic.pack_ln
                     (FStar_Reflection_Data.Tv_FVar
                        (FStar_Reflection_Basic.pack_fv
                           ["FStar"; "Tactics"; "Logic"; "revert_squash"]))))
                 (FStar_Tactics_Types.decr_depth
                    (FStar_Tactics_Types.set_proofstate_range ps'
                       (FStar_Range.prims_to_fstar_range
                          (Prims.mk_range "FStar.Tactics.Logic.fst"
                             (Prims.of_int (34)) (Prims.of_int (4))
                             (Prims.of_int (34)) (Prims.of_int (26)))))))
      | FStar_Tactics_Result.Failed (e,ps') ->
          FStar_Tactics_Result.Failed (e, ps')
  
let rec (l_revert_all :
  FStar_Reflection_Types.binders ->
    (unit,unit) FStar_Tactics_Effect._dm4f_TAC_repr)
  =
  fun bs  ->
    match bs with
    | [] -> (fun s  -> FStar_Tactics_Result.Success ((), s))
    | uu____210::tl1 ->
        (fun ps  ->
           match (l_revert ())
                   (FStar_Tactics_Types.incr_depth
                      (FStar_Tactics_Types.set_proofstate_range ps
                         (FStar_Range.prims_to_fstar_range
                            (Prims.mk_range "FStar.Tactics.Logic.fst"
                               (Prims.of_int (39)) (Prims.of_int (21))
                               (Prims.of_int (39)) (Prims.of_int (32))))))
           with
           | FStar_Tactics_Result.Success (a,ps') ->
               (match () with
                | () ->
                    (l_revert_all tl1)
                      (FStar_Tactics_Types.decr_depth
                         (FStar_Tactics_Types.set_proofstate_range ps'
                            (FStar_Range.prims_to_fstar_range
                               (Prims.mk_range "FStar.Tactics.Logic.fst"
                                  (Prims.of_int (39)) (Prims.of_int (34))
                                  (Prims.of_int (39)) (Prims.of_int (49)))))))
           | FStar_Tactics_Result.Failed (e,ps') ->
               FStar_Tactics_Result.Failed (e, ps'))
  

let (forall_intro :
  unit ->
    (FStar_Reflection_Types.binder,unit) FStar_Tactics_Effect._dm4f_TAC_repr)
  =
  fun uu____266  ->
    fun ps  ->
      match (FStar_Tactics_Builtins.apply_lemma
               (FStar_Reflection_Basic.pack_ln
                  (FStar_Reflection_Data.Tv_FVar
                     (FStar_Reflection_Basic.pack_fv
                        ["FStar"; "Tactics"; "Logic"; "fa_intro_lem"]))))
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.Logic.fst"
                          (Prims.of_int (47)) (Prims.of_int (4))
                          (Prims.of_int (47)) (Prims.of_int (31))))))
      with
      | FStar_Tactics_Result.Success (a,ps') ->
          (match () with
           | () ->
               (FStar_Tactics_Builtins.intro ())
                 (FStar_Tactics_Types.decr_depth
                    (FStar_Tactics_Types.set_proofstate_range ps'
                       (FStar_Range.prims_to_fstar_range
                          (Prims.mk_range "FStar.Tactics.Logic.fst"
                             (Prims.of_int (48)) (Prims.of_int (4))
                             (Prims.of_int (48)) (Prims.of_int (12)))))))
      | FStar_Tactics_Result.Failed (e,ps') ->
          FStar_Tactics_Result.Failed (e, ps')
  
let (forall_intro_as :
  Prims.string ->
    (FStar_Reflection_Types.binder,unit) FStar_Tactics_Effect._dm4f_TAC_repr)
  =
  fun s  ->
    fun ps  ->
      match (FStar_Tactics_Builtins.apply_lemma
               (FStar_Reflection_Basic.pack_ln
                  (FStar_Reflection_Data.Tv_FVar
                     (FStar_Reflection_Basic.pack_fv
                        ["FStar"; "Tactics"; "Logic"; "fa_intro_lem"]))))
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.Logic.fst"
                          (Prims.of_int (51)) (Prims.of_int (4))
                          (Prims.of_int (51)) (Prims.of_int (31))))))
      with
      | FStar_Tactics_Result.Success (a,ps') ->
          (match () with
           | () ->
               (FStar_Tactics_Derived.intro_as s)
                 (FStar_Tactics_Types.decr_depth
                    (FStar_Tactics_Types.set_proofstate_range ps'
                       (FStar_Range.prims_to_fstar_range
                          (Prims.mk_range "FStar.Tactics.Logic.fst"
                             (Prims.of_int (52)) (Prims.of_int (4))
                             (Prims.of_int (52)) (Prims.of_int (14)))))))
      | FStar_Tactics_Result.Failed (e,ps') ->
          FStar_Tactics_Result.Failed (e, ps')
  
let (forall_intros :
  unit ->
    (FStar_Reflection_Types.binders,unit) FStar_Tactics_Effect._dm4f_TAC_repr)
  = fun uu____419  -> FStar_Tactics_Derived.repeat1 forall_intro 

let (split : unit -> (unit,unit) FStar_Tactics_Effect._dm4f_TAC_repr) =
  fun uu____449  ->
    FStar_Tactics_Derived.try_with
      (fun uu___44_457  ->
         match () with
         | () ->
             FStar_Tactics_Builtins.apply_lemma
               (FStar_Reflection_Basic.pack_ln
                  (FStar_Reflection_Data.Tv_FVar
                     (FStar_Reflection_Basic.pack_fv
                        ["FStar"; "Tactics"; "Logic"; "split_lem"]))))
      (fun uu___43_468  -> FStar_Tactics_Derived.fail "Could not split goal")
  

let (implies_intro :
  unit ->
    (FStar_Reflection_Types.binder,unit) FStar_Tactics_Effect._dm4f_TAC_repr)
  =
  fun uu____499  ->
    fun ps  ->
      match (FStar_Tactics_Builtins.apply_lemma
               (FStar_Reflection_Basic.pack_ln
                  (FStar_Reflection_Data.Tv_FVar
                     (FStar_Reflection_Basic.pack_fv
                        ["FStar"; "Tactics"; "Logic"; "imp_intro_lem"]))))
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.Logic.fst"
                          (Prims.of_int (71)) (Prims.of_int (4))
                          (Prims.of_int (71)) (Prims.of_int (32))))))
      with
      | FStar_Tactics_Result.Success (a,ps') ->
          (match () with
           | () ->
               (FStar_Tactics_Builtins.intro ())
                 (FStar_Tactics_Types.decr_depth
                    (FStar_Tactics_Types.set_proofstate_range ps'
                       (FStar_Range.prims_to_fstar_range
                          (Prims.mk_range "FStar.Tactics.Logic.fst"
                             (Prims.of_int (72)) (Prims.of_int (4))
                             (Prims.of_int (72)) (Prims.of_int (12)))))))
      | FStar_Tactics_Result.Failed (e,ps') ->
          FStar_Tactics_Result.Failed (e, ps')
  
let (implies_intros :
  unit ->
    (FStar_Reflection_Types.binders,unit) FStar_Tactics_Effect._dm4f_TAC_repr)
  = fun uu____574  -> FStar_Tactics_Derived.repeat1 implies_intro 
let (l_intro :
  unit ->
    (FStar_Reflection_Types.binder,unit) FStar_Tactics_Effect._dm4f_TAC_repr)
  =
  fun uu____597  -> FStar_Tactics_Derived.or_else forall_intro implies_intro 
let (l_intros :
  unit ->
    (FStar_Reflection_Types.binder Prims.list,unit)
      FStar_Tactics_Effect._dm4f_TAC_repr)
  = fun uu____622  -> FStar_Tactics_Derived.repeat l_intro 
let (squash_intro : unit -> (unit,unit) FStar_Tactics_Effect._dm4f_TAC_repr)
  =
  fun uu____645  ->
    FStar_Tactics_Derived.apply
      (FStar_Reflection_Basic.pack_ln
         (FStar_Reflection_Data.Tv_FVar
            (FStar_Reflection_Basic.pack_fv
               ["FStar"; "Squash"; "return_squash"])))
  
let (l_exact :
  FStar_Reflection_Types.term ->
    (unit,unit) FStar_Tactics_Effect._dm4f_TAC_repr)
  =
  fun t  ->
    FStar_Tactics_Derived.try_with
      (fun uu___64_689  ->
         match () with | () -> FStar_Tactics_Derived.exact t)
      (fun uu___63_692  ->
         fun ps  ->
           match (squash_intro ())
                   (FStar_Tactics_Types.incr_depth
                      (FStar_Tactics_Types.set_proofstate_range ps
                         (FStar_Range.prims_to_fstar_range
                            (Prims.mk_range "FStar.Tactics.Logic.fst"
                               (Prims.of_int (84)) (Prims.of_int (12))
                               (Prims.of_int (84)) (Prims.of_int (27))))))
           with
           | FStar_Tactics_Result.Success (a,ps') ->
               (match () with
                | () ->
                    (FStar_Tactics_Derived.exact t)
                      (FStar_Tactics_Types.decr_depth
                         (FStar_Tactics_Types.set_proofstate_range ps'
                            (FStar_Range.prims_to_fstar_range
                               (Prims.mk_range "FStar.Tactics.Logic.fst"
                                  (Prims.of_int (84)) (Prims.of_int (29))
                                  (Prims.of_int (84)) (Prims.of_int (36)))))))
           | FStar_Tactics_Result.Failed (e,ps') ->
               FStar_Tactics_Result.Failed (e, ps'))
  
let (hyp :
  FStar_Reflection_Types.binder ->
    (unit,unit) FStar_Tactics_Effect._dm4f_TAC_repr)
  =
  fun b  ->
    fun ps  ->
      match (FStar_Tactics_Derived.binder_to_term b)
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.Logic.fst"
                          (Prims.of_int (86)) (Prims.of_int (40))
                          (Prims.of_int (86)) (Prims.of_int (58))))))
      with
      | FStar_Tactics_Result.Success (a,ps') ->
          (match () with
           | () ->
               (l_exact a)
                 (FStar_Tactics_Types.decr_depth
                    (FStar_Tactics_Types.set_proofstate_range ps'
                       (FStar_Range.prims_to_fstar_range
                          (Prims.mk_range "FStar.Tactics.Logic.fst"
                             (Prims.of_int (86)) (Prims.of_int (32))
                             (Prims.of_int (86)) (Prims.of_int (58)))))))
      | FStar_Tactics_Result.Failed (e,ps') ->
          FStar_Tactics_Result.Failed (e, ps')
  

let (pose_lemma :
  FStar_Reflection_Types.term ->
    (FStar_Reflection_Types.binder,unit) FStar_Tactics_Effect._dm4f_TAC_repr)
  =
  fun t  ->
    fun ps  ->
      match match (FStar_Tactics_Derived.cur_env ())
                    (FStar_Tactics_Types.incr_depth
                       (FStar_Tactics_Types.set_proofstate_range
                          (FStar_Tactics_Types.incr_depth
                             (FStar_Tactics_Types.set_proofstate_range ps
                                (FStar_Range.prims_to_fstar_range
                                   (Prims.mk_range "FStar.Tactics.Logic.fst"
                                      (Prims.of_int (93)) (Prims.of_int (10))
                                      (Prims.of_int (93)) (Prims.of_int (28))))))
                          (FStar_Range.prims_to_fstar_range
                             (Prims.mk_range "FStar.Tactics.Logic.fst"
                                (Prims.of_int (93)) (Prims.of_int (14))
                                (Prims.of_int (93)) (Prims.of_int (26))))))
            with
            | FStar_Tactics_Result.Success (a,ps') ->
                (match () with
                 | () ->
                     (FStar_Tactics_Builtins.tcc a t)
                       (FStar_Tactics_Types.decr_depth
                          (FStar_Tactics_Types.set_proofstate_range ps'
                             (FStar_Range.prims_to_fstar_range
                                (Prims.mk_range "FStar.Tactics.Logic.fst"
                                   (Prims.of_int (93)) (Prims.of_int (10))
                                   (Prims.of_int (93)) (Prims.of_int (28)))))))
            | FStar_Tactics_Result.Failed (e,ps') ->
                FStar_Tactics_Result.Failed (e, ps')
      with
      | FStar_Tactics_Result.Success (a,ps') ->
          (match () with
           | () ->
               (match (match FStar_Reflection_Basic.inspect_comp a with
                       | FStar_Reflection_Data.C_Lemma (pre,post) ->
                           (fun s  ->
                              FStar_Tactics_Result.Success ((pre, post), s))
                       | uu____1157 -> FStar_Tactics_Derived.fail "")
                        (FStar_Tactics_Types.incr_depth
                           (FStar_Tactics_Types.set_proofstate_range
                              (FStar_Tactics_Types.decr_depth
                                 (FStar_Tactics_Types.set_proofstate_range
                                    ps'
                                    (FStar_Range.prims_to_fstar_range
                                       (Prims.mk_range
                                          "FStar.Tactics.Logic.fst"
                                          (Prims.of_int (94))
                                          (Prims.of_int (2))
                                          (Prims.of_int (109))
                                          (Prims.of_int (5))))))
                              (FStar_Range.prims_to_fstar_range
                                 (Prims.mk_range "FStar.Tactics.Logic.fst"
                                    (Prims.of_int (95)) (Prims.of_int (4))
                                    (Prims.of_int (97)) (Prims.of_int (18))))))
                with
                | FStar_Tactics_Result.Success (a1,ps'1) ->
                    (match () with
                     | () ->
                         ((match a1 with
                           | (pre,post) ->
                               (fun ps1  ->
                                  match (FStar_Reflection_Formula.term_as_formula'
                                           pre)
                                          (FStar_Tactics_Types.incr_depth
                                             (FStar_Tactics_Types.set_proofstate_range
                                                ps1
                                                (FStar_Range.prims_to_fstar_range
                                                   (Prims.mk_range
                                                      "FStar.Tactics.Logic.fst"
                                                      (Prims.of_int (100))
                                                      (Prims.of_int (8))
                                                      (Prims.of_int (100))
                                                      (Prims.of_int (28))))))
                                  with
                                  | FStar_Tactics_Result.Success (a2,ps'2) ->
                                      (match () with
                                       | () ->
                                           ((match a2 with
                                             | FStar_Reflection_Formula.True_
                                                  ->
                                                 FStar_Tactics_Derived.pose
                                                   (FStar_Reflection_Basic.pack_ln
                                                      (FStar_Reflection_Data.Tv_App
                                                         ((FStar_Reflection_Basic.pack_ln
                                                             (FStar_Reflection_Data.Tv_App
                                                                ((FStar_Reflection_Basic.pack_ln
                                                                    (
                                                                    FStar_Reflection_Data.Tv_App
                                                                    ((FStar_Reflection_Basic.pack_ln
                                                                    (FStar_Reflection_Data.Tv_App
                                                                    ((FStar_Reflection_Basic.pack_ln
                                                                    (FStar_Reflection_Data.Tv_FVar
                                                                    (FStar_Reflection_Basic.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "Logic";
                                                                    "__lemma_to_squash"]))),
                                                                    (pre,
                                                                    FStar_Reflection_Data.Q_Implicit)))),
                                                                    (post,
                                                                    FStar_Reflection_Data.Q_Implicit)))),
                                                                  ((FStar_Reflection_Basic.pack_ln
                                                                    (FStar_Reflection_Data.Tv_Const
                                                                    FStar_Reflection_Data.C_Unit)),
                                                                    FStar_Reflection_Data.Q_Explicit)))),
                                                           ((FStar_Reflection_Basic.pack_ln
                                                               (FStar_Reflection_Data.Tv_Abs
                                                                  ((FStar_Reflection_Basic.pack_binder
                                                                    (FStar_Reflection_Basic.pack_bv
                                                                    {
                                                                    FStar_Reflection_Data.bv_ppname
                                                                    = "uu___";
                                                                    FStar_Reflection_Data.bv_index
                                                                    =
                                                                    (Prims.of_int (86));
                                                                    FStar_Reflection_Data.bv_sort
                                                                    =
                                                                    (FStar_Reflection_Basic.pack_ln
                                                                    (FStar_Reflection_Data.Tv_FVar
                                                                    (FStar_Reflection_Basic.pack_fv
                                                                    ["Prims";
                                                                    "unit"])))
                                                                    })
                                                                    FStar_Reflection_Data.Q_Explicit),
                                                                    t))),
                                                             FStar_Reflection_Data.Q_Explicit))))
                                             | uu____1217 ->
                                                 (fun ps2  ->
                                                    match (FStar_Tactics_Derived.tcut
                                                             (FStar_Reflection_Basic.pack_ln
                                                                (FStar_Reflection_Data.Tv_App
                                                                   ((FStar_Reflection_Basic.pack_ln
                                                                    (FStar_Reflection_Data.Tv_FVar
                                                                    (FStar_Reflection_Basic.pack_fv
                                                                    ["Prims";
                                                                    "squash"]))),
                                                                    (pre,
                                                                    FStar_Reflection_Data.Q_Explicit)))))
                                                            (FStar_Tactics_Types.incr_depth
                                                               (FStar_Tactics_Types.set_proofstate_range
                                                                  ps2
                                                                  (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Logic.fst"
                                                                    (Prims.of_int (104))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (104))
                                                                    (Prims.of_int (37))))))
                                                    with
                                                    | FStar_Tactics_Result.Success
                                                        (a3,ps'3) ->
                                                        (match () with
                                                         | () ->
                                                             (match match 
                                                                    match ()
                                                                    with
                                                                    | 
                                                                    () ->
                                                                    (match 
                                                                    (FStar_Tactics_Derived.binder_to_term
                                                                    a3)
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Logic.fst"
                                                                    (Prims.of_int (106))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (109))
                                                                    (Prims.of_int (5))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Logic.fst"
                                                                    (Prims.of_int (106))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (106))
                                                                    (Prims.of_int (102))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Logic.fst"
                                                                    (Prims.of_int (106))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (106))
                                                                    (Prims.of_int (102))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Logic.fst"
                                                                    (Prims.of_int (106))
                                                                    (Prims.of_int (97))
                                                                    (Prims.of_int (106))
                                                                    (Prims.of_int (98))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Logic.fst"
                                                                    (Prims.of_int (106))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (106))
                                                                    (Prims.of_int (102))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Logic.fst"
                                                                    (Prims.of_int (106))
                                                                    (Prims.of_int (60))
                                                                    (Prims.of_int (106))
                                                                    (Prims.of_int (81))))))
                                                                    with
                                                                    | 
                                                                    FStar_Tactics_Result.Success
                                                                    (a4,ps'4)
                                                                    ->
                                                                    (match ()
                                                                    with
                                                                    | 
                                                                    () ->
                                                                    FStar_Tactics_Result.Success
                                                                    ((FStar_Reflection_Basic.pack_ln
                                                                    (FStar_Reflection_Data.Tv_App
                                                                    ((FStar_Reflection_Basic.pack_ln
                                                                    (FStar_Reflection_Data.Tv_App
                                                                    ((FStar_Reflection_Basic.pack_ln
                                                                    (FStar_Reflection_Data.Tv_App
                                                                    ((FStar_Reflection_Basic.pack_ln
                                                                    (FStar_Reflection_Data.Tv_App
                                                                    ((FStar_Reflection_Basic.pack_ln
                                                                    (FStar_Reflection_Data.Tv_FVar
                                                                    (FStar_Reflection_Basic.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "Logic";
                                                                    "__lemma_to_squash"]))),
                                                                    (pre,
                                                                    FStar_Reflection_Data.Q_Implicit)))),
                                                                    (post,
                                                                    FStar_Reflection_Data.Q_Implicit)))),
                                                                    (a4,
                                                                    FStar_Reflection_Data.Q_Explicit)))),
                                                                    ((FStar_Reflection_Basic.pack_ln
                                                                    (FStar_Reflection_Data.Tv_Abs
                                                                    ((FStar_Reflection_Basic.pack_binder
                                                                    (FStar_Reflection_Basic.pack_bv
                                                                    {
                                                                    FStar_Reflection_Data.bv_ppname
                                                                    = "uu___";
                                                                    FStar_Reflection_Data.bv_index
                                                                    =
                                                                    (Prims.of_int (93));
                                                                    FStar_Reflection_Data.bv_sort
                                                                    =
                                                                    (FStar_Reflection_Basic.pack_ln
                                                                    (FStar_Reflection_Data.Tv_FVar
                                                                    (FStar_Reflection_Basic.pack_fv
                                                                    ["Prims";
                                                                    "unit"])))
                                                                    })
                                                                    FStar_Reflection_Data.Q_Explicit),
                                                                    t))),
                                                                    FStar_Reflection_Data.Q_Explicit)))),
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'4
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Logic.fst"
                                                                    (Prims.of_int (106))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (106))
                                                                    (Prims.of_int (102))))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e,ps'4)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'4))
                                                                    with
                                                                    | 
                                                                    FStar_Tactics_Result.Success
                                                                    (a4,ps'4)
                                                                    ->
                                                                    (match ()
                                                                    with
                                                                    | 
                                                                    () ->
                                                                    (FStar_Tactics_Derived.pose
                                                                    a4)
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'4
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Logic.fst"
                                                                    (Prims.of_int (106))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (106))
                                                                    (Prims.of_int (102)))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e,ps'4)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'4)
                                                              with
                                                              | FStar_Tactics_Result.Success
                                                                  (a4,ps'4)
                                                                  ->
                                                                  (match ()
                                                                   with
                                                                   | 
                                                                   () ->
                                                                    (match 
                                                                    (FStar_Tactics_Derived.flip
                                                                    ())
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'4
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Logic.fst"
                                                                    (Prims.of_int (107))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (109))
                                                                    (Prims.of_int (5))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Logic.fst"
                                                                    (Prims.of_int (107))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (107))
                                                                    (Prims.of_int (11))))))
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
                                                                    match 
                                                                    (FStar_Tactics_Derived.trytac
                                                                    FStar_Tactics_Builtins.trivial)
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'5
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Logic.fst"
                                                                    (Prims.of_int (108))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (109))
                                                                    (Prims.of_int (5))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Logic.fst"
                                                                    (Prims.of_int (108))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (108))
                                                                    (Prims.of_int (27))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Logic.fst"
                                                                    (Prims.of_int (108))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (108))
                                                                    (Prims.of_int (27))))))
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
                                                                    ((),
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'6
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Logic.fst"
                                                                    (Prims.of_int (108))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (108))
                                                                    (Prims.of_int (27))))))))
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
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
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
                                                          (e, ps'3))))
                                             (FStar_Tactics_Types.decr_depth
                                                (FStar_Tactics_Types.set_proofstate_range
                                                   ps'2
                                                   (FStar_Range.prims_to_fstar_range
                                                      (Prims.mk_range
                                                         "FStar.Tactics.Logic.fst"
                                                         (Prims.of_int (100))
                                                         (Prims.of_int (2))
                                                         (Prims.of_int (109))
                                                         (Prims.of_int (5)))))))
                                  | FStar_Tactics_Result.Failed (e,ps'2) ->
                                      FStar_Tactics_Result.Failed (e, ps'2))))
                           (FStar_Tactics_Types.decr_depth
                              (FStar_Tactics_Types.set_proofstate_range ps'1
                                 (FStar_Range.prims_to_fstar_range
                                    (Prims.mk_range "FStar.Tactics.Logic.fst"
                                       (Prims.of_int (94)) (Prims.of_int (2))
                                       (Prims.of_int (109))
                                       (Prims.of_int (5)))))))
                | FStar_Tactics_Result.Failed (e,ps'1) ->
                    FStar_Tactics_Result.Failed (e, ps'1)))
      | FStar_Tactics_Result.Failed (e,ps') ->
          FStar_Tactics_Result.Failed (e, ps')
  
let (explode : unit -> (unit,unit) FStar_Tactics_Effect._dm4f_TAC_repr) =
  fun uu____1357  ->
    fun ps  ->
      match (FStar_Tactics_Derived.repeatseq
               (fun uu____1424  ->
                  FStar_Tactics_Derived.first
                    [(fun uu____1467  ->
                        fun ps1  ->
                          match (l_intro ())
                                  (FStar_Tactics_Types.incr_depth
                                     (FStar_Tactics_Types.set_proofstate_range
                                        ps1
                                        (FStar_Range.prims_to_fstar_range
                                           (Prims.mk_range
                                              "FStar.Tactics.Logic.fst"
                                              (Prims.of_int (113))
                                              (Prims.of_int (50))
                                              (Prims.of_int (113))
                                              (Prims.of_int (62))))))
                          with
                          | FStar_Tactics_Result.Success (a,ps') ->
                              (match () with
                               | () ->
                                   FStar_Tactics_Result.Success
                                     ((),
                                       (FStar_Tactics_Types.decr_depth
                                          (FStar_Tactics_Types.set_proofstate_range
                                             ps'
                                             (FStar_Range.prims_to_fstar_range
                                                (Prims.mk_range
                                                   "FStar.Tactics.Logic.fst"
                                                   (Prims.of_int (113))
                                                   (Prims.of_int (43))
                                                   (Prims.of_int (113))
                                                   (Prims.of_int (62))))))))
                          | FStar_Tactics_Result.Failed (e,ps') ->
                              FStar_Tactics_Result.Failed (e, ps'));
                    (fun uu____1537  ->
                       fun ps1  ->
                         match (split ())
                                 (FStar_Tactics_Types.incr_depth
                                    (FStar_Tactics_Types.set_proofstate_range
                                       ps1
                                       (FStar_Range.prims_to_fstar_range
                                          (Prims.mk_range
                                             "FStar.Tactics.Logic.fst"
                                             (Prims.of_int (114))
                                             (Prims.of_int (49))
                                             (Prims.of_int (114))
                                             (Prims.of_int (59))))))
                         with
                         | FStar_Tactics_Result.Success (a,ps') ->
                             (match () with
                              | () ->
                                  FStar_Tactics_Result.Success
                                    ((),
                                      (FStar_Tactics_Types.decr_depth
                                         (FStar_Tactics_Types.set_proofstate_range
                                            ps'
                                            (FStar_Range.prims_to_fstar_range
                                               (Prims.mk_range
                                                  "FStar.Tactics.Logic.fst"
                                                  (Prims.of_int (114))
                                                  (Prims.of_int (42))
                                                  (Prims.of_int (114))
                                                  (Prims.of_int (59))))))))
                         | FStar_Tactics_Result.Failed (e,ps') ->
                             FStar_Tactics_Result.Failed (e, ps'))]))
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.Logic.fst"
                          (Prims.of_int (112)) (Prims.of_int (11))
                          (Prims.of_int (114)) (Prims.of_int (63))))))
      with
      | FStar_Tactics_Result.Success (a,ps') ->
          (match () with
           | () ->
               FStar_Tactics_Result.Success
                 ((),
                   (FStar_Tactics_Types.decr_depth
                      (FStar_Tactics_Types.set_proofstate_range ps'
                         (FStar_Range.prims_to_fstar_range
                            (Prims.mk_range "FStar.Tactics.Logic.fst"
                               (Prims.of_int (112)) (Prims.of_int (4))
                               (Prims.of_int (114)) (Prims.of_int (63))))))))
      | FStar_Tactics_Result.Failed (e,ps') ->
          FStar_Tactics_Result.Failed (e, ps')
  
let rec (visit :
  (unit -> (unit,unit) FStar_Tactics_Effect._dm4f_TAC_repr) ->
    (unit,unit) FStar_Tactics_Effect._dm4f_TAC_repr)
  =
  fun callback  ->
    FStar_Tactics_Derived.focus
      (fun uu____1744  ->
         FStar_Tactics_Derived.or_else callback
           (fun uu____1799  ->
              fun ps  ->
                match (FStar_Tactics_Derived.cur_goal ())
                        (FStar_Tactics_Types.incr_depth
                           (FStar_Tactics_Types.set_proofstate_range ps
                              (FStar_Range.prims_to_fstar_range
                                 (Prims.mk_range "FStar.Tactics.Logic.fst"
                                    (Prims.of_int (120)) (Prims.of_int (28))
                                    (Prims.of_int (120)) (Prims.of_int (39))))))
                with
                | FStar_Tactics_Result.Success (a,ps') ->
                    (match () with
                     | () ->
                         (match (FStar_Reflection_Formula.term_as_formula a)
                                  (FStar_Tactics_Types.incr_depth
                                     (FStar_Tactics_Types.set_proofstate_range
                                        (FStar_Tactics_Types.decr_depth
                                           (FStar_Tactics_Types.set_proofstate_range
                                              ps'
                                              (FStar_Range.prims_to_fstar_range
                                                 (Prims.mk_range
                                                    "FStar.Tactics.Logic.fst"
                                                    (Prims.of_int (121))
                                                    (Prims.of_int (20))
                                                    (Prims.of_int (131))
                                                    (Prims.of_int (26))))))
                                        (FStar_Range.prims_to_fstar_range
                                           (Prims.mk_range
                                              "FStar.Tactics.Logic.fst"
                                              (Prims.of_int (121))
                                              (Prims.of_int (26))
                                              (Prims.of_int (121))
                                              (Prims.of_int (43))))))
                          with
                          | FStar_Tactics_Result.Success (a1,ps'1) ->
                              (match () with
                               | () ->
                                   ((match a1 with
                                     | FStar_Reflection_Formula.Forall
                                         (b,phi) ->
                                         (fun ps1  ->
                                            match (forall_intros ())
                                                    (FStar_Tactics_Types.incr_depth
                                                       (FStar_Tactics_Types.set_proofstate_range
                                                          ps1
                                                          (FStar_Range.prims_to_fstar_range
                                                             (Prims.mk_range
                                                                "FStar.Tactics.Logic.fst"
                                                                (Prims.of_int (123))
                                                                (Prims.of_int (38))
                                                                (Prims.of_int (123))
                                                                (Prims.of_int (54))))))
                                            with
                                            | FStar_Tactics_Result.Success
                                                (a2,ps'2) ->
                                                (match () with
                                                 | () ->
                                                     (FStar_Tactics_Derived.seq
                                                        (fun uu____1996  ->
                                                           visit callback)
                                                        (fun uu____1998  ->
                                                           l_revert_all a2))
                                                       (FStar_Tactics_Types.decr_depth
                                                          (FStar_Tactics_Types.set_proofstate_range
                                                             ps'2
                                                             (FStar_Range.prims_to_fstar_range
                                                                (Prims.mk_range
                                                                   "FStar.Tactics.Logic.fst"
                                                                   (Prims.of_int (124))
                                                                   (Prims.of_int (24))
                                                                   (Prims.of_int (124))
                                                                   (Prims.of_int (87)))))))
                                            | FStar_Tactics_Result.Failed
                                                (e,ps'2) ->
                                                FStar_Tactics_Result.Failed
                                                  (e, ps'2))
                                     | FStar_Reflection_Formula.And (p,q) ->
                                         FStar_Tactics_Derived.seq split
                                           (fun uu____2005  -> visit callback)
                                     | FStar_Reflection_Formula.Implies 
                                         (p,q) ->
                                         (fun ps1  ->
                                            match (implies_intro ())
                                                    (FStar_Tactics_Types.incr_depth
                                                       (FStar_Tactics_Types.set_proofstate_range
                                                          ps1
                                                          (FStar_Range.prims_to_fstar_range
                                                             (Prims.mk_range
                                                                "FStar.Tactics.Logic.fst"
                                                                (Prims.of_int (128))
                                                                (Prims.of_int (32))
                                                                (Prims.of_int (128))
                                                                (Prims.of_int (48))))))
                                            with
                                            | FStar_Tactics_Result.Success
                                                (a2,ps'2) ->
                                                (match () with
                                                 | () ->
                                                     (FStar_Tactics_Derived.seq
                                                        (fun uu____2030  ->
                                                           visit callback)
                                                        l_revert)
                                                       (FStar_Tactics_Types.decr_depth
                                                          (FStar_Tactics_Types.set_proofstate_range
                                                             ps'2
                                                             (FStar_Range.prims_to_fstar_range
                                                                (Prims.mk_range
                                                                   "FStar.Tactics.Logic.fst"
                                                                   (Prims.of_int (129))
                                                                   (Prims.of_int (24))
                                                                   (Prims.of_int (129))
                                                                   (Prims.of_int (63)))))))
                                            | FStar_Tactics_Result.Failed
                                                (e,ps'2) ->
                                                FStar_Tactics_Result.Failed
                                                  (e, ps'2))
                                     | uu____2033 ->
                                         (fun s  ->
                                            FStar_Tactics_Result.Success
                                              ((), s))))
                                     (FStar_Tactics_Types.decr_depth
                                        (FStar_Tactics_Types.set_proofstate_range
                                           ps'1
                                           (FStar_Range.prims_to_fstar_range
                                              (Prims.mk_range
                                                 "FStar.Tactics.Logic.fst"
                                                 (Prims.of_int (121))
                                                 (Prims.of_int (20))
                                                 (Prims.of_int (131))
                                                 (Prims.of_int (26)))))))
                          | FStar_Tactics_Result.Failed (e,ps'1) ->
                              FStar_Tactics_Result.Failed (e, ps'1)))
                | FStar_Tactics_Result.Failed (e,ps') ->
                    FStar_Tactics_Result.Failed (e, ps')))
  
let rec (simplify_eq_implication :
  unit -> (unit,unit) FStar_Tactics_Effect._dm4f_TAC_repr) =
  fun uu____2071  ->
    fun ps  ->
      match (FStar_Tactics_Derived.cur_env ())
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.Logic.fst"
                          (Prims.of_int (136)) (Prims.of_int (12))
                          (Prims.of_int (136)) (Prims.of_int (22))))))
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
                                          "FStar.Tactics.Logic.fst"
                                          (Prims.of_int (137))
                                          (Prims.of_int (4))
                                          (Prims.of_int (146))
                                          (Prims.of_int (37))))))
                              (FStar_Range.prims_to_fstar_range
                                 (Prims.mk_range "FStar.Tactics.Logic.fst"
                                    (Prims.of_int (137)) (Prims.of_int (12))
                                    (Prims.of_int (137)) (Prims.of_int (23))))))
                with
                | FStar_Tactics_Result.Success (a1,ps'1) ->
                    (match () with
                     | () ->
                         (match (FStar_Tactics_Derived.destruct_equality_implication
                                   a1)
                                  (FStar_Tactics_Types.incr_depth
                                     (FStar_Tactics_Types.set_proofstate_range
                                        (FStar_Tactics_Types.decr_depth
                                           (FStar_Tactics_Types.set_proofstate_range
                                              ps'1
                                              (FStar_Range.prims_to_fstar_range
                                                 (Prims.mk_range
                                                    "FStar.Tactics.Logic.fst"
                                                    (Prims.of_int (138))
                                                    (Prims.of_int (4))
                                                    (Prims.of_int (146))
                                                    (Prims.of_int (37))))))
                                        (FStar_Range.prims_to_fstar_range
                                           (Prims.mk_range
                                              "FStar.Tactics.Logic.fst"
                                              (Prims.of_int (138))
                                              (Prims.of_int (12))
                                              (Prims.of_int (138))
                                              (Prims.of_int (43))))))
                          with
                          | FStar_Tactics_Result.Success (a2,ps'2) ->
                              (match () with
                               | () ->
                                   ((match a2 with
                                     | FStar_Pervasives_Native.None  ->
                                         FStar_Tactics_Derived.fail
                                           "Not an equality implication"
                                     | FStar_Pervasives_Native.Some
                                         (uu____2248,rhs) ->
                                         (fun ps1  ->
                                            match (implies_intro ())
                                                    (FStar_Tactics_Types.incr_depth
                                                       (FStar_Tactics_Types.set_proofstate_range
                                                          ps1
                                                          (FStar_Range.prims_to_fstar_range
                                                             (Prims.mk_range
                                                                "FStar.Tactics.Logic.fst"
                                                                (Prims.of_int (143))
                                                                (Prims.of_int (19))
                                                                (Prims.of_int (143))
                                                                (Prims.of_int (35))))))
                                            with
                                            | FStar_Tactics_Result.Success
                                                (a3,ps'3) ->
                                                (match () with
                                                 | () ->
                                                     (match (FStar_Tactics_Builtins.rewrite
                                                               a3)
                                                              (FStar_Tactics_Types.incr_depth
                                                                 (FStar_Tactics_Types.set_proofstate_range
                                                                    (
                                                                    FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Logic.fst"
                                                                    (Prims.of_int (144))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (146))
                                                                    (Prims.of_int (37))))))
                                                                    (
                                                                    FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Logic.fst"
                                                                    (Prims.of_int (144))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (144))
                                                                    (Prims.of_int (20))))))
                                                      with
                                                      | FStar_Tactics_Result.Success
                                                          (a4,ps'4) ->
                                                          (match () with
                                                           | () ->
                                                               (match 
                                                                  (FStar_Tactics_Builtins.clear_top
                                                                    ())
                                                                    (
                                                                    FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'4
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Logic.fst"
                                                                    (Prims.of_int (145))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (146))
                                                                    (Prims.of_int (37))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Logic.fst"
                                                                    (Prims.of_int (145))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (145))
                                                                    (Prims.of_int (20))))))
                                                                with
                                                                | FStar_Tactics_Result.Success
                                                                    (a5,ps'5)
                                                                    ->
                                                                    (
                                                                    match ()
                                                                    with
                                                                    | 
                                                                    () ->
                                                                    (visit
                                                                    simplify_eq_implication)
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'5
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Logic.fst"
                                                                    (Prims.of_int (146))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (146))
                                                                    (Prims.of_int (37)))))))
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
                                                  (e, ps'3))))
                                     (FStar_Tactics_Types.decr_depth
                                        (FStar_Tactics_Types.set_proofstate_range
                                           ps'2
                                           (FStar_Range.prims_to_fstar_range
                                              (Prims.mk_range
                                                 "FStar.Tactics.Logic.fst"
                                                 (Prims.of_int (139))
                                                 (Prims.of_int (4))
                                                 (Prims.of_int (146))
                                                 (Prims.of_int (37)))))))
                          | FStar_Tactics_Result.Failed (e,ps'2) ->
                              FStar_Tactics_Result.Failed (e, ps'2)))
                | FStar_Tactics_Result.Failed (e,ps'1) ->
                    FStar_Tactics_Result.Failed (e, ps'1)))
      | FStar_Tactics_Result.Failed (e,ps') ->
          FStar_Tactics_Result.Failed (e, ps')
  
let (rewrite_all_equalities :
  unit -> (unit,unit) FStar_Tactics_Effect._dm4f_TAC_repr) =
  fun uu____2325  -> visit simplify_eq_implication 
let rec (unfold_definition_and_simplify_eq :
  FStar_Reflection_Types.term ->
    (unit,unit) FStar_Tactics_Effect._dm4f_TAC_repr)
  =
  fun tm  ->
    fun ps  ->
      match (FStar_Tactics_Derived.cur_goal ())
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.Logic.fst"
                          (Prims.of_int (152)) (Prims.of_int (12))
                          (Prims.of_int (152)) (Prims.of_int (23))))))
      with
      | FStar_Tactics_Result.Success (a,ps') ->
          (match () with
           | () ->
               (match (FStar_Reflection_Formula.term_as_formula a)
                        (FStar_Tactics_Types.incr_depth
                           (FStar_Tactics_Types.set_proofstate_range
                              (FStar_Tactics_Types.decr_depth
                                 (FStar_Tactics_Types.set_proofstate_range
                                    ps'
                                    (FStar_Range.prims_to_fstar_range
                                       (Prims.mk_range
                                          "FStar.Tactics.Logic.fst"
                                          (Prims.of_int (153))
                                          (Prims.of_int (4))
                                          (Prims.of_int (167))
                                          (Prims.of_int (11))))))
                              (FStar_Range.prims_to_fstar_range
                                 (Prims.mk_range "FStar.Tactics.Logic.fst"
                                    (Prims.of_int (153)) (Prims.of_int (10))
                                    (Prims.of_int (153)) (Prims.of_int (27))))))
                with
                | FStar_Tactics_Result.Success (a1,ps'1) ->
                    (match () with
                     | () ->
                         ((match a1 with
                           | FStar_Reflection_Formula.App (hd1,arg) ->
                               if FStar_Reflection_Basic.term_eq hd1 tm
                               then FStar_Tactics_Builtins.trivial ()
                               else
                                 (fun s  ->
                                    FStar_Tactics_Result.Success ((), s))
                           | uu____2571 ->
                               (fun ps1  ->
                                  match (FStar_Tactics_Derived.destruct_equality_implication
                                           a)
                                          (FStar_Tactics_Types.incr_depth
                                             (FStar_Tactics_Types.set_proofstate_range
                                                ps1
                                                (FStar_Range.prims_to_fstar_range
                                                   (Prims.mk_range
                                                      "FStar.Tactics.Logic.fst"
                                                      (Prims.of_int (159))
                                                      (Prims.of_int (16))
                                                      (Prims.of_int (159))
                                                      (Prims.of_int (47))))))
                                  with
                                  | FStar_Tactics_Result.Success (a2,ps'2) ->
                                      (match () with
                                       | () ->
                                           ((match a2 with
                                             | FStar_Pervasives_Native.None 
                                                 ->
                                                 FStar_Tactics_Derived.fail
                                                   "Not an equality implication"
                                             | FStar_Pervasives_Native.Some
                                                 (uu____2608,rhs) ->
                                                 (fun ps2  ->
                                                    match (implies_intro ())
                                                            (FStar_Tactics_Types.incr_depth
                                                               (FStar_Tactics_Types.set_proofstate_range
                                                                  ps2
                                                                  (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Logic.fst"
                                                                    (Prims.of_int (163))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (163))
                                                                    (Prims.of_int (39))))))
                                                    with
                                                    | FStar_Tactics_Result.Success
                                                        (a3,ps'3) ->
                                                        (match () with
                                                         | () ->
                                                             (match (FStar_Tactics_Builtins.rewrite
                                                                    a3)
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Logic.fst"
                                                                    (Prims.of_int (164))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (166))
                                                                    (Prims.of_int (66))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Logic.fst"
                                                                    (Prims.of_int (164))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (164))
                                                                    (Prims.of_int (24))))))
                                                              with
                                                              | FStar_Tactics_Result.Success
                                                                  (a4,ps'4)
                                                                  ->
                                                                  (match ()
                                                                   with
                                                                   | 
                                                                   () ->
                                                                    (match 
                                                                    (FStar_Tactics_Builtins.clear_top
                                                                    ())
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'4
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Logic.fst"
                                                                    (Prims.of_int (165))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (166))
                                                                    (Prims.of_int (66))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Logic.fst"
                                                                    (Prims.of_int (165))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (165))
                                                                    (Prims.of_int (24))))))
                                                                    with
                                                                    | 
                                                                    FStar_Tactics_Result.Success
                                                                    (a5,ps'5)
                                                                    ->
                                                                    (match ()
                                                                    with
                                                                    | 
                                                                    () ->
                                                                    (visit
                                                                    (fun
                                                                    uu____2648
                                                                     ->
                                                                    unfold_definition_and_simplify_eq
                                                                    tm))
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'5
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Logic.fst"
                                                                    (Prims.of_int (166))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (166))
                                                                    (Prims.of_int (66)))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
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
                                                          (e, ps'3))))
                                             (FStar_Tactics_Types.decr_depth
                                                (FStar_Tactics_Types.set_proofstate_range
                                                   ps'2
                                                   (FStar_Range.prims_to_fstar_range
                                                      (Prims.mk_range
                                                         "FStar.Tactics.Logic.fst"
                                                         (Prims.of_int (160))
                                                         (Prims.of_int (8))
                                                         (Prims.of_int (166))
                                                         (Prims.of_int (66)))))))
                                  | FStar_Tactics_Result.Failed (e,ps'2) ->
                                      FStar_Tactics_Result.Failed (e, ps'2))))
                           (FStar_Tactics_Types.decr_depth
                              (FStar_Tactics_Types.set_proofstate_range ps'1
                                 (FStar_Range.prims_to_fstar_range
                                    (Prims.mk_range "FStar.Tactics.Logic.fst"
                                       (Prims.of_int (153))
                                       (Prims.of_int (4))
                                       (Prims.of_int (167))
                                       (Prims.of_int (11)))))))
                | FStar_Tactics_Result.Failed (e,ps'1) ->
                    FStar_Tactics_Result.Failed (e, ps'1)))
      | FStar_Tactics_Result.Failed (e,ps') ->
          FStar_Tactics_Result.Failed (e, ps')
  

let (unsquash :
  FStar_Reflection_Types.term ->
    (FStar_Reflection_Types.term,unit) FStar_Tactics_Effect._dm4f_TAC_repr)
  =
  fun t  ->
    fun ps  ->
      match () with
      | () ->
          (match (FStar_Tactics_Builtins.apply_lemma
                    (FStar_Reflection_Derived.mk_e_app
                       (FStar_Reflection_Basic.pack_ln
                          (FStar_Reflection_Data.Tv_FVar
                             (FStar_Reflection_Basic.pack_fv
                                ["FStar"; "Tactics"; "Logic"; "vbind"]))) 
                       [t]))
                   (FStar_Tactics_Types.incr_depth
                      (FStar_Tactics_Types.set_proofstate_range
                         (FStar_Tactics_Types.decr_depth
                            (FStar_Tactics_Types.set_proofstate_range
                               (FStar_Tactics_Types.incr_depth
                                  (FStar_Tactics_Types.set_proofstate_range
                                     ps
                                     (FStar_Range.prims_to_fstar_range
                                        (Prims.mk_range
                                           "FStar.Tactics.Logic.fst"
                                           (Prims.of_int (173))
                                           (Prims.of_int (12))
                                           (Prims.of_int (173))
                                           (Prims.of_int (18))))))
                               (FStar_Range.prims_to_fstar_range
                                  (Prims.mk_range "FStar.Tactics.Logic.fst"
                                     (Prims.of_int (174)) (Prims.of_int (4))
                                     (Prims.of_int (176)) (Prims.of_int (37))))))
                         (FStar_Range.prims_to_fstar_range
                            (Prims.mk_range "FStar.Tactics.Logic.fst"
                               (Prims.of_int (174)) (Prims.of_int (4))
                               (Prims.of_int (174)) (Prims.of_int (32))))))
           with
           | FStar_Tactics_Result.Success (a,ps') ->
               (match () with
                | () ->
                    (match (FStar_Tactics_Builtins.intro ())
                             (FStar_Tactics_Types.incr_depth
                                (FStar_Tactics_Types.set_proofstate_range
                                   (FStar_Tactics_Types.decr_depth
                                      (FStar_Tactics_Types.set_proofstate_range
                                         ps'
                                         (FStar_Range.prims_to_fstar_range
                                            (Prims.mk_range
                                               "FStar.Tactics.Logic.fst"
                                               (Prims.of_int (175))
                                               (Prims.of_int (4))
                                               (Prims.of_int (176))
                                               (Prims.of_int (37))))))
                                   (FStar_Range.prims_to_fstar_range
                                      (Prims.mk_range
                                         "FStar.Tactics.Logic.fst"
                                         (Prims.of_int (175))
                                         (Prims.of_int (12))
                                         (Prims.of_int (175))
                                         (Prims.of_int (20))))))
                     with
                     | FStar_Tactics_Result.Success (a1,ps'1) ->
                         (match () with
                          | () ->
                              FStar_Tactics_Result.Success
                                ((FStar_Reflection_Basic.pack_ln
                                    (FStar_Reflection_Data.Tv_Var
                                       (FStar_Reflection_Derived.bv_of_binder
                                          a1))),
                                  (FStar_Tactics_Types.decr_depth
                                     (FStar_Tactics_Types.set_proofstate_range
                                        ps'1
                                        (FStar_Range.prims_to_fstar_range
                                           (Prims.mk_range
                                              "FStar.Tactics.Logic.fst"
                                              (Prims.of_int (176))
                                              (Prims.of_int (4))
                                              (Prims.of_int (176))
                                              (Prims.of_int (37))))))))
                     | FStar_Tactics_Result.Failed (e,ps'1) ->
                         FStar_Tactics_Result.Failed (e, ps'1)))
           | FStar_Tactics_Result.Failed (e,ps') ->
               FStar_Tactics_Result.Failed (e, ps'))
  

let (cases_or :
  FStar_Reflection_Types.term ->
    (unit,unit) FStar_Tactics_Effect._dm4f_TAC_repr)
  =
  fun o  ->
    FStar_Tactics_Builtins.apply_lemma
      (FStar_Reflection_Derived.mk_e_app
         (FStar_Reflection_Basic.pack_ln
            (FStar_Reflection_Data.Tv_FVar
               (FStar_Reflection_Basic.pack_fv
                  ["FStar"; "Tactics"; "Logic"; "or_ind"]))) [o])
  

let (cases_bool :
  FStar_Reflection_Types.term ->
    (unit,unit) FStar_Tactics_Effect._dm4f_TAC_repr)
  =
  fun b  ->
    fun ps  ->
      match () with
      | () ->
          (FStar_Tactics_Derived.seq
             (fun uu____2921  ->
                FStar_Tactics_Builtins.apply_lemma
                  (FStar_Reflection_Derived.mk_e_app
                     (FStar_Reflection_Basic.pack_ln
                        (FStar_Reflection_Data.Tv_FVar
                           (FStar_Reflection_Basic.pack_fv
                              ["FStar"; "Tactics"; "Logic"; "bool_ind"])))
                     [b]))
             (fun uu____2933  ->
                fun ps1  ->
                  match (FStar_Tactics_Derived.trytac
                           (fun uu____2988  ->
                              fun ps2  ->
                                match (implies_intro ())
                                        (FStar_Tactics_Types.incr_depth
                                           (FStar_Tactics_Types.set_proofstate_range
                                              ps2
                                              (FStar_Range.prims_to_fstar_range
                                                 (Prims.mk_range
                                                    "FStar.Tactics.Logic.fst"
                                                    (Prims.of_int (196))
                                                    (Prims.of_int (53))
                                                    (Prims.of_int (196))
                                                    (Prims.of_int (69))))))
                                with
                                | FStar_Tactics_Result.Success (a,ps') ->
                                    (match () with
                                     | () ->
                                         (match (FStar_Tactics_Builtins.rewrite
                                                   a)
                                                  (FStar_Tactics_Types.incr_depth
                                                     (FStar_Tactics_Types.set_proofstate_range
                                                        (FStar_Tactics_Types.decr_depth
                                                           (FStar_Tactics_Types.set_proofstate_range
                                                              ps'
                                                              (FStar_Range.prims_to_fstar_range
                                                                 (Prims.mk_range
                                                                    "FStar.Tactics.Logic.fst"
                                                                    (Prims.of_int (196))
                                                                    (Prims.of_int (73))
                                                                    (Prims.of_int (196))
                                                                    (Prims.of_int (96))))))
                                                        (FStar_Range.prims_to_fstar_range
                                                           (Prims.mk_range
                                                              "FStar.Tactics.Logic.fst"
                                                              (Prims.of_int (196))
                                                              (Prims.of_int (73))
                                                              (Prims.of_int (196))
                                                              (Prims.of_int (82))))))
                                          with
                                          | FStar_Tactics_Result.Success
                                              (a1,ps'1) ->
                                              (match () with
                                               | () ->
                                                   (FStar_Tactics_Builtins.clear_top
                                                      ())
                                                     (FStar_Tactics_Types.decr_depth
                                                        (FStar_Tactics_Types.set_proofstate_range
                                                           ps'1
                                                           (FStar_Range.prims_to_fstar_range
                                                              (Prims.mk_range
                                                                 "FStar.Tactics.Logic.fst"
                                                                 (Prims.of_int (196))
                                                                 (Prims.of_int (84))
                                                                 (Prims.of_int (196))
                                                                 (Prims.of_int (96)))))))
                                          | FStar_Tactics_Result.Failed
                                              (e,ps'1) ->
                                              FStar_Tactics_Result.Failed
                                                (e, ps'1)))
                                | FStar_Tactics_Result.Failed (e,ps') ->
                                    FStar_Tactics_Result.Failed (e, ps')))
                          (FStar_Tactics_Types.incr_depth
                             (FStar_Tactics_Types.set_proofstate_range ps1
                                (FStar_Range.prims_to_fstar_range
                                   (Prims.mk_range "FStar.Tactics.Logic.fst"
                                      (Prims.of_int (196))
                                      (Prims.of_int (27))
                                      (Prims.of_int (196))
                                      (Prims.of_int (97))))))
                  with
                  | FStar_Tactics_Result.Success (a,ps') ->
                      (match () with
                       | () ->
                           FStar_Tactics_Result.Success
                             ((),
                               (FStar_Tactics_Types.decr_depth
                                  (FStar_Tactics_Types.set_proofstate_range
                                     ps'
                                     (FStar_Range.prims_to_fstar_range
                                        (Prims.mk_range
                                           "FStar.Tactics.Logic.fst"
                                           (Prims.of_int (196))
                                           (Prims.of_int (101))
                                           (Prims.of_int (196))
                                           (Prims.of_int (103))))))))
                  | FStar_Tactics_Result.Failed (e,ps') ->
                      FStar_Tactics_Result.Failed (e, ps')))
            (FStar_Tactics_Types.decr_depth
               (FStar_Tactics_Types.set_proofstate_range
                  (FStar_Tactics_Types.incr_depth
                     (FStar_Tactics_Types.set_proofstate_range ps
                        (FStar_Range.prims_to_fstar_range
                           (Prims.mk_range "FStar.Tactics.Logic.fst"
                              (Prims.of_int (194)) (Prims.of_int (13))
                              (Prims.of_int (194)) (Prims.of_int (22))))))
                  (FStar_Range.prims_to_fstar_range
                     (Prims.mk_range "FStar.Tactics.Logic.fst"
                        (Prims.of_int (195)) (Prims.of_int (4))
                        (Prims.of_int (196)) (Prims.of_int (104))))))
  


let (left : unit -> (unit,unit) FStar_Tactics_Effect._dm4f_TAC_repr) =
  fun uu____3099  ->
    FStar_Tactics_Builtins.apply_lemma
      (FStar_Reflection_Basic.pack_ln
         (FStar_Reflection_Data.Tv_FVar
            (FStar_Reflection_Basic.pack_fv
               ["FStar"; "Tactics"; "Logic"; "or_intro_1"])))
  
let (right : unit -> (unit,unit) FStar_Tactics_Effect._dm4f_TAC_repr) =
  fun uu____3131  ->
    FStar_Tactics_Builtins.apply_lemma
      (FStar_Reflection_Basic.pack_ln
         (FStar_Reflection_Data.Tv_FVar
            (FStar_Reflection_Basic.pack_fv
               ["FStar"; "Tactics"; "Logic"; "or_intro_2"])))
  


let (and_elim :
  FStar_Reflection_Types.term ->
    (unit,unit) FStar_Tactics_Effect._dm4f_TAC_repr)
  =
  fun t  ->
    FStar_Tactics_Derived.try_with
      (fun uu___226_3185  ->
         match () with
         | () ->
             FStar_Tactics_Builtins.apply_lemma
               (FStar_Reflection_Basic.pack_ln
                  (FStar_Reflection_Data.Tv_App
                     ((FStar_Reflection_Basic.pack_ln
                         (FStar_Reflection_Data.Tv_FVar
                            (FStar_Reflection_Basic.pack_fv
                               ["FStar"; "Tactics"; "Logic"; "__and_elim"]))),
                       (t, FStar_Reflection_Data.Q_Explicit)))))
      (fun uu___225_3196  ->
         FStar_Tactics_Builtins.apply_lemma
           (FStar_Reflection_Basic.pack_ln
              (FStar_Reflection_Data.Tv_App
                 ((FStar_Reflection_Basic.pack_ln
                     (FStar_Reflection_Data.Tv_FVar
                        (FStar_Reflection_Basic.pack_fv
                           ["FStar"; "Tactics"; "Logic"; "__and_elim'"]))),
                   (t, FStar_Reflection_Data.Q_Explicit)))))
  
let (destruct_and :
  FStar_Reflection_Types.term ->
    ((FStar_Reflection_Types.binder * FStar_Reflection_Types.binder),
      unit) FStar_Tactics_Effect._dm4f_TAC_repr)
  =
  fun t  ->
    fun ps  ->
      match (and_elim t)
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.Logic.fst"
                          (Prims.of_int (229)) (Prims.of_int (4))
                          (Prims.of_int (229)) (Prims.of_int (14))))))
      with
      | FStar_Tactics_Result.Success (a,ps') ->
          (match () with
           | () ->
               (match (implies_intro ())
                        (FStar_Tactics_Types.incr_depth
                           (FStar_Tactics_Types.set_proofstate_range
                              (FStar_Tactics_Types.decr_depth
                                 (FStar_Tactics_Types.set_proofstate_range
                                    ps'
                                    (FStar_Range.prims_to_fstar_range
                                       (Prims.mk_range
                                          "FStar.Tactics.Logic.fst"
                                          (Prims.of_int (230))
                                          (Prims.of_int (4))
                                          (Prims.of_int (230))
                                          (Prims.of_int (40))))))
                              (FStar_Range.prims_to_fstar_range
                                 (Prims.mk_range "FStar.Tactics.Logic.fst"
                                    (Prims.of_int (230)) (Prims.of_int (5))
                                    (Prims.of_int (230)) (Prims.of_int (21))))))
                with
                | FStar_Tactics_Result.Success (a1,ps'1) ->
                    (match () with
                     | () ->
                         (match (implies_intro ())
                                  (FStar_Tactics_Types.incr_depth
                                     (FStar_Tactics_Types.set_proofstate_range
                                        (FStar_Tactics_Types.decr_depth
                                           (FStar_Tactics_Types.set_proofstate_range
                                              ps'1
                                              (FStar_Range.prims_to_fstar_range
                                                 (Prims.mk_range
                                                    "FStar.Tactics.Logic.fst"
                                                    (Prims.of_int (230))
                                                    (Prims.of_int (4))
                                                    (Prims.of_int (230))
                                                    (Prims.of_int (40))))))
                                        (FStar_Range.prims_to_fstar_range
                                           (Prims.mk_range
                                              "FStar.Tactics.Logic.fst"
                                              (Prims.of_int (230))
                                              (Prims.of_int (23))
                                              (Prims.of_int (230))
                                              (Prims.of_int (39))))))
                          with
                          | FStar_Tactics_Result.Success (a2,ps'2) ->
                              (match () with
                               | () ->
                                   FStar_Tactics_Result.Success
                                     ((a1, a2),
                                       (FStar_Tactics_Types.decr_depth
                                          (FStar_Tactics_Types.set_proofstate_range
                                             ps'2
                                             (FStar_Range.prims_to_fstar_range
                                                (Prims.mk_range
                                                   "FStar.Tactics.Logic.fst"
                                                   (Prims.of_int (230))
                                                   (Prims.of_int (4))
                                                   (Prims.of_int (230))
                                                   (Prims.of_int (40))))))))
                          | FStar_Tactics_Result.Failed (e,ps'2) ->
                              FStar_Tactics_Result.Failed (e, ps'2)))
                | FStar_Tactics_Result.Failed (e,ps'1) ->
                    FStar_Tactics_Result.Failed (e, ps'1)))
      | FStar_Tactics_Result.Failed (e,ps') ->
          FStar_Tactics_Result.Failed (e, ps')
  

let (witness :
  FStar_Reflection_Types.term ->
    (unit,unit) FStar_Tactics_Effect._dm4f_TAC_repr)
  =
  fun t  ->
    fun ps  ->
      match (FStar_Tactics_Derived.apply_raw
               (FStar_Reflection_Basic.pack_ln
                  (FStar_Reflection_Data.Tv_FVar
                     (FStar_Reflection_Basic.pack_fv
                        ["FStar"; "Tactics"; "Logic"; "__witness"]))))
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.Logic.fst"
                          (Prims.of_int (238)) (Prims.of_int (4))
                          (Prims.of_int (238)) (Prims.of_int (26))))))
      with
      | FStar_Tactics_Result.Success (a,ps') ->
          (match () with
           | () ->
               (FStar_Tactics_Derived.exact t)
                 (FStar_Tactics_Types.decr_depth
                    (FStar_Tactics_Types.set_proofstate_range ps'
                       (FStar_Range.prims_to_fstar_range
                          (Prims.mk_range "FStar.Tactics.Logic.fst"
                             (Prims.of_int (239)) (Prims.of_int (4))
                             (Prims.of_int (239)) (Prims.of_int (11)))))))
      | FStar_Tactics_Result.Failed (e,ps') ->
          FStar_Tactics_Result.Failed (e, ps')
  

let (elim_exists :
  FStar_Reflection_Types.term ->
    ((FStar_Reflection_Types.binder * FStar_Reflection_Types.binder),
      unit) FStar_Tactics_Effect._dm4f_TAC_repr)
  =
  fun t  ->
    fun ps  ->
      match (FStar_Tactics_Builtins.apply_lemma
               (FStar_Reflection_Basic.pack_ln
                  (FStar_Reflection_Data.Tv_App
                     ((FStar_Reflection_Basic.pack_ln
                         (FStar_Reflection_Data.Tv_FVar
                            (FStar_Reflection_Basic.pack_fv
                               ["FStar";
                               "Tactics";
                               "Logic";
                               "__elim_exists'"]))),
                       (t, FStar_Reflection_Data.Q_Explicit)))))
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.Logic.fst"
                          (Prims.of_int (248)) (Prims.of_int (2))
                          (Prims.of_int (248)) (Prims.of_int (41))))))
      with
      | FStar_Tactics_Result.Success (a,ps') ->
          (match () with
           | () ->
               (match (FStar_Tactics_Builtins.intro ())
                        (FStar_Tactics_Types.incr_depth
                           (FStar_Tactics_Types.set_proofstate_range
                              (FStar_Tactics_Types.decr_depth
                                 (FStar_Tactics_Types.set_proofstate_range
                                    ps'
                                    (FStar_Range.prims_to_fstar_range
                                       (Prims.mk_range
                                          "FStar.Tactics.Logic.fst"
                                          (Prims.of_int (249))
                                          (Prims.of_int (2))
                                          (Prims.of_int (251))
                                          (Prims.of_int (9))))))
                              (FStar_Range.prims_to_fstar_range
                                 (Prims.mk_range "FStar.Tactics.Logic.fst"
                                    (Prims.of_int (249)) (Prims.of_int (10))
                                    (Prims.of_int (249)) (Prims.of_int (18))))))
                with
                | FStar_Tactics_Result.Success (a1,ps'1) ->
                    (match () with
                     | () ->
                         (match (FStar_Tactics_Builtins.intro ())
                                  (FStar_Tactics_Types.incr_depth
                                     (FStar_Tactics_Types.set_proofstate_range
                                        (FStar_Tactics_Types.decr_depth
                                           (FStar_Tactics_Types.set_proofstate_range
                                              ps'1
                                              (FStar_Range.prims_to_fstar_range
                                                 (Prims.mk_range
                                                    "FStar.Tactics.Logic.fst"
                                                    (Prims.of_int (250))
                                                    (Prims.of_int (2))
                                                    (Prims.of_int (251))
                                                    (Prims.of_int (9))))))
                                        (FStar_Range.prims_to_fstar_range
                                           (Prims.mk_range
                                              "FStar.Tactics.Logic.fst"
                                              (Prims.of_int (250))
                                              (Prims.of_int (11))
                                              (Prims.of_int (250))
                                              (Prims.of_int (19))))))
                          with
                          | FStar_Tactics_Result.Success (a2,ps'2) ->
                              (match () with
                               | () ->
                                   FStar_Tactics_Result.Success
                                     ((a1, a2),
                                       (FStar_Tactics_Types.decr_depth
                                          (FStar_Tactics_Types.set_proofstate_range
                                             ps'2
                                             (FStar_Range.prims_to_fstar_range
                                                (Prims.mk_range
                                                   "FStar.Tactics.Logic.fst"
                                                   (Prims.of_int (251))
                                                   (Prims.of_int (2))
                                                   (Prims.of_int (251))
                                                   (Prims.of_int (9))))))))
                          | FStar_Tactics_Result.Failed (e,ps'2) ->
                              FStar_Tactics_Result.Failed (e, ps'2)))
                | FStar_Tactics_Result.Failed (e,ps'1) ->
                    FStar_Tactics_Result.Failed (e, ps'1)))
      | FStar_Tactics_Result.Failed (e,ps') ->
          FStar_Tactics_Result.Failed (e, ps')
  


let (instantiate :
  FStar_Reflection_Types.term ->
    FStar_Reflection_Types.term ->
      (FStar_Reflection_Types.binder,unit)
        FStar_Tactics_Effect._dm4f_TAC_repr)
  =
  fun fa  ->
    fun x  ->
      FStar_Tactics_Derived.try_with
        (fun uu___276_3747  ->
           match () with
           | () ->
               FStar_Tactics_Derived.pose
                 (FStar_Reflection_Basic.pack_ln
                    (FStar_Reflection_Data.Tv_App
                       ((FStar_Reflection_Basic.pack_ln
                           (FStar_Reflection_Data.Tv_App
                              ((FStar_Reflection_Basic.pack_ln
                                  (FStar_Reflection_Data.Tv_FVar
                                     (FStar_Reflection_Basic.pack_fv
                                        ["FStar";
                                        "Tactics";
                                        "Logic";
                                        "__forall_inst_sq"]))),
                                (fa, FStar_Reflection_Data.Q_Explicit)))),
                         (x, FStar_Reflection_Data.Q_Explicit)))))
        (fun uu___275_3758  ->
           FStar_Tactics_Derived.try_with
             (fun uu___280_3766  ->
                match () with
                | () ->
                    FStar_Tactics_Derived.pose
                      (FStar_Reflection_Basic.pack_ln
                         (FStar_Reflection_Data.Tv_App
                            ((FStar_Reflection_Basic.pack_ln
                                (FStar_Reflection_Data.Tv_App
                                   ((FStar_Reflection_Basic.pack_ln
                                       (FStar_Reflection_Data.Tv_FVar
                                          (FStar_Reflection_Basic.pack_fv
                                             ["FStar";
                                             "Tactics";
                                             "Logic";
                                             "__forall_inst"]))),
                                     (fa, FStar_Reflection_Data.Q_Explicit)))),
                              (x, FStar_Reflection_Data.Q_Explicit)))))
             (fun uu___279_3777  ->
                FStar_Tactics_Derived.fail "could not instantiate"))
  

let rec (sk_binder' :
  FStar_Reflection_Types.binders ->
    FStar_Reflection_Types.binder ->
      ((FStar_Reflection_Types.binders * FStar_Reflection_Types.binder),
        unit) FStar_Tactics_Effect._dm4f_TAC_repr)
  =
  fun acc  ->
    fun b  ->
      FStar_Tactics_Derived.focus
        (fun uu____3876  ->
           FStar_Tactics_Derived.try_with
             (fun uu___302_3923  ->
                match () with
                | () ->
                    (fun ps  ->
                       match match match (FStar_Tactics_Derived.binder_to_term
                                            b)
                                           (FStar_Tactics_Types.incr_depth
                                              (FStar_Tactics_Types.set_proofstate_range
                                                 (FStar_Tactics_Types.incr_depth
                                                    (FStar_Tactics_Types.set_proofstate_range
                                                       (FStar_Tactics_Types.incr_depth
                                                          (FStar_Tactics_Types.set_proofstate_range
                                                             ps
                                                             (FStar_Range.prims_to_fstar_range
                                                                (Prims.mk_range
                                                                   "FStar.Tactics.Logic.fst"
                                                                   (Prims.of_int (276))
                                                                   (Prims.of_int (6))
                                                                   (Prims.of_int (276))
                                                                   (Prims.of_int (52))))))
                                                       (FStar_Range.prims_to_fstar_range
                                                          (Prims.mk_range
                                                             "FStar.Tactics.Logic.fst"
                                                             (Prims.of_int (276))
                                                             (Prims.of_int (18))
                                                             (Prims.of_int (276))
                                                             (Prims.of_int (52))))))
                                                 (FStar_Range.prims_to_fstar_range
                                                    (Prims.mk_range
                                                       "FStar.Tactics.Logic.fst"
                                                       (Prims.of_int (276))
                                                       (Prims.of_int (31))
                                                       (Prims.of_int (276))
                                                       (Prims.of_int (49))))))
                                   with
                                   | FStar_Tactics_Result.Success (a,ps') ->
                                       (match () with
                                        | () ->
                                            FStar_Tactics_Result.Success
                                              ((FStar_Reflection_Basic.pack_ln
                                                  (FStar_Reflection_Data.Tv_App
                                                     ((FStar_Reflection_Basic.pack_ln
                                                         (FStar_Reflection_Data.Tv_FVar
                                                            (FStar_Reflection_Basic.pack_fv
                                                               ["FStar";
                                                               "Tactics";
                                                               "Logic";
                                                               "sklem0"]))),
                                                       (a,
                                                         FStar_Reflection_Data.Q_Explicit)))),
                                                (FStar_Tactics_Types.decr_depth
                                                   (FStar_Tactics_Types.set_proofstate_range
                                                      ps'
                                                      (FStar_Range.prims_to_fstar_range
                                                         (Prims.mk_range
                                                            "FStar.Tactics.Logic.fst"
                                                            (Prims.of_int (276))
                                                            (Prims.of_int (18))
                                                            (Prims.of_int (276))
                                                            (Prims.of_int (52))))))))
                                   | FStar_Tactics_Result.Failed (e,ps') ->
                                       FStar_Tactics_Result.Failed (e, ps')
                             with
                             | FStar_Tactics_Result.Success (a,ps') ->
                                 (match () with
                                  | () ->
                                      (FStar_Tactics_Builtins.apply_lemma a)
                                        (FStar_Tactics_Types.decr_depth
                                           (FStar_Tactics_Types.set_proofstate_range
                                              ps'
                                              (FStar_Range.prims_to_fstar_range
                                                 (Prims.mk_range
                                                    "FStar.Tactics.Logic.fst"
                                                    (Prims.of_int (276))
                                                    (Prims.of_int (6))
                                                    (Prims.of_int (276))
                                                    (Prims.of_int (52)))))))
                             | FStar_Tactics_Result.Failed (e,ps') ->
                                 FStar_Tactics_Result.Failed (e, ps')
                       with
                       | FStar_Tactics_Result.Success (a,ps') ->
                           (match () with
                            | () ->
                                (match match match (FStar_Tactics_Derived.ngoals
                                                      ())
                                                     (FStar_Tactics_Types.incr_depth
                                                        (FStar_Tactics_Types.set_proofstate_range
                                                           (FStar_Tactics_Types.incr_depth
                                                              (FStar_Tactics_Types.set_proofstate_range
                                                                 (FStar_Tactics_Types.incr_depth
                                                                    (
                                                                    FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Logic.fst"
                                                                    (Prims.of_int (277))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (281))
                                                                    (Prims.of_int (29))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Logic.fst"
                                                                    (Prims.of_int (277))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (277))
                                                                    (Prims.of_int (38))))))
                                                                 (FStar_Range.prims_to_fstar_range
                                                                    (
                                                                    Prims.mk_range
                                                                    "FStar.Tactics.Logic.fst"
                                                                    (Prims.of_int (277))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (277))
                                                                    (Prims.of_int (23))))))
                                                           (FStar_Range.prims_to_fstar_range
                                                              (Prims.mk_range
                                                                 "FStar.Tactics.Logic.fst"
                                                                 (Prims.of_int (277))
                                                                 (Prims.of_int (9))
                                                                 (Prims.of_int (277))
                                                                 (Prims.of_int (18))))))
                                             with
                                             | FStar_Tactics_Result.Success
                                                 (a1,ps'1) ->
                                                 (match () with
                                                  | () ->
                                                      FStar_Tactics_Result.Success
                                                        ((a1 <> Prims.int_one),
                                                          (FStar_Tactics_Types.decr_depth
                                                             (FStar_Tactics_Types.set_proofstate_range
                                                                ps'1
                                                                (FStar_Range.prims_to_fstar_range
                                                                   (Prims.mk_range
                                                                    "FStar.Tactics.Logic.fst"
                                                                    (Prims.of_int (277))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (277))
                                                                    (Prims.of_int (23))))))))
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
                                                   FStar_Tactics_Derived.fail
                                                     "no"
                                                 else
                                                   (fun s  ->
                                                      FStar_Tactics_Result.Success
                                                        ((), s)))
                                                  (FStar_Tactics_Types.decr_depth
                                                     (FStar_Tactics_Types.set_proofstate_range
                                                        ps'1
                                                        (FStar_Range.prims_to_fstar_range
                                                           (Prims.mk_range
                                                              "FStar.Tactics.Logic.fst"
                                                              (Prims.of_int (277))
                                                              (Prims.of_int (6))
                                                              (Prims.of_int (277))
                                                              (Prims.of_int (38)))))))
                                       | FStar_Tactics_Result.Failed 
                                           (e,ps'1) ->
                                           FStar_Tactics_Result.Failed
                                             (e, ps'1)
                                 with
                                 | FStar_Tactics_Result.Success (a1,ps'1) ->
                                     (match () with
                                      | () ->
                                          (match (FStar_Tactics_Builtins.clear
                                                    b)
                                                   (FStar_Tactics_Types.incr_depth
                                                      (FStar_Tactics_Types.set_proofstate_range
                                                         (FStar_Tactics_Types.decr_depth
                                                            (FStar_Tactics_Types.set_proofstate_range
                                                               ps'1
                                                               (FStar_Range.prims_to_fstar_range
                                                                  (Prims.mk_range
                                                                    "FStar.Tactics.Logic.fst"
                                                                    (Prims.of_int (278))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (281))
                                                                    (Prims.of_int (29))))))
                                                         (FStar_Range.prims_to_fstar_range
                                                            (Prims.mk_range
                                                               "FStar.Tactics.Logic.fst"
                                                               (Prims.of_int (278))
                                                               (Prims.of_int (6))
                                                               (Prims.of_int (278))
                                                               (Prims.of_int (13))))))
                                           with
                                           | FStar_Tactics_Result.Success
                                               (a2,ps'2) ->
                                               (match () with
                                                | () ->
                                                    (match (forall_intro ())
                                                             (FStar_Tactics_Types.incr_depth
                                                                (FStar_Tactics_Types.set_proofstate_range
                                                                   (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Logic.fst"
                                                                    (Prims.of_int (279))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (281))
                                                                    (Prims.of_int (29))))))
                                                                   (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Logic.fst"
                                                                    (Prims.of_int (279))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (279))
                                                                    (Prims.of_int (30))))))
                                                     with
                                                     | FStar_Tactics_Result.Success
                                                         (a3,ps'3) ->
                                                         (match () with
                                                          | () ->
                                                              (match 
                                                                 (implies_intro
                                                                    ())
                                                                   (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Logic.fst"
                                                                    (Prims.of_int (280))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (281))
                                                                    (Prims.of_int (29))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Logic.fst"
                                                                    (Prims.of_int (280))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (280))
                                                                    (Prims.of_int (31))))))
                                                               with
                                                               | FStar_Tactics_Result.Success
                                                                   (a4,ps'4)
                                                                   ->
                                                                   (match ()
                                                                    with
                                                                    | 
                                                                    () ->
                                                                    (sk_binder'
                                                                    (a3 ::
                                                                    acc) a4)
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'4
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Logic.fst"
                                                                    (Prims.of_int (281))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (281))
                                                                    (Prims.of_int (29)))))))
                                                               | FStar_Tactics_Result.Failed
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
                                                 (e, ps'2)))
                                 | FStar_Tactics_Result.Failed (e,ps'1) ->
                                     FStar_Tactics_Result.Failed (e, ps'1)))
                       | FStar_Tactics_Result.Failed (e,ps') ->
                           FStar_Tactics_Result.Failed (e, ps')))
             (fun uu___301_4266  ->
                fun s  -> FStar_Tactics_Result.Success ((acc, b), s)))
  
let (sk_binder :
  FStar_Reflection_Types.binder ->
    ((FStar_Reflection_Types.binders * FStar_Reflection_Types.binder),
      unit) FStar_Tactics_Effect._dm4f_TAC_repr)
  = fun b  -> sk_binder' [] b 
let (skolem :
  unit ->
    ((FStar_Reflection_Types.binders * FStar_Reflection_Types.binder)
       Prims.list,unit)
      FStar_Tactics_Effect._dm4f_TAC_repr)
  =
  fun uu____4356  ->
    fun ps  ->
      match match (FStar_Tactics_Derived.cur_env ())
                    (FStar_Tactics_Types.incr_depth
                       (FStar_Tactics_Types.set_proofstate_range
                          (FStar_Tactics_Types.incr_depth
                             (FStar_Tactics_Types.set_proofstate_range ps
                                (FStar_Range.prims_to_fstar_range
                                   (Prims.mk_range "FStar.Tactics.Logic.fst"
                                      (Prims.of_int (290))
                                      (Prims.of_int (11))
                                      (Prims.of_int (290))
                                      (Prims.of_int (38))))))
                          (FStar_Range.prims_to_fstar_range
                             (Prims.mk_range "FStar.Tactics.Logic.fst"
                                (Prims.of_int (290)) (Prims.of_int (26))
                                (Prims.of_int (290)) (Prims.of_int (38))))))
            with
            | FStar_Tactics_Result.Success (a,ps') ->
                (match () with
                 | () ->
                     FStar_Tactics_Result.Success
                       ((FStar_Reflection_Basic.binders_of_env a),
                         (FStar_Tactics_Types.decr_depth
                            (FStar_Tactics_Types.set_proofstate_range ps'
                               (FStar_Range.prims_to_fstar_range
                                  (Prims.mk_range "FStar.Tactics.Logic.fst"
                                     (Prims.of_int (290)) (Prims.of_int (11))
                                     (Prims.of_int (290)) (Prims.of_int (38))))))))
            | FStar_Tactics_Result.Failed (e,ps') ->
                FStar_Tactics_Result.Failed (e, ps')
      with
      | FStar_Tactics_Result.Success (a,ps') ->
          (match () with
           | () ->
               (FStar_Tactics_Util.map sk_binder a)
                 (FStar_Tactics_Types.decr_depth
                    (FStar_Tactics_Types.set_proofstate_range ps'
                       (FStar_Range.prims_to_fstar_range
                          (Prims.mk_range "FStar.Tactics.Logic.fst"
                             (Prims.of_int (291)) (Prims.of_int (2))
                             (Prims.of_int (291)) (Prims.of_int (18)))))))
      | FStar_Tactics_Result.Failed (e,ps') ->
          FStar_Tactics_Result.Failed (e, ps')
  