open Prims

let rec first :
  'a 'b .
    ('a -> ('b,unit) FStar_Tactics_Effect._dm4f_TAC_repr) ->
      'a Prims.list -> ('b,unit) FStar_Tactics_Effect._dm4f_TAC_repr
  =
  fun f  ->
    fun l  ->
      match l with
      | [] -> FStar_Tactics_Derived.fail "no cands"
      | x::xs ->
          FStar_Tactics_Derived.or_else (fun uu____107  -> f x)
            (fun uu____109  -> first f xs)
  
let rec (tcresolve' :
  FStar_Reflection_Types.term Prims.list ->
    Prims.int -> (unit,unit) FStar_Tactics_Effect._dm4f_TAC_repr)
  =
  fun seen  ->
    fun fuel  ->
      fun ps  ->
        match (if fuel <= Prims.int_zero
               then FStar_Tactics_Derived.fail "out of fuel"
               else (fun s  -> FStar_Tactics_Result.Success ((), s)))
                (FStar_Tactics_Types.incr_depth
                   (FStar_Tactics_Types.set_proofstate_range ps
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range "FStar.Tactics.Typeclasses.fst"
                            (Prims.of_int (36)) (Prims.of_int (4))
                            (Prims.of_int (37)) (Prims.of_int (26))))))
        with
        | FStar_Tactics_Result.Success (a,ps') ->
            (match () with
             | () ->
                 (match (FStar_Tactics_Derived.debug
                           (Prims.strcat "fuel = " (Prims.string_of_int fuel)))
                          (FStar_Tactics_Types.incr_depth
                             (FStar_Tactics_Types.set_proofstate_range
                                (FStar_Tactics_Types.decr_depth
                                   (FStar_Tactics_Types.set_proofstate_range
                                      ps'
                                      (FStar_Range.prims_to_fstar_range
                                         (Prims.mk_range
                                            "FStar.Tactics.Typeclasses.fst"
                                            (Prims.of_int (38))
                                            (Prims.of_int (4))
                                            (Prims.of_int (43))
                                            (Prims.of_int (137))))))
                                (FStar_Range.prims_to_fstar_range
                                   (Prims.mk_range
                                      "FStar.Tactics.Typeclasses.fst"
                                      (Prims.of_int (38)) (Prims.of_int (4))
                                      (Prims.of_int (38)) (Prims.of_int (42))))))
                  with
                  | FStar_Tactics_Result.Success (a1,ps'1) ->
                      (match () with
                       | () ->
                           (match (FStar_Tactics_Derived.cur_goal ())
                                    (FStar_Tactics_Types.incr_depth
                                       (FStar_Tactics_Types.set_proofstate_range
                                          (FStar_Tactics_Types.decr_depth
                                             (FStar_Tactics_Types.set_proofstate_range
                                                ps'1
                                                (FStar_Range.prims_to_fstar_range
                                                   (Prims.mk_range
                                                      "FStar.Tactics.Typeclasses.fst"
                                                      (Prims.of_int (39))
                                                      (Prims.of_int (4))
                                                      (Prims.of_int (43))
                                                      (Prims.of_int (137))))))
                                          (FStar_Range.prims_to_fstar_range
                                             (Prims.mk_range
                                                "FStar.Tactics.Typeclasses.fst"
                                                (Prims.of_int (39))
                                                (Prims.of_int (12))
                                                (Prims.of_int (39))
                                                (Prims.of_int (23))))))
                            with
                            | FStar_Tactics_Result.Success (a2,ps'2) ->
                                (match () with
                                 | () ->
                                     (match (if
                                               FStar_List_Tot_Base.existsb
                                                 (FStar_Reflection_Basic.term_eq
                                                    a2) seen
                                             then
                                               FStar_Tactics_Derived.fail
                                                 "loop"
                                             else
                                               (fun s  ->
                                                  FStar_Tactics_Result.Success
                                                    ((), s)))
                                              (FStar_Tactics_Types.incr_depth
                                                 (FStar_Tactics_Types.set_proofstate_range
                                                    (FStar_Tactics_Types.decr_depth
                                                       (FStar_Tactics_Types.set_proofstate_range
                                                          ps'2
                                                          (FStar_Range.prims_to_fstar_range
                                                             (Prims.mk_range
                                                                "FStar.Tactics.Typeclasses.fst"
                                                                (Prims.of_int (40))
                                                                (Prims.of_int (4))
                                                                (Prims.of_int (43))
                                                                (Prims.of_int (137))))))
                                                    (FStar_Range.prims_to_fstar_range
                                                       (Prims.mk_range
                                                          "FStar.Tactics.Typeclasses.fst"
                                                          (Prims.of_int (40))
                                                          (Prims.of_int (4))
                                                          (Prims.of_int (41))
                                                          (Prims.of_int (17))))))
                                      with
                                      | FStar_Tactics_Result.Success
                                          (a3,ps'3) ->
                                          (match () with
                                           | () ->
                                               (match () with
                                                | () ->
                                                    (FStar_Tactics_Derived.or_else
                                                       (local (a2 :: seen)
                                                          fuel)
                                                       (fun uu____443  ->
                                                          FStar_Tactics_Derived.or_else
                                                            (global (a2 ::
                                                               seen) fuel)
                                                            (fun uu____448 
                                                               ->
                                                               FStar_Tactics_Derived.fail
                                                                 (Prims.strcat
                                                                    "could not solve constraint: "
                                                                    (
                                                                    FStar_Reflection_Basic.term_to_string
                                                                    a2)))))
                                                      (FStar_Tactics_Types.decr_depth
                                                         (FStar_Tactics_Types.set_proofstate_range
                                                            (FStar_Tactics_Types.incr_depth
                                                               (FStar_Tactics_Types.set_proofstate_range
                                                                  (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (42))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (43))
                                                                    (Prims.of_int (137))))))
                                                                  (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (42))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (42))
                                                                    (Prims.of_int (19))))))
                                                            (FStar_Range.prims_to_fstar_range
                                                               (Prims.mk_range
                                                                  "FStar.Tactics.Typeclasses.fst"
                                                                  (Prims.of_int (43))
                                                                  (Prims.of_int (4))
                                                                  (Prims.of_int (43))
                                                                  (Prims.of_int (137))))))))
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

and (local :
  FStar_Reflection_Types.term Prims.list ->
    Prims.int -> unit -> (unit,unit) FStar_Tactics_Effect._dm4f_TAC_repr)
  =
  fun seen  ->
    fun fuel  ->
      fun uu____460  ->
        fun ps  ->
          match match (FStar_Tactics_Derived.cur_env ())
                        (FStar_Tactics_Types.incr_depth
                           (FStar_Tactics_Types.set_proofstate_range
                              (FStar_Tactics_Types.incr_depth
                                 (FStar_Tactics_Types.set_proofstate_range ps
                                    (FStar_Range.prims_to_fstar_range
                                       (Prims.mk_range
                                          "FStar.Tactics.Typeclasses.fst"
                                          (Prims.of_int (45))
                                          (Prims.of_int (13))
                                          (Prims.of_int (45))
                                          (Prims.of_int (40))))))
                              (FStar_Range.prims_to_fstar_range
                                 (Prims.mk_range
                                    "FStar.Tactics.Typeclasses.fst"
                                    (Prims.of_int (45)) (Prims.of_int (28))
                                    (Prims.of_int (45)) (Prims.of_int (40))))))
                with
                | FStar_Tactics_Result.Success (a,ps') ->
                    (match () with
                     | () ->
                         FStar_Tactics_Result.Success
                           ((FStar_Reflection_Basic.binders_of_env a),
                             (FStar_Tactics_Types.decr_depth
                                (FStar_Tactics_Types.set_proofstate_range ps'
                                   (FStar_Range.prims_to_fstar_range
                                      (Prims.mk_range
                                         "FStar.Tactics.Typeclasses.fst"
                                         (Prims.of_int (45))
                                         (Prims.of_int (13))
                                         (Prims.of_int (45))
                                         (Prims.of_int (40))))))))
                | FStar_Tactics_Result.Failed (e,ps') ->
                    FStar_Tactics_Result.Failed (e, ps')
          with
          | FStar_Tactics_Result.Success (a,ps') ->
              (match () with
               | () ->
                   (first
                      (fun b  ->
                         fun ps1  ->
                           match (FStar_Tactics_Builtins.pack
                                    (FStar_Reflection_Data.Tv_Var
                                       (FStar_Reflection_Derived.bv_of_binder
                                          b)))
                                   (FStar_Tactics_Types.incr_depth
                                      (FStar_Tactics_Types.set_proofstate_range
                                         ps1
                                         (FStar_Range.prims_to_fstar_range
                                            (Prims.mk_range
                                               "FStar.Tactics.Typeclasses.fst"
                                               (Prims.of_int (46))
                                               (Prims.of_int (38))
                                               (Prims.of_int (46))
                                               (Prims.of_int (70))))))
                           with
                           | FStar_Tactics_Result.Success (a1,ps'1) ->
                               (match () with
                                | () ->
                                    (trywith seen fuel a1)
                                      (FStar_Tactics_Types.decr_depth
                                         (FStar_Tactics_Types.set_proofstate_range
                                            ps'1
                                            (FStar_Range.prims_to_fstar_range
                                               (Prims.mk_range
                                                  "FStar.Tactics.Typeclasses.fst"
                                                  (Prims.of_int (46))
                                                  (Prims.of_int (20))
                                                  (Prims.of_int (46))
                                                  (Prims.of_int (70)))))))
                           | FStar_Tactics_Result.Failed (e,ps'1) ->
                               FStar_Tactics_Result.Failed (e, ps'1)) a)
                     (FStar_Tactics_Types.decr_depth
                        (FStar_Tactics_Types.set_proofstate_range ps'
                           (FStar_Range.prims_to_fstar_range
                              (Prims.mk_range "FStar.Tactics.Typeclasses.fst"
                                 (Prims.of_int (46)) (Prims.of_int (4))
                                 (Prims.of_int (46)) (Prims.of_int (74)))))))
          | FStar_Tactics_Result.Failed (e,ps') ->
              FStar_Tactics_Result.Failed (e, ps')

and (global :
  FStar_Reflection_Types.term Prims.list ->
    Prims.int -> unit -> (unit,unit) FStar_Tactics_Effect._dm4f_TAC_repr)
  =
  fun seen  ->
    fun fuel  ->
      fun uu____582  ->
        fun ps  ->
          match match (FStar_Tactics_Derived.cur_env ())
                        (FStar_Tactics_Types.incr_depth
                           (FStar_Tactics_Types.set_proofstate_range
                              (FStar_Tactics_Types.incr_depth
                                 (FStar_Tactics_Types.set_proofstate_range ps
                                    (FStar_Range.prims_to_fstar_range
                                       (Prims.mk_range
                                          "FStar.Tactics.Typeclasses.fst"
                                          (Prims.of_int (48))
                                          (Prims.of_int (16))
                                          (Prims.of_int (48))
                                          (Prims.of_int (54))))))
                              (FStar_Range.prims_to_fstar_range
                                 (Prims.mk_range
                                    "FStar.Tactics.Typeclasses.fst"
                                    (Prims.of_int (48)) (Prims.of_int (42))
                                    (Prims.of_int (48)) (Prims.of_int (54))))))
                with
                | FStar_Tactics_Result.Success (a,ps') ->
                    (match () with
                     | () ->
                         FStar_Tactics_Result.Success
                           ((FStar_Reflection_Basic.lookup_attr
                               (FStar_Reflection_Basic.pack_ln
                                  (FStar_Reflection_Data.Tv_FVar
                                     (FStar_Reflection_Basic.pack_fv
                                        ["FStar";
                                        "Tactics";
                                        "Typeclasses";
                                        "tcinstance"]))) a),
                             (FStar_Tactics_Types.decr_depth
                                (FStar_Tactics_Types.set_proofstate_range ps'
                                   (FStar_Range.prims_to_fstar_range
                                      (Prims.mk_range
                                         "FStar.Tactics.Typeclasses.fst"
                                         (Prims.of_int (48))
                                         (Prims.of_int (16))
                                         (Prims.of_int (48))
                                         (Prims.of_int (54))))))))
                | FStar_Tactics_Result.Failed (e,ps') ->
                    FStar_Tactics_Result.Failed (e, ps')
          with
          | FStar_Tactics_Result.Success (a,ps') ->
              (match () with
               | () ->
                   (first
                      (fun fv  ->
                         fun ps1  ->
                           match (FStar_Tactics_Builtins.pack
                                    (FStar_Reflection_Data.Tv_FVar fv))
                                   (FStar_Tactics_Types.incr_depth
                                      (FStar_Tactics_Types.set_proofstate_range
                                         ps1
                                         (FStar_Range.prims_to_fstar_range
                                            (Prims.mk_range
                                               "FStar.Tactics.Typeclasses.fst"
                                               (Prims.of_int (49))
                                               (Prims.of_int (39))
                                               (Prims.of_int (49))
                                               (Prims.of_int (58))))))
                           with
                           | FStar_Tactics_Result.Success (a1,ps'1) ->
                               (match () with
                                | () ->
                                    (trywith seen fuel a1)
                                      (FStar_Tactics_Types.decr_depth
                                         (FStar_Tactics_Types.set_proofstate_range
                                            ps'1
                                            (FStar_Range.prims_to_fstar_range
                                               (Prims.mk_range
                                                  "FStar.Tactics.Typeclasses.fst"
                                                  (Prims.of_int (49))
                                                  (Prims.of_int (21))
                                                  (Prims.of_int (49))
                                                  (Prims.of_int (58)))))))
                           | FStar_Tactics_Result.Failed (e,ps'1) ->
                               FStar_Tactics_Result.Failed (e, ps'1)) a)
                     (FStar_Tactics_Types.decr_depth
                        (FStar_Tactics_Types.set_proofstate_range ps'
                           (FStar_Range.prims_to_fstar_range
                              (Prims.mk_range "FStar.Tactics.Typeclasses.fst"
                                 (Prims.of_int (49)) (Prims.of_int (4))
                                 (Prims.of_int (49)) (Prims.of_int (65)))))))
          | FStar_Tactics_Result.Failed (e,ps') ->
              FStar_Tactics_Result.Failed (e, ps')

and (trywith :
  FStar_Reflection_Types.term Prims.list ->
    Prims.int ->
      FStar_Reflection_Types.term ->
        (unit,unit) FStar_Tactics_Effect._dm4f_TAC_repr)
  =
  fun seen  ->
    fun fuel  ->
      fun t  ->
        fun ps  ->
          match (FStar_Tactics_Derived.debug
                   (Prims.strcat "Trying to apply hypothesis/instance: "
                      (FStar_Reflection_Basic.term_to_string t)))
                  (FStar_Tactics_Types.incr_depth
                     (FStar_Tactics_Types.set_proofstate_range ps
                        (FStar_Range.prims_to_fstar_range
                           (Prims.mk_range "FStar.Tactics.Typeclasses.fst"
                              (Prims.of_int (51)) (Prims.of_int (4))
                              (Prims.of_int (51)) (Prims.of_int (70))))))
          with
          | FStar_Tactics_Result.Success (a,ps') ->
              (match () with
               | () ->
                   (FStar_Tactics_Derived.seq
                      (fun uu____790  -> FStar_Tactics_Derived.apply_noinst t)
                      (fun uu____792  ->
                         tcresolve' seen (fuel - Prims.int_one)))
                     (FStar_Tactics_Types.decr_depth
                        (FStar_Tactics_Types.set_proofstate_range ps'
                           (FStar_Range.prims_to_fstar_range
                              (Prims.mk_range "FStar.Tactics.Typeclasses.fst"
                                 (Prims.of_int (52)) (Prims.of_int (4))
                                 (Prims.of_int (52)) (Prims.of_int (73)))))))
          | FStar_Tactics_Result.Failed (e,ps') ->
              FStar_Tactics_Result.Failed (e, ps')

let (tcresolve : unit -> (unit,unit) FStar_Tactics_Effect._dm4f_TAC_repr) =
  fun uu____822  ->
    FStar_Tactics_Derived.try_with
      (fun uu___39_836  ->
         match () with | () -> tcresolve' [] (Prims.of_int (16)))
      (fun uu___38_840  ->
         match uu___38_840 with
         | FStar_Tactics_Types.TacticFailure s ->
             FStar_Tactics_Derived.fail
               (Prims.strcat "Typeclass resolution failed: " s)
         | e -> FStar_Tactics_Effect.raise e)
  
let _ =
  FStar_Tactics_Native.register_tactic "FStar.Tactics.Typeclasses.tcresolve"
    (Prims.of_int (2))
    (fun psc  ->
       fun ncb  ->
         fun args  ->
           FStar_Tactics_InterpFuns.mk_tactic_interpretation_1
             (FStar_Tactics_Native.from_tactic_1 tcresolve)
             FStar_Syntax_Embeddings.e_unit FStar_Syntax_Embeddings.e_unit
             psc ncb args)
  
let solve : 'Aa . 'Aa -> 'Aa = fun ev  -> ev 
let rec (mk_abs :
  FStar_Reflection_Types.binder Prims.list ->
    FStar_Reflection_Types.term ->
      (FStar_Reflection_Types.term,unit) FStar_Tactics_Effect._dm4f_TAC_repr)
  =
  fun bs  ->
    fun body  ->
      match bs with
      | [] -> (fun s  -> FStar_Tactics_Result.Success (body, s))
      | b::bs1 ->
          (fun ps  ->
             match match (mk_abs bs1 body)
                           (FStar_Tactics_Types.incr_depth
                              (FStar_Tactics_Types.set_proofstate_range
                                 (FStar_Tactics_Types.incr_depth
                                    (FStar_Tactics_Types.set_proofstate_range
                                       ps
                                       (FStar_Range.prims_to_fstar_range
                                          (Prims.mk_range
                                             "FStar.Tactics.Typeclasses.fst"
                                             (Prims.of_int (70))
                                             (Prims.of_int (20))
                                             (Prims.of_int (70))
                                             (Prims.of_int (47))))))
                                 (FStar_Range.prims_to_fstar_range
                                    (Prims.mk_range
                                       "FStar.Tactics.Typeclasses.fst"
                                       (Prims.of_int (70))
                                       (Prims.of_int (30))
                                       (Prims.of_int (70))
                                       (Prims.of_int (46))))))
                   with
                   | FStar_Tactics_Result.Success (a,ps') ->
                       (match () with
                        | () ->
                            FStar_Tactics_Result.Success
                              ((FStar_Reflection_Data.Tv_Abs (b, a)),
                                (FStar_Tactics_Types.decr_depth
                                   (FStar_Tactics_Types.set_proofstate_range
                                      ps'
                                      (FStar_Range.prims_to_fstar_range
                                         (Prims.mk_range
                                            "FStar.Tactics.Typeclasses.fst"
                                            (Prims.of_int (70))
                                            (Prims.of_int (20))
                                            (Prims.of_int (70))
                                            (Prims.of_int (47))))))))
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
                                    "FStar.Tactics.Typeclasses.fst"
                                    (Prims.of_int (70)) (Prims.of_int (15))
                                    (Prims.of_int (70)) (Prims.of_int (47)))))))
             | FStar_Tactics_Result.Failed (e,ps') ->
                 FStar_Tactics_Result.Failed (e, ps'))
  
let rec last :
  'a . 'a Prims.list -> ('a,unit) FStar_Tactics_Effect._dm4f_TAC_repr =
  fun l  ->
    match l with
    | [] -> FStar_Tactics_Derived.fail "last: empty list"
    | x::[] -> (fun s  -> FStar_Tactics_Result.Success (x, s))
    | uu____1029::xs -> last xs
  
let (mk_class :
  Prims.string ->
    (FStar_Reflection_Data.decls,unit) FStar_Tactics_Effect._dm4f_TAC_repr)
  =
  fun nm  ->
    fun ps  ->
      match () with
      | () ->
          (match match (FStar_Tactics_Builtins.top_env ())
                         (FStar_Tactics_Types.incr_depth
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
                                                       "FStar.Tactics.Typeclasses.fst"
                                                       (Prims.of_int (80))
                                                       (Prims.of_int (13))
                                                       (Prims.of_int (80))
                                                       (Prims.of_int (34))))))
                                           (FStar_Range.prims_to_fstar_range
                                              (Prims.mk_range
                                                 "FStar.Tactics.Typeclasses.fst"
                                                 (Prims.of_int (81))
                                                 (Prims.of_int (4))
                                                 (Prims.of_int (136))
                                                 (Prims.of_int (8))))))
                                     (FStar_Range.prims_to_fstar_range
                                        (Prims.mk_range
                                           "FStar.Tactics.Typeclasses.fst"
                                           (Prims.of_int (81))
                                           (Prims.of_int (12))
                                           (Prims.of_int (81))
                                           (Prims.of_int (38))))))
                               (FStar_Range.prims_to_fstar_range
                                  (Prims.mk_range
                                     "FStar.Tactics.Typeclasses.fst"
                                     (Prims.of_int (81)) (Prims.of_int (23))
                                     (Prims.of_int (81)) (Prims.of_int (35))))))
                 with
                 | FStar_Tactics_Result.Success (a,ps') ->
                     (match () with
                      | () ->
                          FStar_Tactics_Result.Success
                            ((FStar_Reflection_Basic.lookup_typ a
                                (FStar_String.split [46] nm)),
                              (FStar_Tactics_Types.decr_depth
                                 (FStar_Tactics_Types.set_proofstate_range
                                    ps'
                                    (FStar_Range.prims_to_fstar_range
                                       (Prims.mk_range
                                          "FStar.Tactics.Typeclasses.fst"
                                          (Prims.of_int (81))
                                          (Prims.of_int (12))
                                          (Prims.of_int (81))
                                          (Prims.of_int (38))))))))
                 | FStar_Tactics_Result.Failed (e,ps') ->
                     FStar_Tactics_Result.Failed (e, ps')
           with
           | FStar_Tactics_Result.Success (a,ps') ->
               (match () with
                | () ->
                    (match (FStar_Tactics_Derived.guard
                              (FStar_Pervasives_Native.uu___is_Some a))
                             (FStar_Tactics_Types.incr_depth
                                (FStar_Tactics_Types.set_proofstate_range
                                   (FStar_Tactics_Types.decr_depth
                                      (FStar_Tactics_Types.set_proofstate_range
                                         ps'
                                         (FStar_Range.prims_to_fstar_range
                                            (Prims.mk_range
                                               "FStar.Tactics.Typeclasses.fst"
                                               (Prims.of_int (82))
                                               (Prims.of_int (4))
                                               (Prims.of_int (136))
                                               (Prims.of_int (8))))))
                                   (FStar_Range.prims_to_fstar_range
                                      (Prims.mk_range
                                         "FStar.Tactics.Typeclasses.fst"
                                         (Prims.of_int (82))
                                         (Prims.of_int (4))
                                         (Prims.of_int (82))
                                         (Prims.of_int (19))))))
                     with
                     | FStar_Tactics_Result.Success (a1,ps'1) ->
                         (match () with
                          | () ->
                              (match () with
                               | () ->
                                   ((match a with
                                     | FStar_Pervasives_Native.Some se ->
                                         (fun ps1  ->
                                            match () with
                                            | () ->
                                                (match (FStar_Tactics_Derived.guard
                                                          (FStar_Reflection_Data.uu___is_Sg_Inductive
                                                             (FStar_Reflection_Basic.inspect_sigelt
                                                                se)))
                                                         (FStar_Tactics_Types.incr_depth
                                                            (FStar_Tactics_Types.set_proofstate_range
                                                               (FStar_Tactics_Types.decr_depth
                                                                  (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps1
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (84))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (84))
                                                                    (Prims.of_int (30))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (85))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (136))
                                                                    (Prims.of_int (8))))))
                                                               (FStar_Range.prims_to_fstar_range
                                                                  (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (85))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (85))
                                                                    (Prims.of_int (28))))))
                                                 with
                                                 | FStar_Tactics_Result.Success
                                                     (a2,ps'2) ->
                                                     (match () with
                                                      | () ->
                                                          (match () with
                                                           | () ->
                                                               ((match 
                                                                   FStar_Reflection_Basic.inspect_sigelt
                                                                    se
                                                                 with
                                                                 | FStar_Reflection_Data.Sg_Inductive
                                                                    (name,us,params,ty,ctors)
                                                                    ->
                                                                    (fun ps2 
                                                                    ->
                                                                    match 
                                                                    (last
                                                                    name)
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (89))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (89))
                                                                    (Prims.of_int (29))))))
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
                                                                    (FStar_Tactics_Derived.guard
                                                                    ((FStar_List_Tot_Base.length
                                                                    ctors) =
                                                                    Prims.int_one))
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (91))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (136))
                                                                    (Prims.of_int (8))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (91))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (91))
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
                                                                    (match ()
                                                                    with
                                                                    | 
                                                                    () ->
                                                                    ((match ctors
                                                                    with
                                                                    | ctor::[]
                                                                    ->
                                                                    (fun ps3 
                                                                    ->
                                                                    match 
                                                                    match 
                                                                    (FStar_Tactics_Builtins.top_env
                                                                    ())
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (93))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (93))
                                                                    (Prims.of_int (40))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (93))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (93))
                                                                    (Prims.of_int (35))))))
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
                                                                    ((FStar_Reflection_Basic.lookup_typ
                                                                    a5 ctor),
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'5
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (93))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (93))
                                                                    (Prims.of_int (40))))))))
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
                                                                    (FStar_Tactics_Derived.guard
                                                                    (FStar_Pervasives_Native.uu___is_Some
                                                                    a5))
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'5
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (94))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (136))
                                                                    (Prims.of_int (8))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (94))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (94))
                                                                    (Prims.of_int (19))))))
                                                                    with
                                                                    | 
                                                                    FStar_Tactics_Result.Success
                                                                    (a6,ps'6)
                                                                    ->
                                                                    (match ()
                                                                    with
                                                                    | 
                                                                    () ->
                                                                    (match ()
                                                                    with
                                                                    | 
                                                                    () ->
                                                                    (match ()
                                                                    with
                                                                    | 
                                                                    () ->
                                                                    (match 
                                                                    (FStar_Tactics_Derived.guard
                                                                    (FStar_Reflection_Data.uu___is_Sg_Constructor
                                                                    (FStar_Reflection_Basic.inspect_sigelt
                                                                    (FStar_Pervasives_Native.__proj__Some__item__v
                                                                    a5))))
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
                                                                    ps'6
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (95))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (136))
                                                                    (Prims.of_int (8))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (95))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (95))
                                                                    (Prims.of_int (23))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (96))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (136))
                                                                    (Prims.of_int (8))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (96))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (96))
                                                                    (Prims.of_int (30))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (97))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (136))
                                                                    (Prims.of_int (8))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (97))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (97))
                                                                    (Prims.of_int (29))))))
                                                                    with
                                                                    | 
                                                                    FStar_Tactics_Result.Success
                                                                    (a7,ps'7)
                                                                    ->
                                                                    (match ()
                                                                    with
                                                                    | 
                                                                    () ->
                                                                    (match ()
                                                                    with
                                                                    | 
                                                                    () ->
                                                                    ((match 
                                                                    FStar_Reflection_Basic.inspect_sigelt
                                                                    (FStar_Pervasives_Native.__proj__Some__item__v
                                                                    a5)
                                                                    with
                                                                    | FStar_Reflection_Data.Sg_Constructor
                                                                    (uu____2899,ty1)
                                                                    ->
                                                                    (fun ps4 
                                                                    ->
                                                                    match 
                                                                    (FStar_Tactics_SyntaxHelpers.collect_arr_bs
                                                                    ty1)
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps4
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (100))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (100))
                                                                    (Prims.of_int (35))))))
                                                                    with
                                                                    | 
                                                                    FStar_Tactics_Result.Success
                                                                    (a8,ps'8)
                                                                    ->
                                                                    (match ()
                                                                    with
                                                                    | 
                                                                    () ->
                                                                    ((match a8
                                                                    with
                                                                    | (bs,cod)
                                                                    ->
                                                                    (fun ps5 
                                                                    ->
                                                                    match ()
                                                                    with
                                                                    | 
                                                                    () ->
                                                                    (match 
                                                                    (FStar_Tactics_Derived.guard
                                                                    (FStar_Reflection_Data.uu___is_C_Total
                                                                    (FStar_Reflection_Basic.inspect_comp
                                                                    cod)))
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps5
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (101))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (101))
                                                                    (Prims.of_int (28))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (102))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (136))
                                                                    (Prims.of_int (8))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (102))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (102))
                                                                    (Prims.of_int (22))))))
                                                                    with
                                                                    | 
                                                                    FStar_Tactics_Result.Success
                                                                    (a9,ps'9)
                                                                    ->
                                                                    (match ()
                                                                    with
                                                                    | 
                                                                    () ->
                                                                    (match ()
                                                                    with
                                                                    | 
                                                                    () ->
                                                                    ((match 
                                                                    FStar_Reflection_Basic.inspect_comp
                                                                    cod
                                                                    with
                                                                    | FStar_Reflection_Data.C_Total
                                                                    (cod1,uu____2980)
                                                                    ->
                                                                    (fun ps6 
                                                                    ->
                                                                    match ()
                                                                    with
                                                                    | 
                                                                    () ->
                                                                    ((match 
                                                                    FStar_List_Tot_Base.splitAt
                                                                    (FStar_List_Tot_Base.length
                                                                    params)
                                                                    bs
                                                                    with
                                                                    | (ps7,bs1)
                                                                    ->
                                                                    (fun ps8 
                                                                    ->
                                                                    match ()
                                                                    with
                                                                    | 
                                                                    () ->
                                                                    (FStar_Tactics_Util.map
                                                                    (fun b 
                                                                    ->
                                                                    fun ps9 
                                                                    ->
                                                                    match ()
                                                                    with
                                                                    | 
                                                                    () ->
                                                                    (match 
                                                                    (FStar_Tactics_Derived.cur_module
                                                                    ())
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps9
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (115))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (115))
                                                                    (Prims.of_int (42))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (117))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (135))
                                                                    (Prims.of_int (20))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (117))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (117))
                                                                    (Prims.of_int (40))))))
                                                                    with
                                                                    | 
                                                                    FStar_Tactics_Result.Success
                                                                    (a10,ps'10)
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
                                                                    (FStar_Tactics_Builtins.fresh_bv_named
                                                                    "d" cod1)
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'10
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (118))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (135))
                                                                    (Prims.of_int (20))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (118))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (118))
                                                                    (Prims.of_int (46))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (119))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (135))
                                                                    (Prims.of_int (20))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (119))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (119))
                                                                    (Prims.of_int (50))))))
                                                                    with
                                                                    | 
                                                                    FStar_Tactics_Result.Success
                                                                    (a11,ps'11)
                                                                    ->
                                                                    (match ()
                                                                    with
                                                                    | 
                                                                    () ->
                                                                    (match ()
                                                                    with
                                                                    | 
                                                                    () ->
                                                                    (match ()
                                                                    with
                                                                    | 
                                                                    () ->
                                                                    (match ()
                                                                    with
                                                                    | 
                                                                    () ->
                                                                    (match 
                                                                    (FStar_Tactics_Builtins.pack
                                                                    FStar_Reflection_Data.Tv_Unknown)
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
                                                                    ps'11
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (120))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (135))
                                                                    (Prims.of_int (20))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (120))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (120))
                                                                    (Prims.of_int (40))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (121))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (135))
                                                                    (Prims.of_int (20))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (121))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (121))
                                                                    (Prims.of_int (59))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (122))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (135))
                                                                    (Prims.of_int (20))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (122))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (122))
                                                                    (Prims.of_int (40))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (135))
                                                                    (Prims.of_int (20))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (42))))))
                                                                    with
                                                                    | 
                                                                    FStar_Tactics_Result.Success
                                                                    (a12,ps'12)
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
                                                                    (FStar_Tactics_Derived.cur_module
                                                                    ())
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
                                                                    ps'12
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (124))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (135))
                                                                    (Prims.of_int (20))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (124))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (124))
                                                                    (Prims.of_int (82))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (124))
                                                                    (Prims.of_int (34))
                                                                    (Prims.of_int (124))
                                                                    (Prims.of_int (82))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (124))
                                                                    (Prims.of_int (43))
                                                                    (Prims.of_int (124))
                                                                    (Prims.of_int (81))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (124))
                                                                    (Prims.of_int (52))
                                                                    (Prims.of_int (124))
                                                                    (Prims.of_int (80))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (124))
                                                                    (Prims.of_int (53))
                                                                    (Prims.of_int (124))
                                                                    (Prims.of_int (66))))))
                                                                    with
                                                                    | 
                                                                    FStar_Tactics_Result.Success
                                                                    (a13,ps'13)
                                                                    ->
                                                                    (match ()
                                                                    with
                                                                    | 
                                                                    () ->
                                                                    FStar_Tactics_Result.Success
                                                                    ((FStar_List_Tot_Base.append
                                                                    a13
                                                                    [
                                                                    Prims.strcat
                                                                    (Prims.strcat
                                                                    "__proj__Mk"
                                                                    (Prims.strcat
                                                                    a3
                                                                    "__item__"))
                                                                    (FStar_Reflection_Derived.name_of_binder
                                                                    b)]),
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'13
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (124))
                                                                    (Prims.of_int (52))
                                                                    (Prims.of_int (124))
                                                                    (Prims.of_int (80))))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e,ps'13)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e,
                                                                    ps'13)
                                                                    with
                                                                    | 
                                                                    FStar_Tactics_Result.Success
                                                                    (a13,ps'13)
                                                                    ->
                                                                    (match ()
                                                                    with
                                                                    | 
                                                                    () ->
                                                                    FStar_Tactics_Result.Success
                                                                    ((FStar_Reflection_Basic.pack_fv
                                                                    a13),
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'13
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (124))
                                                                    (Prims.of_int (43))
                                                                    (Prims.of_int (124))
                                                                    (Prims.of_int (81))))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e,ps'13)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e,
                                                                    ps'13)
                                                                    with
                                                                    | 
                                                                    FStar_Tactics_Result.Success
                                                                    (a13,ps'13)
                                                                    ->
                                                                    (match ()
                                                                    with
                                                                    | 
                                                                    () ->
                                                                    FStar_Tactics_Result.Success
                                                                    ((FStar_Reflection_Data.Tv_FVar
                                                                    a13),
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'13
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (124))
                                                                    (Prims.of_int (34))
                                                                    (Prims.of_int (124))
                                                                    (Prims.of_int (82))))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e,ps'13)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e,
                                                                    ps'13)
                                                                    with
                                                                    | 
                                                                    FStar_Tactics_Result.Success
                                                                    (a13,ps'13)
                                                                    ->
                                                                    (match ()
                                                                    with
                                                                    | 
                                                                    () ->
                                                                    (FStar_Tactics_Builtins.pack
                                                                    a13)
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'13
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (124))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (124))
                                                                    (Prims.of_int (82)))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e,ps'13)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e,
                                                                    ps'13)
                                                                    with
                                                                    | 
                                                                    FStar_Tactics_Result.Success
                                                                    (a13,ps'13)
                                                                    ->
                                                                    (match ()
                                                                    with
                                                                    | 
                                                                    () ->
                                                                    (match 
                                                                    match 
                                                                    match 
                                                                    match 
                                                                    (FStar_Tactics_Derived.binder_to_term
                                                                    (FStar_Reflection_Basic.pack_binder
                                                                    a11
                                                                    (FStar_Reflection_Data.Q_Meta
                                                                    (FStar_Reflection_Basic.pack_ln
                                                                    (FStar_Reflection_Data.Tv_FVar
                                                                    (FStar_Reflection_Basic.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "Typeclasses";
                                                                    "tcresolve"]))))))
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
                                                                    ps'13
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (125))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (135))
                                                                    (Prims.of_int (20))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (125))
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (125))
                                                                    (Prims.of_int (84))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (125))
                                                                    (Prims.of_int (45))
                                                                    (Prims.of_int (125))
                                                                    (Prims.of_int (84))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (125))
                                                                    (Prims.of_int (60))
                                                                    (Prims.of_int (125))
                                                                    (Prims.of_int (83))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (125))
                                                                    (Prims.of_int (61))
                                                                    (Prims.of_int (125))
                                                                    (Prims.of_int (82))))))
                                                                    with
                                                                    | 
                                                                    FStar_Tactics_Result.Success
                                                                    (a14,ps'14)
                                                                    ->
                                                                    (match ()
                                                                    with
                                                                    | 
                                                                    () ->
                                                                    FStar_Tactics_Result.Success
                                                                    ([a14],
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'14
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (125))
                                                                    (Prims.of_int (60))
                                                                    (Prims.of_int (125))
                                                                    (Prims.of_int (83))))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e,ps'14)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e,
                                                                    ps'14)
                                                                    with
                                                                    | 
                                                                    FStar_Tactics_Result.Success
                                                                    (a14,ps'14)
                                                                    ->
                                                                    (match ()
                                                                    with
                                                                    | 
                                                                    () ->
                                                                    FStar_Tactics_Result.Success
                                                                    ((FStar_Reflection_Derived.mk_e_app
                                                                    a13 a14),
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'14
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (125))
                                                                    (Prims.of_int (45))
                                                                    (Prims.of_int (125))
                                                                    (Prims.of_int (84))))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e,ps'14)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e,
                                                                    ps'14)
                                                                    with
                                                                    | 
                                                                    FStar_Tactics_Result.Success
                                                                    (a14,ps'14)
                                                                    ->
                                                                    (match ()
                                                                    with
                                                                    | 
                                                                    () ->
                                                                    (mk_abs
                                                                    (FStar_List_Tot_Base.append
                                                                    ps7
                                                                    [
                                                                    FStar_Reflection_Basic.pack_binder
                                                                    a11
                                                                    (FStar_Reflection_Data.Q_Meta
                                                                    (FStar_Reflection_Basic.pack_ln
                                                                    (FStar_Reflection_Data.Tv_FVar
                                                                    (FStar_Reflection_Basic.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "Typeclasses";
                                                                    "tcresolve"]))))])
                                                                    a14)
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'14
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (125))
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (125))
                                                                    (Prims.of_int (84)))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e,ps'14)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e,
                                                                    ps'14)
                                                                    with
                                                                    | 
                                                                    FStar_Tactics_Result.Success
                                                                    (a14,ps'14)
                                                                    ->
                                                                    (match ()
                                                                    with
                                                                    | 
                                                                    () ->
                                                                    FStar_Tactics_Result.Success
                                                                    ((FStar_Reflection_Basic.pack_sigelt
                                                                    (FStar_Reflection_Data.Sg_Let
                                                                    (false,
                                                                    (FStar_Reflection_Basic.pack_fv
                                                                    (FStar_List_Tot_Base.append
                                                                    a10
                                                                    [
                                                                    FStar_Reflection_Derived.name_of_binder
                                                                    b])), us,
                                                                    a12, a14))),
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'14
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (132))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (132))
                                                                    (Prims.of_int (67))))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e,ps'14)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e,
                                                                    ps'14)))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e,ps'13)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e,
                                                                    ps'13)))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e,ps'12)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e,
                                                                    ps'12))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e,ps'11)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e,
                                                                    ps'11))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e,ps'10)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e,
                                                                    ps'10)))
                                                                    bs1)
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps8
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (110))
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (110))
                                                                    (Prims.of_int (61))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (113))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (136))
                                                                    (Prims.of_int (8)))))))))
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps6
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (106))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (106))
                                                                    (Prims.of_int (57))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (106))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (136))
                                                                    (Prims.of_int (8)))))))))
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'9
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (103))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (136))
                                                                    (Prims.of_int (8))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (103))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (103))
                                                                    (Prims.of_int (25))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (103))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (136))
                                                                    (Prims.of_int (8))))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e,ps'9)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'9)))))
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'8
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (100))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (136))
                                                                    (Prims.of_int (8)))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e,ps'8)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'8))))
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'7
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (98))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (136))
                                                                    (Prims.of_int (8))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (98))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (98))
                                                                    (Prims.of_int (31))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (98))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (136))
                                                                    (Prims.of_int (8))))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e,ps'7)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'7)))))
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
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'4
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (92))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (136))
                                                                    (Prims.of_int (8))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (92))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (92))
                                                                    (Prims.of_int (22))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (92))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (136))
                                                                    (Prims.of_int (8))))))))
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
                                                                    (e, ps'3))))
                                                                 (FStar_Tactics_Types.decr_depth
                                                                    (
                                                                    FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (86))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (136))
                                                                    (Prims.of_int (8))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (86))
                                                                    (Prims.of_int (47))
                                                                    (Prims.of_int (86))
                                                                    (Prims.of_int (49))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (86))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (136))
                                                                    (Prims.of_int (8))))))))
                                                 | FStar_Tactics_Result.Failed
                                                     (e,ps'2) ->
                                                     FStar_Tactics_Result.Failed
                                                       (e, ps'2)))))
                                     (FStar_Tactics_Types.decr_depth
                                        (FStar_Tactics_Types.set_proofstate_range
                                           (FStar_Tactics_Types.incr_depth
                                              (FStar_Tactics_Types.set_proofstate_range
                                                 (FStar_Tactics_Types.decr_depth
                                                    (FStar_Tactics_Types.set_proofstate_range
                                                       ps'1
                                                       (FStar_Range.prims_to_fstar_range
                                                          (Prims.mk_range
                                                             "FStar.Tactics.Typeclasses.fst"
                                                             (Prims.of_int (83))
                                                             (Prims.of_int (4))
                                                             (Prims.of_int (136))
                                                             (Prims.of_int (8))))))
                                                 (FStar_Range.prims_to_fstar_range
                                                    (Prims.mk_range
                                                       "FStar.Tactics.Typeclasses.fst"
                                                       (Prims.of_int (83))
                                                       (Prims.of_int (18))
                                                       (Prims.of_int (83))
                                                       (Prims.of_int (19))))))
                                           (FStar_Range.prims_to_fstar_range
                                              (Prims.mk_range
                                                 "FStar.Tactics.Typeclasses.fst"
                                                 (Prims.of_int (83))
                                                 (Prims.of_int (4))
                                                 (Prims.of_int (136))
                                                 (Prims.of_int (8))))))))
                     | FStar_Tactics_Result.Failed (e,ps'1) ->
                         FStar_Tactics_Result.Failed (e, ps'1)))
           | FStar_Tactics_Result.Failed (e,ps') ->
               FStar_Tactics_Result.Failed (e, ps'))
  