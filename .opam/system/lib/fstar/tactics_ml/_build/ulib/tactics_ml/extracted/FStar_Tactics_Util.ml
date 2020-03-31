open Prims
let rec map :
  'a 'b .
    ('a -> ('b,unit) FStar_Tactics_Effect._dm4f_TAC_repr) ->
      'a Prims.list ->
        ('b Prims.list,unit) FStar_Tactics_Effect._dm4f_TAC_repr
  =
  fun f  ->
    fun x  ->
      match x with
      | [] -> (fun s  -> FStar_Tactics_Result.Success ([], s))
      | a::tl1 ->
          (fun ps  ->
             match (f a)
                     (FStar_Tactics_Types.incr_depth
                        (FStar_Tactics_Types.set_proofstate_range ps
                           (FStar_Range.prims_to_fstar_range
                              (Prims.mk_range "FStar.Tactics.Util.fst"
                                 (Prims.of_int (25)) (Prims.of_int (13))
                                 (Prims.of_int (25)) (Prims.of_int (16))))))
             with
             | FStar_Tactics_Result.Success (a1,ps') ->
                 (match () with
                  | () ->
                      (match (map f tl1)
                               (FStar_Tactics_Types.incr_depth
                                  (FStar_Tactics_Types.set_proofstate_range
                                     (FStar_Tactics_Types.decr_depth
                                        (FStar_Tactics_Types.set_proofstate_range
                                           ps'
                                           (FStar_Range.prims_to_fstar_range
                                              (Prims.mk_range
                                                 "FStar.Tactics.Util.fst"
                                                 (Prims.of_int (25))
                                                 (Prims.of_int (16))
                                                 (Prims.of_int (25))
                                                 (Prims.of_int (18))))))
                                     (FStar_Range.prims_to_fstar_range
                                        (Prims.mk_range
                                           "FStar.Tactics.Util.fst"
                                           (Prims.of_int (25))
                                           (Prims.of_int (18))
                                           (Prims.of_int (25))
                                           (Prims.of_int (26))))))
                       with
                       | FStar_Tactics_Result.Success (a2,ps'1) ->
                           (match () with
                            | () ->
                                FStar_Tactics_Result.Success
                                  ((a1 :: a2),
                                    (FStar_Tactics_Types.decr_depth
                                       (FStar_Tactics_Types.set_proofstate_range
                                          ps'1
                                          (FStar_Range.prims_to_fstar_range
                                             (Prims.mk_range
                                                "FStar.Tactics.Util.fst"
                                                (Prims.of_int (25))
                                                (Prims.of_int (16))
                                                (Prims.of_int (25))
                                                (Prims.of_int (18))))))))
                       | FStar_Tactics_Result.Failed (e,ps'1) ->
                           FStar_Tactics_Result.Failed (e, ps'1)))
             | FStar_Tactics_Result.Failed (e,ps') ->
                 FStar_Tactics_Result.Failed (e, ps'))
  
let rec iter :
  'a .
    ('a -> (unit,unit) FStar_Tactics_Effect._dm4f_TAC_repr) ->
      'a Prims.list -> (unit,unit) FStar_Tactics_Effect._dm4f_TAC_repr
  =
  fun f  ->
    fun x  ->
      match x with
      | [] -> (fun s  -> FStar_Tactics_Result.Success ((), s))
      | a::tl1 ->
          (fun ps  ->
             match (f a)
                     (FStar_Tactics_Types.incr_depth
                        (FStar_Tactics_Types.set_proofstate_range ps
                           (FStar_Range.prims_to_fstar_range
                              (Prims.mk_range "FStar.Tactics.Util.fst"
                                 (Prims.of_int (30)) (Prims.of_int (13))
                                 (Prims.of_int (30)) (Prims.of_int (16))))))
             with
             | FStar_Tactics_Result.Success (a1,ps') ->
                 (match () with
                  | () ->
                      (iter f tl1)
                        (FStar_Tactics_Types.decr_depth
                           (FStar_Tactics_Types.set_proofstate_range ps'
                              (FStar_Range.prims_to_fstar_range
                                 (Prims.mk_range "FStar.Tactics.Util.fst"
                                    (Prims.of_int (30)) (Prims.of_int (18))
                                    (Prims.of_int (30)) (Prims.of_int (27)))))))
             | FStar_Tactics_Result.Failed (e,ps') ->
                 FStar_Tactics_Result.Failed (e, ps'))
  
let rec fold_left :
  'a 'b .
    ('a -> 'b -> ('a,unit) FStar_Tactics_Effect._dm4f_TAC_repr) ->
      'a -> 'b Prims.list -> ('a,unit) FStar_Tactics_Effect._dm4f_TAC_repr
  =
  fun f  ->
    fun x  ->
      fun l  ->
        match l with
        | [] -> (fun s  -> FStar_Tactics_Result.Success (x, s))
        | hd1::tl1 ->
            (fun ps  ->
               match (f x hd1)
                       (FStar_Tactics_Types.incr_depth
                          (FStar_Tactics_Types.set_proofstate_range ps
                             (FStar_Range.prims_to_fstar_range
                                (Prims.mk_range "FStar.Tactics.Util.fst"
                                   (Prims.of_int (35)) (Prims.of_int (26))
                                   (Prims.of_int (35)) (Prims.of_int (34))))))
               with
               | FStar_Tactics_Result.Success (a,ps') ->
                   (match () with
                    | () ->
                        (fold_left f a tl1)
                          (FStar_Tactics_Types.decr_depth
                             (FStar_Tactics_Types.set_proofstate_range ps'
                                (FStar_Range.prims_to_fstar_range
                                   (Prims.mk_range "FStar.Tactics.Util.fst"
                                      (Prims.of_int (35)) (Prims.of_int (14))
                                      (Prims.of_int (35)) (Prims.of_int (37)))))))
               | FStar_Tactics_Result.Failed (e,ps') ->
                   FStar_Tactics_Result.Failed (e, ps'))
  
let rec fold_right :
  'a 'b .
    ('a -> 'b -> ('b,unit) FStar_Tactics_Effect._dm4f_TAC_repr) ->
      'a Prims.list -> 'b -> ('b,unit) FStar_Tactics_Effect._dm4f_TAC_repr
  =
  fun f  ->
    fun l  ->
      fun x  ->
        match l with
        | [] -> (fun s  -> FStar_Tactics_Result.Success (x, s))
        | hd1::tl1 ->
            (fun ps  ->
               match (fold_right f tl1 x)
                       (FStar_Tactics_Types.incr_depth
                          (FStar_Tactics_Types.set_proofstate_range ps
                             (FStar_Range.prims_to_fstar_range
                                (Prims.mk_range "FStar.Tactics.Util.fst"
                                   (Prims.of_int (40)) (Prims.of_int (19))
                                   (Prims.of_int (40)) (Prims.of_int (38))))))
               with
               | FStar_Tactics_Result.Success (a,ps') ->
                   (match () with
                    | () ->
                        (f hd1 a)
                          (FStar_Tactics_Types.decr_depth
                             (FStar_Tactics_Types.set_proofstate_range ps'
                                (FStar_Range.prims_to_fstar_range
                                   (Prims.mk_range "FStar.Tactics.Util.fst"
                                      (Prims.of_int (40)) (Prims.of_int (14))
                                      (Prims.of_int (40)) (Prims.of_int (38)))))))
               | FStar_Tactics_Result.Failed (e,ps') ->
                   FStar_Tactics_Result.Failed (e, ps'))
  
let rec zip :
  'Aa 'Ab .
    'Aa Prims.list ->
      'Ab Prims.list ->
        (('Aa * 'Ab) Prims.list,unit) FStar_Tactics_Effect._dm4f_TAC_repr
  =
  fun l1  ->
    fun l2  ->
      match (l1, l2) with
      | (x::xs,y::ys) ->
          (fun ps  ->
             match (zip xs ys)
                     (FStar_Tactics_Types.incr_depth
                        (FStar_Tactics_Types.set_proofstate_range ps
                           (FStar_Range.prims_to_fstar_range
                              (Prims.mk_range "FStar.Tactics.Util.fst"
                                 (Prims.of_int (45)) (Prims.of_int (31))
                                 (Prims.of_int (45)) (Prims.of_int (42))))))
             with
             | FStar_Tactics_Result.Success (a,ps') ->
                 (match () with
                  | () ->
                      FStar_Tactics_Result.Success
                        (((x, y) :: a),
                          (FStar_Tactics_Types.decr_depth
                             (FStar_Tactics_Types.set_proofstate_range ps'
                                (FStar_Range.prims_to_fstar_range
                                   (Prims.mk_range "FStar.Tactics.Util.fst"
                                      (Prims.of_int (45)) (Prims.of_int (28))
                                      (Prims.of_int (45)) (Prims.of_int (30))))))))
             | FStar_Tactics_Result.Failed (e,ps') ->
                 FStar_Tactics_Result.Failed (e, ps'))
      | uu____877 -> (fun s  -> FStar_Tactics_Result.Success ([], s))
  
let rec filter_map_acc :
  'a 'b .
    ('a ->
       ('b FStar_Pervasives_Native.option,unit)
         FStar_Tactics_Effect._dm4f_TAC_repr)
      ->
      'b Prims.list ->
        'a Prims.list ->
          ('b Prims.list,unit) FStar_Tactics_Effect._dm4f_TAC_repr
  =
  fun f  ->
    fun acc  ->
      fun l  ->
        match l with
        | [] ->
            (fun s  ->
               FStar_Tactics_Result.Success
                 ((FStar_List_Tot_Base.rev acc), s))
        | hd1::tl1 ->
            (fun ps  ->
               match (f hd1)
                       (FStar_Tactics_Types.incr_depth
                          (FStar_Tactics_Types.set_proofstate_range ps
                             (FStar_Range.prims_to_fstar_range
                                (Prims.mk_range "FStar.Tactics.Util.fst"
                                   (Prims.of_int (54)) (Prims.of_int (12))
                                   (Prims.of_int (54)) (Prims.of_int (16))))))
               with
               | FStar_Tactics_Result.Success (a,ps') ->
                   (match () with
                    | () ->
                        ((match a with
                          | FStar_Pervasives_Native.Some hd2 ->
                              filter_map_acc f (hd2 :: acc) tl1
                          | FStar_Pervasives_Native.None  ->
                              filter_map_acc f acc tl1))
                          (FStar_Tactics_Types.decr_depth
                             (FStar_Tactics_Types.set_proofstate_range ps'
                                (FStar_Range.prims_to_fstar_range
                                   (Prims.mk_range "FStar.Tactics.Util.fst"
                                      (Prims.of_int (54)) (Prims.of_int (6))
                                      (Prims.of_int (58)) (Prims.of_int (33)))))))
               | FStar_Tactics_Result.Failed (e,ps') ->
                   FStar_Tactics_Result.Failed (e, ps'))
  
let filter_map :
  'a 'b .
    ('a ->
       ('b FStar_Pervasives_Native.option,unit)
         FStar_Tactics_Effect._dm4f_TAC_repr)
      ->
      'a Prims.list ->
        ('b Prims.list,unit) FStar_Tactics_Effect._dm4f_TAC_repr
  = fun f  -> fun l  -> filter_map_acc f [] l 