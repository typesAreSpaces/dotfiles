open Prims

type ('Aa,'Acm_add,'Acm_mult) distribute_left_lemma = unit
type ('Aa,'Acm_add,'Acm_mult) distribute_right_lemma = unit
type ('Aa,'Acm_add,'Acm_mult) mult_zero_l_lemma = unit
type 'Aa cr =
  | CR of 'Aa FStar_Algebra_CommMonoid.cm * 'Aa FStar_Algebra_CommMonoid.cm *
  unit * unit 
let uu___is_CR : 'Aa . 'Aa cr -> Prims.bool = fun projectee  -> true 
let __proj__CR__item__cm_add :
  'Aa . 'Aa cr -> 'Aa FStar_Algebra_CommMonoid.cm =
  fun projectee  ->
    match projectee with
    | CR (cm_add,cm_mult,distribute,mult_zero_l) -> cm_add
  
let __proj__CR__item__cm_mult :
  'Aa . 'Aa cr -> 'Aa FStar_Algebra_CommMonoid.cm =
  fun projectee  ->
    match projectee with
    | CR (cm_add,cm_mult,distribute,mult_zero_l) -> cm_mult
  



let norm_fully : 'Aa . 'Aa -> 'Aa = fun x  -> x 
type index = Prims.nat
type varlist =
  | Nil_var 
  | Cons_var of index * varlist 
let (uu___is_Nil_var : varlist -> Prims.bool) =
  fun projectee  ->
    match projectee with | Nil_var  -> true | uu____365 -> false
  
let (uu___is_Cons_var : varlist -> Prims.bool) =
  fun projectee  ->
    match projectee with | Cons_var (_0,_1) -> true | uu____382 -> false
  
let (__proj__Cons_var__item___0 : varlist -> index) =
  fun projectee  -> match projectee with | Cons_var (_0,_1) -> _0 
let (__proj__Cons_var__item___1 : varlist -> varlist) =
  fun projectee  -> match projectee with | Cons_var (_0,_1) -> _1 
type 'Aa canonical_sum =
  | Nil_monom 
  | Cons_monom of 'Aa * varlist * 'Aa canonical_sum 
  | Cons_varlist of varlist * 'Aa canonical_sum 
let uu___is_Nil_monom : 'Aa . 'Aa canonical_sum -> Prims.bool =
  fun projectee  ->
    match projectee with | Nil_monom  -> true | uu____468 -> false
  
let uu___is_Cons_monom : 'Aa . 'Aa canonical_sum -> Prims.bool =
  fun projectee  ->
    match projectee with | Cons_monom (_0,_1,_2) -> true | uu____500 -> false
  
let __proj__Cons_monom__item___0 : 'Aa . 'Aa canonical_sum -> 'Aa =
  fun projectee  -> match projectee with | Cons_monom (_0,_1,_2) -> _0 
let __proj__Cons_monom__item___1 : 'Aa . 'Aa canonical_sum -> varlist =
  fun projectee  -> match projectee with | Cons_monom (_0,_1,_2) -> _1 
let __proj__Cons_monom__item___2 :
  'Aa . 'Aa canonical_sum -> 'Aa canonical_sum =
  fun projectee  -> match projectee with | Cons_monom (_0,_1,_2) -> _2 
let uu___is_Cons_varlist : 'Aa . 'Aa canonical_sum -> Prims.bool =
  fun projectee  ->
    match projectee with | Cons_varlist (_0,_1) -> true | uu____607 -> false
  
let __proj__Cons_varlist__item___0 : 'Aa . 'Aa canonical_sum -> varlist =
  fun projectee  -> match projectee with | Cons_varlist (_0,_1) -> _0 
let __proj__Cons_varlist__item___1 :
  'Aa . 'Aa canonical_sum -> 'Aa canonical_sum =
  fun projectee  -> match projectee with | Cons_varlist (_0,_1) -> _1 
let rec (varlist_lt : varlist -> varlist -> Prims.bool) =
  fun x  ->
    fun y  ->
      match (x, y) with
      | (Nil_var ,Cons_var (uu____682,uu____683)) -> true
      | (Cons_var (i,xs),Cons_var (j,ys)) ->
          if i < j then true else (i = j) && (varlist_lt xs ys)
      | (uu____697,uu____698) -> false
  
let rec (varlist_merge : varlist -> varlist -> varlist) =
  fun l1  ->
    fun l2  ->
      match (l1, l2) with
      | (uu____739,Nil_var ) -> l1
      | (Nil_var ,uu____740) -> l2
      | (Cons_var (v1,t1),Cons_var (v2,t2)) -> vm_aux v1 t1 l2

and (vm_aux : index -> varlist -> varlist -> varlist) =
  fun v1  ->
    fun t1  ->
      fun l2  ->
        match l2 with
        | Cons_var (v2,t2) ->
            if v1 < v2
            then Cons_var (v1, (varlist_merge t1 l2))
            else Cons_var (v2, (vm_aux v1 t1 t2))
        | uu____757 -> Cons_var (v1, t1)

let rec canonical_sum_merge :
  'Aa . 'Aa cr -> 'Aa canonical_sum -> 'Aa canonical_sum -> 'Aa canonical_sum
  =
  fun r  ->
    fun s1  ->
      fun s2  ->
        let aplus =
          FStar_Algebra_CommMonoid.__proj__CM__item__mult
            (__proj__CR__item__cm_add r)
           in
        let aone =
          FStar_Algebra_CommMonoid.__proj__CM__item__unit
            (__proj__CR__item__cm_mult r)
           in
        match s1 with
        | Cons_monom (c1,l1,t1) -> csm_aux r c1 l1 t1 s2
        | Cons_varlist (l1,t1) -> csm_aux r aone l1 t1 s2
        | Nil_monom  -> s2

and csm_aux :
  'Aa .
    'Aa cr ->
      'Aa ->
        varlist ->
          'Aa canonical_sum -> 'Aa canonical_sum -> 'Aa canonical_sum
  =
  fun r  ->
    fun c1  ->
      fun l1  ->
        fun t1  ->
          fun s2  ->
            let aplus =
              FStar_Algebra_CommMonoid.__proj__CM__item__mult
                (__proj__CR__item__cm_add r)
               in
            let aone =
              FStar_Algebra_CommMonoid.__proj__CM__item__unit
                (__proj__CR__item__cm_mult r)
               in
            match s2 with
            | Cons_monom (c2,l2,t2) ->
                if l1 = l2
                then
                  Cons_monom
                    ((aplus c1 c2), l1, (canonical_sum_merge r t1 t2))
                else
                  if varlist_lt l1 l2
                  then Cons_monom (c1, l1, (canonical_sum_merge r t1 s2))
                  else Cons_monom (c2, l2, (csm_aux r c1 l1 t1 t2))
            | Cons_varlist (l2,t2) ->
                if l1 = l2
                then
                  Cons_monom
                    ((aplus c1 aone), l1, (canonical_sum_merge r t1 t2))
                else
                  if varlist_lt l1 l2
                  then Cons_monom (c1, l1, (canonical_sum_merge r t1 s2))
                  else Cons_varlist (l2, (csm_aux r c1 l1 t1 t2))
            | Nil_monom  ->
                if c1 = aone
                then Cons_varlist (l1, t1)
                else Cons_monom (c1, l1, t1)

let rec monom_insert :
  'Aa . 'Aa cr -> 'Aa -> varlist -> 'Aa canonical_sum -> 'Aa canonical_sum =
  fun r  ->
    fun c1  ->
      fun l1  ->
        fun s2  ->
          let aplus =
            FStar_Algebra_CommMonoid.__proj__CM__item__mult
              (__proj__CR__item__cm_add r)
             in
          let aone =
            FStar_Algebra_CommMonoid.__proj__CM__item__unit
              (__proj__CR__item__cm_mult r)
             in
          match s2 with
          | Cons_monom (c2,l2,t2) ->
              if l1 = l2
              then Cons_monom ((aplus c1 c2), l1, t2)
              else
                if varlist_lt l1 l2
                then Cons_monom (c1, l1, s2)
                else Cons_monom (c2, l2, (monom_insert r c1 l1 t2))
          | Cons_varlist (l2,t2) ->
              if l1 = l2
              then Cons_monom ((aplus c1 aone), l1, t2)
              else
                if varlist_lt l1 l2
                then Cons_monom (c1, l1, s2)
                else Cons_varlist (l2, (monom_insert r c1 l1 t2))
          | Nil_monom  ->
              if c1 = aone
              then Cons_varlist (l1, Nil_monom)
              else Cons_monom (c1, l1, Nil_monom)
  
let varlist_insert :
  'Aa . 'Aa cr -> varlist -> 'Aa canonical_sum -> 'Aa canonical_sum =
  fun r  ->
    fun l1  ->
      fun s2  ->
        let aone =
          FStar_Algebra_CommMonoid.__proj__CM__item__unit
            (__proj__CR__item__cm_mult r)
           in
        monom_insert r aone l1 s2
  
let rec canonical_sum_scalar :
  'Aa . 'Aa cr -> 'Aa -> 'Aa canonical_sum -> 'Aa canonical_sum =
  fun r  ->
    fun c0  ->
      fun s  ->
        let amult =
          FStar_Algebra_CommMonoid.__proj__CM__item__mult
            (__proj__CR__item__cm_mult r)
           in
        match s with
        | Cons_monom (c,l,t) ->
            Cons_monom ((amult c0 c), l, (canonical_sum_scalar r c0 t))
        | Cons_varlist (l,t) ->
            Cons_monom (c0, l, (canonical_sum_scalar r c0 t))
        | Nil_monom  -> Nil_monom
  
let rec canonical_sum_scalar2 :
  'Aa . 'Aa cr -> varlist -> 'Aa canonical_sum -> 'Aa canonical_sum =
  fun r  ->
    fun l0  ->
      fun s  ->
        match s with
        | Cons_monom (c,l,t) ->
            monom_insert r c (varlist_merge l0 l)
              (canonical_sum_scalar2 r l0 t)
        | Cons_varlist (l,t) ->
            varlist_insert r (varlist_merge l0 l)
              (canonical_sum_scalar2 r l0 t)
        | Nil_monom  -> Nil_monom
  
let rec canonical_sum_scalar3 :
  'Aa . 'Aa cr -> 'Aa -> varlist -> 'Aa canonical_sum -> 'Aa canonical_sum =
  fun r  ->
    fun c0  ->
      fun l0  ->
        fun s  ->
          let amult =
            FStar_Algebra_CommMonoid.__proj__CM__item__mult
              (__proj__CR__item__cm_mult r)
             in
          match s with
          | Cons_monom (c,l,t) ->
              monom_insert r (amult c0 c) (varlist_merge l0 l)
                (canonical_sum_scalar3 r c0 l0 t)
          | Cons_varlist (l,t) ->
              monom_insert r c0 (varlist_merge l0 l)
                (canonical_sum_scalar3 r c0 l0 t)
          | Nil_monom  -> s
  
let rec canonical_sum_prod :
  'Aa . 'Aa cr -> 'Aa canonical_sum -> 'Aa canonical_sum -> 'Aa canonical_sum
  =
  fun r  ->
    fun s1  ->
      fun s2  ->
        match s1 with
        | Cons_monom (c1,l1,t1) ->
            canonical_sum_merge r (canonical_sum_scalar3 r c1 l1 s2)
              (canonical_sum_prod r t1 s2)
        | Cons_varlist (l1,t1) ->
            canonical_sum_merge r (canonical_sum_scalar2 r l1 s2)
              (canonical_sum_prod r t1 s2)
        | Nil_monom  -> s1
  
type 'Aa spolynomial =
  | SPvar of index 
  | SPconst of 'Aa 
  | SPplus of 'Aa spolynomial * 'Aa spolynomial 
  | SPmult of 'Aa spolynomial * 'Aa spolynomial 
let uu___is_SPvar : 'Aa . 'Aa spolynomial -> Prims.bool =
  fun projectee  ->
    match projectee with | SPvar _0 -> true | uu____1397 -> false
  
let __proj__SPvar__item___0 : 'Aa . 'Aa spolynomial -> index =
  fun projectee  -> match projectee with | SPvar _0 -> _0 
let uu___is_SPconst : 'Aa . 'Aa spolynomial -> Prims.bool =
  fun projectee  ->
    match projectee with | SPconst _0 -> true | uu____1444 -> false
  
let __proj__SPconst__item___0 : 'Aa . 'Aa spolynomial -> 'Aa =
  fun projectee  -> match projectee with | SPconst _0 -> _0 
let uu___is_SPplus : 'Aa . 'Aa spolynomial -> Prims.bool =
  fun projectee  ->
    match projectee with | SPplus (_0,_1) -> true | uu____1495 -> false
  
let __proj__SPplus__item___0 : 'Aa . 'Aa spolynomial -> 'Aa spolynomial =
  fun projectee  -> match projectee with | SPplus (_0,_1) -> _0 
let __proj__SPplus__item___1 : 'Aa . 'Aa spolynomial -> 'Aa spolynomial =
  fun projectee  -> match projectee with | SPplus (_0,_1) -> _1 
let uu___is_SPmult : 'Aa . 'Aa spolynomial -> Prims.bool =
  fun projectee  ->
    match projectee with | SPmult (_0,_1) -> true | uu____1581 -> false
  
let __proj__SPmult__item___0 : 'Aa . 'Aa spolynomial -> 'Aa spolynomial =
  fun projectee  -> match projectee with | SPmult (_0,_1) -> _0 
let __proj__SPmult__item___1 : 'Aa . 'Aa spolynomial -> 'Aa spolynomial =
  fun projectee  -> match projectee with | SPmult (_0,_1) -> _1 
let rec spolynomial_normalize :
  'Aa . 'Aa cr -> 'Aa spolynomial -> 'Aa canonical_sum =
  fun r  ->
    fun p  ->
      match p with
      | SPvar i -> Cons_varlist ((Cons_var (i, Nil_var)), Nil_monom)
      | SPconst c -> Cons_monom (c, Nil_var, Nil_monom)
      | SPplus (l,q) ->
          canonical_sum_merge r (spolynomial_normalize r l)
            (spolynomial_normalize r q)
      | SPmult (l,q) ->
          canonical_sum_prod r (spolynomial_normalize r l)
            (spolynomial_normalize r q)
  
let rec canonical_sum_simplify :
  'Aa . 'Aa cr -> 'Aa canonical_sum -> 'Aa canonical_sum =
  fun r  ->
    fun s  ->
      let azero =
        FStar_Algebra_CommMonoid.__proj__CM__item__unit
          (__proj__CR__item__cm_add r)
         in
      let aone =
        FStar_Algebra_CommMonoid.__proj__CM__item__unit
          (__proj__CR__item__cm_mult r)
         in
      let aplus =
        FStar_Algebra_CommMonoid.__proj__CM__item__mult
          (__proj__CR__item__cm_add r)
         in
      match s with
      | Cons_monom (c,l,t) ->
          if c = azero
          then canonical_sum_simplify r t
          else
            if c = aone
            then Cons_varlist (l, (canonical_sum_simplify r t))
            else Cons_monom (c, l, (canonical_sum_simplify r t))
      | Cons_varlist (l,t) -> Cons_varlist (l, (canonical_sum_simplify r t))
      | Nil_monom  -> s
  
let spolynomial_simplify :
  'Aa . 'Aa cr -> 'Aa spolynomial -> 'Aa canonical_sum =
  fun r  -> fun p  -> canonical_sum_simplify r (spolynomial_normalize r p) 
type 'Aa vmap = ((FStar_Reflection_Data.var * 'Aa) Prims.list * 'Aa)
let update : 'Aa . FStar_Reflection_Data.var -> 'Aa -> 'Aa vmap -> 'Aa vmap =
  fun x  ->
    fun xa  ->
      fun vm  ->
        let uu____1846 = vm  in
        match uu____1846 with | (l,y) -> (((x, xa) :: l), y)
  
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
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (373))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (375))
                                                                    (Prims.of_int (68))))))
                                                           (FStar_Range.prims_to_fstar_range
                                                              (Prims.mk_range
                                                                 "FStar.Tactics.CanonCommSemiring.fst"
                                                                 (Prims.of_int (373))
                                                                 (Prims.of_int (29))
                                                                 (Prims.of_int (375))
                                                                 (Prims.of_int (68))))))
                                                     (FStar_Range.prims_to_fstar_range
                                                        (Prims.mk_range
                                                           "FStar.Tactics.CanonCommSemiring.fst"
                                                           (Prims.of_int (374))
                                                           (Prims.of_int (29))
                                                           (Prims.of_int (374))
                                                           (Prims.of_int (51))))))
                                               (FStar_Range.prims_to_fstar_range
                                                  (Prims.mk_range
                                                     "FStar.Tactics.CanonCommSemiring.fst"
                                                     (Prims.of_int (374))
                                                     (Prims.of_int (30))
                                                     (Prims.of_int (374))
                                                     (Prims.of_int (38))))))
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
                                                          "FStar.Tactics.CanonCommSemiring.fst"
                                                          (Prims.of_int (374))
                                                          (Prims.of_int (29))
                                                          (Prims.of_int (374))
                                                          (Prims.of_int (51))))))))
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
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (373))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (375))
                                                                    (Prims.of_int (68))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (373))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (375))
                                                                    (Prims.of_int (68))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (375))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (375))
                                                                    (Prims.of_int (67))))))
                                                               (FStar_Range.prims_to_fstar_range
                                                                  (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (375))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (375))
                                                                    (Prims.of_int (54))))))
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
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (375))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (375))
                                                                    (Prims.of_int (67))))))))
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
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (373))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (375))
                                                                    (Prims.of_int (68))))))))
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
                                                              "FStar.Tactics.CanonCommSemiring.fst"
                                                              (Prims.of_int (373))
                                                              (Prims.of_int (29))
                                                              (Prims.of_int (375))
                                                              (Prims.of_int (68))))))))
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
                                              "FStar.Tactics.CanonCommSemiring.fst"
                                              (Prims.of_int (373))
                                              (Prims.of_int (29))
                                              (Prims.of_int (375))
                                              (Prims.of_int (68))))))))
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
                                        "FStar.Tactics.CanonCommSemiring.fst"
                                        (Prims.of_int (373))
                                        (Prims.of_int (14))
                                        (Prims.of_int (375))
                                        (Prims.of_int (68))))))))
               | FStar_Tactics_Result.Failed (e,ps') ->
                   FStar_Tactics_Result.Failed (e, ps'))
  
let quote_vm :
  'Aa .
    FStar_Reflection_Types.term ->
      ('Aa ->
         (FStar_Reflection_Types.term,unit)
           FStar_Tactics_Effect._dm4f_TAC_repr)
        ->
        'Aa vmap ->
          (FStar_Reflection_Types.term,unit)
            FStar_Tactics_Effect._dm4f_TAC_repr
  =
  fun ta  ->
    fun quotea  ->
      fun vm  ->
        fun ps  ->
          match () with
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
                                ta])
                             (fun p  ->
                                fun ps1  ->
                                  match match match match match (FStar_Tactics_Builtins.pack
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
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (380))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (382))
                                                                    (Prims.of_int (35))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (380))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (382))
                                                                    (Prims.of_int (35))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (380))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (382))
                                                                    (Prims.of_int (35))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (381))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (381))
                                                                    (Prims.of_int (51))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (381))
                                                                    (Prims.of_int (7))
                                                                    (Prims.of_int (381))
                                                                    (Prims.of_int (38))))))
                                                          with
                                                          | FStar_Tactics_Result.Success
                                                              (a,ps') ->
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
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (381))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (381))
                                                                    (Prims.of_int (51))))))))
                                                          | FStar_Tactics_Result.Failed
                                                              (e,ps') ->
                                                              FStar_Tactics_Result.Failed
                                                                (e, ps')
                                                    with
                                                    | FStar_Tactics_Result.Success
                                                        (a,ps') ->
                                                        (match () with
                                                         | () ->
                                                             (match match 
                                                                    match 
                                                                    (quotea
                                                                    (FStar_Pervasives_Native.snd
                                                                    p))
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
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (380))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (382))
                                                                    (Prims.of_int (35))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (380))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (382))
                                                                    (Prims.of_int (35))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (382))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (382))
                                                                    (Prims.of_int (34))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (382))
                                                                    (Prims.of_int (7))
                                                                    (Prims.of_int (382))
                                                                    (Prims.of_int (21))))))
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
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (382))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (382))
                                                                    (Prims.of_int (34))))))))
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
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (380))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (382))
                                                                    (Prims.of_int (35))))))))
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
                                                                    ((a ::
                                                                    a1),
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'1
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (380))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (382))
                                                                    (Prims.of_int (35))))))))
                                                              | FStar_Tactics_Result.Failed
                                                                  (e,ps'1) ->
                                                                  FStar_Tactics_Result.Failed
                                                                    (e, ps'1)))
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
                                                         (((ta,
                                                             FStar_Reflection_Data.Q_Implicit)
                                                           :: a),
                                                           (FStar_Tactics_Types.decr_depth
                                                              (FStar_Tactics_Types.set_proofstate_range
                                                                 ps'
                                                                 (FStar_Range.prims_to_fstar_range
                                                                    (
                                                                    Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (380))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (382))
                                                                    (Prims.of_int (35))))))))
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
                                                                 "FStar.Tactics.CanonCommSemiring.fst"
                                                                 (Prims.of_int (380))
                                                                 (Prims.of_int (23))
                                                                 (Prims.of_int (382))
                                                                 (Prims.of_int (35))))))))
                                        | FStar_Tactics_Result.Failed 
                                            (e,ps') ->
                                            FStar_Tactics_Result.Failed
                                              (e, ps')
                                  with
                                  | FStar_Tactics_Result.Success (a,ps') ->
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
                                                          "Mktuple2"]))) a),
                                               (FStar_Tactics_Types.decr_depth
                                                  (FStar_Tactics_Types.set_proofstate_range
                                                     ps'
                                                     (FStar_Range.prims_to_fstar_range
                                                        (Prims.mk_range
                                                           "FStar.Tactics.CanonCommSemiring.fst"
                                                           (Prims.of_int (380))
                                                           (Prims.of_int (4))
                                                           (Prims.of_int (382))
                                                           (Prims.of_int (35))))))))
                                  | FStar_Tactics_Result.Failed (e,ps') ->
                                      FStar_Tactics_Result.Failed (e, ps'))
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
                                                          ps
                                                          (FStar_Range.prims_to_fstar_range
                                                             (Prims.mk_range
                                                                "FStar.Tactics.CanonCommSemiring.fst"
                                                                (Prims.of_int (380))
                                                                (Prims.of_int (4))
                                                                (Prims.of_int (382))
                                                                (Prims.of_int (35))))))
                                                    (FStar_Range.prims_to_fstar_range
                                                       (Prims.mk_range
                                                          "FStar.Tactics.CanonCommSemiring.fst"
                                                          (Prims.of_int (383))
                                                          (Prims.of_int (2))
                                                          (Prims.of_int (387))
                                                          (Prims.of_int (73))))))
                                              (FStar_Range.prims_to_fstar_range
                                                 (Prims.mk_range
                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                    (Prims.of_int (383))
                                                    (Prims.of_int (16))
                                                    (Prims.of_int (383))
                                                    (Prims.of_int (47))))))
                                        (FStar_Range.prims_to_fstar_range
                                           (Prims.mk_range
                                              "FStar.Tactics.CanonCommSemiring.fst"
                                              (Prims.of_int (384))
                                              (Prims.of_int (2))
                                              (Prims.of_int (387))
                                              (Prims.of_int (73))))))
                                  (FStar_Range.prims_to_fstar_range
                                     (Prims.mk_range
                                        "FStar.Tactics.CanonCommSemiring.fst"
                                        (Prims.of_int (384))
                                        (Prims.of_int (14))
                                        (Prims.of_int (384))
                                        (Prims.of_int (57))))))
                    with
                    | FStar_Tactics_Result.Success (a,ps') ->
                        (match () with
                         | () ->
                             (match () with
                              | () ->
                                  (match match match match match match 
                                                                   (quotea
                                                                    (FStar_Pervasives_Native.snd
                                                                    vm))
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
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (385))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (387))
                                                                    (Prims.of_int (73))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (385))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (385))
                                                                    (Prims.of_int (41))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (386))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (387))
                                                                    (Prims.of_int (73))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (386))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (387))
                                                                    (Prims.of_int (73))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (386))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (387))
                                                                    (Prims.of_int (73))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (386))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (387))
                                                                    (Prims.of_int (73))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (386))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (387))
                                                                    (Prims.of_int (73))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (387))
                                                                    (Prims.of_int (43))
                                                                    (Prims.of_int (387))
                                                                    (Prims.of_int (72))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (387))
                                                                    (Prims.of_int (44))
                                                                    (Prims.of_int (387))
                                                                    (Prims.of_int (59))))))
                                                                 with
                                                                 | FStar_Tactics_Result.Success
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
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (387))
                                                                    (Prims.of_int (43))
                                                                    (Prims.of_int (387))
                                                                    (Prims.of_int (72))))))))
                                                                 | FStar_Tactics_Result.Failed
                                                                    (e,ps'1)
                                                                    ->
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
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (386))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (387))
                                                                    (Prims.of_int (73))))))))
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
                                                                (((a,
                                                                    FStar_Reflection_Data.Q_Explicit)
                                                                  :: a1),
                                                                  (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'1
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (386))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (387))
                                                                    (Prims.of_int (73))))))))
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
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (386))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (387))
                                                                    (Prims.of_int (73))))))))
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
                                                    ((((FStar_Reflection_Derived.mk_e_app
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
                                                             ta]]),
                                                        FStar_Reflection_Data.Q_Implicit)
                                                      :: a1),
                                                      (FStar_Tactics_Types.decr_depth
                                                         (FStar_Tactics_Types.set_proofstate_range
                                                            ps'1
                                                            (FStar_Range.prims_to_fstar_range
                                                               (Prims.mk_range
                                                                  "FStar.Tactics.CanonCommSemiring.fst"
                                                                  (Prims.of_int (386))
                                                                  (Prims.of_int (21))
                                                                  (Prims.of_int (387))
                                                                  (Prims.of_int (73))))))))
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
                                              ((FStar_Reflection_Derived.mk_app
                                                  (FStar_Reflection_Basic.pack_ln
                                                     (FStar_Reflection_Data.Tv_FVar
                                                        (FStar_Reflection_Basic.pack_fv
                                                           ["FStar";
                                                           "Pervasives";
                                                           "Native";
                                                           "Mktuple2"]))) a1),
                                                (FStar_Tactics_Types.decr_depth
                                                   (FStar_Tactics_Types.set_proofstate_range
                                                      ps'1
                                                      (FStar_Range.prims_to_fstar_range
                                                         (Prims.mk_range
                                                            "FStar.Tactics.CanonCommSemiring.fst"
                                                            (Prims.of_int (386))
                                                            (Prims.of_int (2))
                                                            (Prims.of_int (387))
                                                            (Prims.of_int (73))))))))
                                   | FStar_Tactics_Result.Failed (e,ps'1) ->
                                       FStar_Tactics_Result.Failed (e, ps'1))))
                    | FStar_Tactics_Result.Failed (e,ps') ->
                        FStar_Tactics_Result.Failed (e, ps')))
  
let interp_var : 'Aa . 'Aa vmap -> index -> 'Aa =
  fun vm  ->
    fun i  ->
      match FStar_List_Tot_Base.assoc i (FStar_Pervasives_Native.fst vm) with
      | FStar_Pervasives_Native.Some x -> x
      | uu____3217 -> FStar_Pervasives_Native.snd vm
  
let rec ivl_aux : 'Aa . 'Aa cr -> 'Aa vmap -> index -> varlist -> 'Aa =
  fun r  ->
    fun vm  ->
      fun x  ->
        fun t  ->
          let amult =
            FStar_Algebra_CommMonoid.__proj__CM__item__mult
              (__proj__CR__item__cm_mult r)
             in
          match t with
          | Nil_var  -> interp_var vm x
          | Cons_var (x',t') -> amult (interp_var vm x) (ivl_aux r vm x' t')
  
let interp_vl : 'Aa . 'Aa cr -> 'Aa vmap -> varlist -> 'Aa =
  fun r  ->
    fun vm  ->
      fun l  ->
        let aone =
          FStar_Algebra_CommMonoid.__proj__CM__item__unit
            (__proj__CR__item__cm_mult r)
           in
        match l with | Nil_var  -> aone | Cons_var (x,t) -> ivl_aux r vm x t
  
let interp_m : 'Aa . 'Aa cr -> 'Aa vmap -> 'Aa -> varlist -> 'Aa =
  fun r  ->
    fun vm  ->
      fun c  ->
        fun l  ->
          let amult =
            FStar_Algebra_CommMonoid.__proj__CM__item__mult
              (__proj__CR__item__cm_mult r)
             in
          match l with
          | Nil_var  -> c
          | Cons_var (x,t) -> amult c (ivl_aux r vm x t)
  
let rec ics_aux : 'Aa . 'Aa cr -> 'Aa vmap -> 'Aa -> 'Aa canonical_sum -> 'Aa
  =
  fun r  ->
    fun vm  ->
      fun x  ->
        fun s  ->
          let aplus =
            FStar_Algebra_CommMonoid.__proj__CM__item__mult
              (__proj__CR__item__cm_add r)
             in
          match s with
          | Nil_monom  -> x
          | Cons_varlist (l,t) -> aplus x (ics_aux r vm (interp_vl r vm l) t)
          | Cons_monom (c,l,t) ->
              aplus x (ics_aux r vm (interp_m r vm c l) t)
  
let interp_cs : 'Aa . 'Aa cr -> 'Aa vmap -> 'Aa canonical_sum -> 'Aa =
  fun r  ->
    fun vm  ->
      fun s  ->
        let azero =
          FStar_Algebra_CommMonoid.__proj__CM__item__unit
            (__proj__CR__item__cm_add r)
           in
        match s with
        | Nil_monom  -> azero
        | Cons_varlist (l,t) -> ics_aux r vm (interp_vl r vm l) t
        | Cons_monom (c,l,t) -> ics_aux r vm (interp_m r vm c l) t
  
let rec interp_sp : 'Aa . 'Aa cr -> 'Aa vmap -> 'Aa spolynomial -> 'Aa =
  fun r  ->
    fun vm  ->
      fun p  ->
        let aplus =
          FStar_Algebra_CommMonoid.__proj__CM__item__mult
            (__proj__CR__item__cm_add r)
           in
        let amult =
          FStar_Algebra_CommMonoid.__proj__CM__item__mult
            (__proj__CR__item__cm_mult r)
           in
        match p with
        | SPconst c -> c
        | SPvar i -> interp_var vm i
        | SPplus (p1,p2) -> aplus (interp_sp r vm p1) (interp_sp r vm p2)
        | SPmult (p1,p2) -> amult (interp_sp r vm p1) (interp_sp r vm p2)
  





















let (ddump : Prims.string -> (unit,unit) FStar_Tactics_Effect._dm4f_TAC_repr)
  =
  fun m  ->
    fun ps  ->
      match (FStar_Tactics_Builtins.debugging ())
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Tactics.CanonCommSemiring.fst"
                          (Prims.of_int (1317)) (Prims.of_int (17))
                          (Prims.of_int (1317)) (Prims.of_int (29))))))
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
                             "FStar.Tactics.CanonCommSemiring.fst"
                             (Prims.of_int (1317)) (Prims.of_int (14))
                             (Prims.of_int (1317)) (Prims.of_int (41)))))))
      | FStar_Tactics_Result.Failed (e,ps') ->
          FStar_Tactics_Result.Failed (e, ps')
  
let rec (find_aux :
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
            else find_aux (n1 + Prims.int_one) x xs'
  
let (find :
  FStar_Reflection_Types.term ->
    FStar_Reflection_Types.term Prims.list ->
      Prims.nat FStar_Pervasives_Native.option)
  = find_aux Prims.int_zero 
let make_fvar :
  'Aa .
    FStar_Reflection_Types.term ->
      (FStar_Reflection_Types.term ->
         ('Aa,unit) FStar_Tactics_Effect._dm4f_TAC_repr)
        ->
        FStar_Reflection_Types.term Prims.list ->
          'Aa vmap ->
            (('Aa spolynomial * FStar_Reflection_Types.term Prims.list * 'Aa
               vmap),unit)
              FStar_Tactics_Effect._dm4f_TAC_repr
  =
  fun t  ->
    fun unquotea  ->
      fun ts  ->
        fun vm  ->
          match find t ts with
          | FStar_Pervasives_Native.Some v1 ->
              (fun s  ->
                 FStar_Tactics_Result.Success (((SPvar v1), ts, vm), s))
          | FStar_Pervasives_Native.None  ->
              (fun ps  ->
                 match () with
                 | () ->
                     (match (unquotea t)
                              (FStar_Tactics_Types.incr_depth
                                 (FStar_Tactics_Types.set_proofstate_range
                                    (FStar_Tactics_Types.decr_depth
                                       (FStar_Tactics_Types.set_proofstate_range
                                          (FStar_Tactics_Types.incr_depth
                                             (FStar_Tactics_Types.set_proofstate_range
                                                ps
                                                (FStar_Range.prims_to_fstar_range
                                                   (Prims.mk_range
                                                      "FStar.Tactics.CanonCommSemiring.fst"
                                                      (Prims.of_int (1335))
                                                      (Prims.of_int (17))
                                                      (Prims.of_int (1335))
                                                      (Prims.of_int (26))))))
                                          (FStar_Range.prims_to_fstar_range
                                             (Prims.mk_range
                                                "FStar.Tactics.CanonCommSemiring.fst"
                                                (Prims.of_int (1336))
                                                (Prims.of_int (4))
                                                (Prims.of_int (1337))
                                                (Prims.of_int (48))))))
                                    (FStar_Range.prims_to_fstar_range
                                       (Prims.mk_range
                                          "FStar.Tactics.CanonCommSemiring.fst"
                                          (Prims.of_int (1336))
                                          (Prims.of_int (12))
                                          (Prims.of_int (1336))
                                          (Prims.of_int (22))))))
                      with
                      | FStar_Tactics_Result.Success (a,ps') ->
                          (match () with
                           | () ->
                               FStar_Tactics_Result.Success
                                 (((SPvar (FStar_List_Tot_Base.length ts)),
                                    (FStar_List_Tot_Base.op_At ts [t]),
                                    (update (FStar_List_Tot_Base.length ts) a
                                       vm)),
                                   (FStar_Tactics_Types.decr_depth
                                      (FStar_Tactics_Types.set_proofstate_range
                                         ps'
                                         (FStar_Range.prims_to_fstar_range
                                            (Prims.mk_range
                                               "FStar.Tactics.CanonCommSemiring.fst"
                                               (Prims.of_int (1337))
                                               (Prims.of_int (4))
                                               (Prims.of_int (1337))
                                               (Prims.of_int (48))))))))
                      | FStar_Tactics_Result.Failed (e,ps') ->
                          FStar_Tactics_Result.Failed (e, ps')))
  
let rec reification_aux :
  'Aa .
    (FStar_Reflection_Types.term ->
       ('Aa,unit) FStar_Tactics_Effect._dm4f_TAC_repr)
      ->
      FStar_Reflection_Types.term Prims.list ->
        'Aa vmap ->
          FStar_Reflection_Types.term ->
            FStar_Reflection_Types.term ->
              FStar_Reflection_Types.term ->
                (('Aa spolynomial * FStar_Reflection_Types.term Prims.list *
                   'Aa vmap),unit)
                  FStar_Tactics_Effect._dm4f_TAC_repr
  =
  fun unquotea  ->
    fun ts  ->
      fun vm  ->
        fun add1  ->
          fun mult  ->
            fun t  ->
              fun ps  ->
                match () with
                | () ->
                    ((match FStar_Reflection_Derived_Lemmas.collect_app_ref t
                      with
                      | (hd1,tl1) ->
                          (fun ps1  ->
                             match match (FStar_Tactics_Builtins.inspect hd1)
                                           (FStar_Tactics_Types.incr_depth
                                              (FStar_Tactics_Types.set_proofstate_range
                                                 (FStar_Tactics_Types.incr_depth
                                                    (FStar_Tactics_Types.set_proofstate_range
                                                       ps1
                                                       (FStar_Range.prims_to_fstar_range
                                                          (Prims.mk_range
                                                             "FStar.Tactics.CanonCommSemiring.fst"
                                                             (Prims.of_int (1343))
                                                             (Prims.of_int (8))
                                                             (Prims.of_int (1343))
                                                             (Prims.of_int (33))))))
                                                 (FStar_Range.prims_to_fstar_range
                                                    (Prims.mk_range
                                                       "FStar.Tactics.CanonCommSemiring.fst"
                                                       (Prims.of_int (1343))
                                                       (Prims.of_int (8))
                                                       (Prims.of_int (1343))
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
                                                            "FStar.Tactics.CanonCommSemiring.fst"
                                                            (Prims.of_int (1343))
                                                            (Prims.of_int (8))
                                                            (Prims.of_int (1343))
                                                            (Prims.of_int (33))))))))
                                   | FStar_Tactics_Result.Failed (e,ps') ->
                                       FStar_Tactics_Result.Failed (e, ps')
                             with
                             | FStar_Tactics_Result.Success (a,ps') ->
                                 (match () with
                                  | () ->
                                      ((match a with
                                        | (FStar_Reflection_Data.Tv_FVar
                                           fv,(t1,uu____6148)::(t2,uu____6150)::[])
                                            ->
                                            (fun ps2  ->
                                               match () with
                                               | () ->
                                                   (match match (FStar_Tactics_Builtins.pack
                                                                   (FStar_Reflection_Data.Tv_FVar
                                                                    fv))
                                                                  (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1349))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (1351))
                                                                    (Prims.of_int (24))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1353))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (1355))
                                                                    (Prims.of_int (30))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1353))
                                                                    (Prims.of_int (7))
                                                                    (Prims.of_int (1353))
                                                                    (Prims.of_int (38))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1353))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (1353))
                                                                    (Prims.of_int (34))))))
                                                          with
                                                          | FStar_Tactics_Result.Success
                                                              (a1,ps'1) ->
                                                              (match () with
                                                               | () ->
                                                                   FStar_Tactics_Result.Success
                                                                    ((FStar_Reflection_Basic.term_eq
                                                                    a1 add1),
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'1
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1353))
                                                                    (Prims.of_int (7))
                                                                    (Prims.of_int (1353))
                                                                    (Prims.of_int (38))))))))
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
                                                                    unquotea
                                                                    ts vm
                                                                    add1 mult
                                                                    t1)
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1349))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (1349))
                                                                    (Prims.of_int (67))))))
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
                                                                    ts1 vm1
                                                                    add1 mult
                                                                    t2)
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps4
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1350))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (1350))
                                                                    (Prims.of_int (67))))))
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
                                                                    ((SPplus
                                                                    (e1, e2)),
                                                                    ts2, vm2))),
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1350))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (1350))
                                                                    (Prims.of_int (21))))))))
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
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1349))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (1349))
                                                                    (Prims.of_int (21)))))))
                                                                   | 
                                                                   FStar_Tactics_Result.Failed
                                                                    (e,ps'2)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'2))
                                                              else
                                                                (fun ps3  ->
                                                                   match 
                                                                    match 
                                                                    (FStar_Tactics_Builtins.pack
                                                                    (FStar_Reflection_Data.Tv_FVar
                                                                    fv))
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1354))
                                                                    (Prims.of_int (7))
                                                                    (Prims.of_int (1354))
                                                                    (Prims.of_int (39))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1354))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (1354))
                                                                    (Prims.of_int (34))))))
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
                                                                    ((FStar_Reflection_Basic.term_eq
                                                                    a2 mult),
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1354))
                                                                    (Prims.of_int (7))
                                                                    (Prims.of_int (1354))
                                                                    (Prims.of_int (39))))))))
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
                                                                    (if a2
                                                                    then
                                                                    (fun ps4 
                                                                    ->
                                                                    match 
                                                                    (reification_aux
                                                                    unquotea
                                                                    ts vm
                                                                    add1 mult
                                                                    t1)
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps4
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1349))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (1349))
                                                                    (Prims.of_int (67))))))
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
                                                                    | (e1,ts1,vm1)
                                                                    ->
                                                                    (fun ps5 
                                                                    ->
                                                                    match 
                                                                    (reification_aux
                                                                    unquotea
                                                                    ts1 vm1
                                                                    add1 mult
                                                                    t2)
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps5
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1350))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (1350))
                                                                    (Prims.of_int (67))))))
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
                                                                    (((
                                                                    match a4
                                                                    with
                                                                    | 
                                                                    (e2,ts2,vm2)
                                                                    ->
                                                                    ((SPmult
                                                                    (e1, e2)),
                                                                    ts2, vm2))),
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'4
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1350))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (1350))
                                                                    (Prims.of_int (21))))))))
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
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1349))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (1349))
                                                                    (Prims.of_int (21)))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e,ps'3)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'3))
                                                                    else
                                                                    make_fvar
                                                                    t
                                                                    unquotea
                                                                    ts vm)
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1354))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (1355))
                                                                    (Prims.of_int (30)))))))
                                                                   | 
                                                                   FStar_Tactics_Result.Failed
                                                                    (e,ps'2)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e, ps'2)))
                                                               (FStar_Tactics_Types.decr_depth
                                                                  (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'1
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1353))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (1355))
                                                                    (Prims.of_int (30)))))))
                                                    | FStar_Tactics_Result.Failed
                                                        (e,ps'1) ->
                                                        FStar_Tactics_Result.Failed
                                                          (e, ps'1)))
                                        | (FStar_Reflection_Data.Tv_Const
                                           uu____6949,[]) ->
                                            (fun ps2  ->
                                               match match (unquotea t)
                                                             (FStar_Tactics_Types.incr_depth
                                                                (FStar_Tactics_Types.set_proofstate_range
                                                                   (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1358))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (1358))
                                                                    (Prims.of_int (42))))))
                                                                   (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1358))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (1358))
                                                                    (Prims.of_int (42))))))
                                                     with
                                                     | FStar_Tactics_Result.Success
                                                         (a1,ps'1) ->
                                                         (match () with
                                                          | () ->
                                                              FStar_Tactics_Result.Success
                                                                ((SPconst a1),
                                                                  (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'1
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1358))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (1358))
                                                                    (Prims.of_int (42))))))))
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
                                                          ((a1, ts, vm),
                                                            (FStar_Tactics_Types.decr_depth
                                                               (FStar_Tactics_Types.set_proofstate_range
                                                                  ps'1
                                                                  (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1358))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (1358))
                                                                    (Prims.of_int (50))))))))
                                               | FStar_Tactics_Result.Failed
                                                   (e,ps'1) ->
                                                   FStar_Tactics_Result.Failed
                                                     (e, ps'1))
                                        | (uu____7083,uu____7084) ->
                                            make_fvar t unquotea ts vm))
                                        (FStar_Tactics_Types.decr_depth
                                           (FStar_Tactics_Types.set_proofstate_range
                                              ps'
                                              (FStar_Range.prims_to_fstar_range
                                                 (Prims.mk_range
                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                    (Prims.of_int (1343))
                                                    (Prims.of_int (2))
                                                    (Prims.of_int (1359))
                                                    (Prims.of_int (38)))))))
                             | FStar_Tactics_Result.Failed (e,ps') ->
                                 FStar_Tactics_Result.Failed (e, ps'))))
                      (FStar_Tactics_Types.decr_depth
                         (FStar_Tactics_Types.set_proofstate_range
                            (FStar_Tactics_Types.incr_depth
                               (FStar_Tactics_Types.set_proofstate_range ps
                                  (FStar_Range.prims_to_fstar_range
                                     (Prims.mk_range
                                        "FStar.Tactics.CanonCommSemiring.fst"
                                        (Prims.of_int (1342))
                                        (Prims.of_int (15))
                                        (Prims.of_int (1342))
                                        (Prims.of_int (32))))))
                            (FStar_Range.prims_to_fstar_range
                               (Prims.mk_range
                                  "FStar.Tactics.CanonCommSemiring.fst"
                                  (Prims.of_int (1342)) (Prims.of_int (2))
                                  (Prims.of_int (1359)) (Prims.of_int (38))))))
  
let (steps : FStar_Pervasives.norm_step Prims.list) =
  [FStar_Pervasives.primops;
  FStar_Pervasives.iota;
  FStar_Pervasives.zeta;
  FStar_Pervasives.delta_attr ["FStar.Tactics.CanonCommSemiring.canon_attr"];
  FStar_Pervasives.delta_only
    ["FStar.Mul.op_Star";
    "FStar.Algebra.CommMonoid.int_plus_cm";
    "FStar.Algebra.CommMonoid.int_multiply_cm";
    "FStar.Algebra.CommMonoid.__proj__CM__item__mult";
    "FStar.Algebra.CommMonoid.__proj__CM__item__unit";
    "FStar.Tactics.CanonCommSemiring.__proj__CR__item__cm_add";
    "FStar.Tactics.CanonCommSemiring.__proj__CR__item__cm_mult";
    "FStar.List.Tot.Base.assoc";
    "FStar.Pervasives.Native.fst";
    "FStar.Pervasives.Native.snd";
    "FStar.Pervasives.Native.__proj__Mktuple2__item___1";
    "FStar.Pervasives.Native.__proj__Mktuple2__item___2";
    "FStar.List.Tot.Base.op_At";
    "FStar.List.Tot.Base.append"]]
  
let (canon_norm : unit -> (unit,unit) FStar_Tactics_Effect._dm4f_TAC_repr) =
  fun uu____7178  -> FStar_Tactics_Builtins.norm steps 
let reification :
  'Aa .
    (FStar_Reflection_Types.term ->
       ('Aa,unit) FStar_Tactics_Effect._dm4f_TAC_repr)
      ->
      ('Aa ->
         (FStar_Reflection_Types.term,unit)
           FStar_Tactics_Effect._dm4f_TAC_repr)
        ->
        FStar_Reflection_Types.term ->
          FStar_Reflection_Types.term ->
            'Aa ->
              FStar_Reflection_Types.term Prims.list ->
                (('Aa spolynomial Prims.list * 'Aa vmap),unit)
                  FStar_Tactics_Effect._dm4f_TAC_repr
  =
  fun unquotea  ->
    fun quotea  ->
      fun tadd  ->
        fun tmult  ->
          fun munit  ->
            fun ts  ->
              fun ps  ->
                match () with
                | () ->
                    (match () with
                     | () ->
                         (match (FStar_Tactics_Util.map
                                   (FStar_Tactics_Derived.norm_term steps) ts)
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
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1396))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (1396))
                                                                    (Prims.of_int (17))))))
                                                          (FStar_Range.prims_to_fstar_range
                                                             (Prims.mk_range
                                                                "FStar.Tactics.CanonCommSemiring.fst"
                                                                (Prims.of_int (1397))
                                                                (Prims.of_int (2))
                                                                (Prims.of_int (1406))
                                                                (Prims.of_int (22))))))
                                                    (FStar_Range.prims_to_fstar_range
                                                       (Prims.mk_range
                                                          "FStar.Tactics.CanonCommSemiring.fst"
                                                          (Prims.of_int (1397))
                                                          (Prims.of_int (13))
                                                          (Prims.of_int (1397))
                                                          (Prims.of_int (18))))))
                                              (FStar_Range.prims_to_fstar_range
                                                 (Prims.mk_range
                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                    (Prims.of_int (1398))
                                                    (Prims.of_int (2))
                                                    (Prims.of_int (1406))
                                                    (Prims.of_int (22))))))
                                        (FStar_Range.prims_to_fstar_range
                                           (Prims.mk_range
                                              "FStar.Tactics.CanonCommSemiring.fst"
                                              (Prims.of_int (1398))
                                              (Prims.of_int (11))
                                              (Prims.of_int (1398))
                                              (Prims.of_int (48))))))
                          with
                          | FStar_Tactics_Result.Success (a,ps') ->
                              (match () with
                               | () ->
                                   (match (FStar_Tactics_Util.fold_left
                                             (fun uu____7626  ->
                                                fun t  ->
                                                  match uu____7626 with
                                                  | (es,vs,vm) ->
                                                      (fun ps1  ->
                                                         match (reification_aux
                                                                  unquotea vs
                                                                  vm tadd
                                                                  tmult t)
                                                                 (FStar_Tactics_Types.incr_depth
                                                                    (
                                                                    FStar_Tactics_Types.set_proofstate_range
                                                                    ps1
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1403))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (1403))
                                                                    (Prims.of_int (67))))))
                                                         with
                                                         | FStar_Tactics_Result.Success
                                                             (a1,ps'1) ->
                                                             (match () with
                                                              | () ->
                                                                  FStar_Tactics_Result.Success
                                                                    (((
                                                                    match a1
                                                                    with
                                                                    | 
                                                                    (e,vs1,vm1)
                                                                    ->
                                                                    ((e ::
                                                                    es), vs1,
                                                                    vm1))),
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'1
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1403))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (1403))
                                                                    (Prims.of_int (22))))))))
                                                         | FStar_Tactics_Result.Failed
                                                             (e,ps'1) ->
                                                             FStar_Tactics_Result.Failed
                                                               (e, ps'1)))
                                             ([], [], ([], munit)) a)
                                            (FStar_Tactics_Types.incr_depth
                                               (FStar_Tactics_Types.set_proofstate_range
                                                  (FStar_Tactics_Types.decr_depth
                                                     (FStar_Tactics_Types.set_proofstate_range
                                                        ps'
                                                        (FStar_Range.prims_to_fstar_range
                                                           (Prims.mk_range
                                                              "FStar.Tactics.CanonCommSemiring.fst"
                                                              (Prims.of_int (1400))
                                                              (Prims.of_int (2))
                                                              (Prims.of_int (1406))
                                                              (Prims.of_int (22))))))
                                                  (FStar_Range.prims_to_fstar_range
                                                     (Prims.mk_range
                                                        "FStar.Tactics.CanonCommSemiring.fst"
                                                        (Prims.of_int (1401))
                                                        (Prims.of_int (4))
                                                        (Prims.of_int (1405))
                                                        (Prims.of_int (29))))))
                                    with
                                    | FStar_Tactics_Result.Success (a1,ps'1)
                                        ->
                                        (match () with
                                         | () ->
                                             FStar_Tactics_Result.Success
                                               (((match a1 with
                                                  | (es,uu____7985,vm) ->
                                                      ((FStar_List_Tot_Base.rev
                                                          es), vm))),
                                                 (FStar_Tactics_Types.decr_depth
                                                    (FStar_Tactics_Types.set_proofstate_range
                                                       ps'1
                                                       (FStar_Range.prims_to_fstar_range
                                                          (Prims.mk_range
                                                             "FStar.Tactics.CanonCommSemiring.fst"
                                                             (Prims.of_int (1400))
                                                             (Prims.of_int (2))
                                                             (Prims.of_int (1406))
                                                             (Prims.of_int (22))))))))
                                    | FStar_Tactics_Result.Failed (e,ps'1) ->
                                        FStar_Tactics_Result.Failed (e, ps'1)))
                          | FStar_Tactics_Result.Failed (e,ps') ->
                              FStar_Tactics_Result.Failed (e, ps')))
  
let rec quote_spolynomial :
  'Aa .
    ('Aa ->
       (FStar_Reflection_Types.term,unit) FStar_Tactics_Effect._dm4f_TAC_repr)
      ->
      'Aa spolynomial ->
        (FStar_Reflection_Types.term,unit)
          FStar_Tactics_Effect._dm4f_TAC_repr
  =
  fun quotea  ->
    fun e  ->
      match e with
      | SPconst c ->
          (fun ps  ->
             match match (quotea c)
                           (FStar_Tactics_Types.incr_depth
                              (FStar_Tactics_Types.set_proofstate_range
                                 (FStar_Tactics_Types.incr_depth
                                    (FStar_Tactics_Types.set_proofstate_range
                                       ps
                                       (FStar_Range.prims_to_fstar_range
                                          (Prims.mk_range
                                             "FStar.Tactics.CanonCommSemiring.fst"
                                             (Prims.of_int (1410))
                                             (Prims.of_int (37))
                                             (Prims.of_int (1410))
                                             (Prims.of_int (47))))))
                                 (FStar_Range.prims_to_fstar_range
                                    (Prims.mk_range
                                       "FStar.Tactics.CanonCommSemiring.fst"
                                       (Prims.of_int (1410))
                                       (Prims.of_int (38))
                                       (Prims.of_int (1410))
                                       (Prims.of_int (46))))))
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
                                            "FStar.Tactics.CanonCommSemiring.fst"
                                            (Prims.of_int (1410))
                                            (Prims.of_int (37))
                                            (Prims.of_int (1410))
                                            (Prims.of_int (47))))))))
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
                                     "CanonCommSemiring";
                                     "SPconst"]))) a),
                          (FStar_Tactics_Types.decr_depth
                             (FStar_Tactics_Types.set_proofstate_range ps'
                                (FStar_Range.prims_to_fstar_range
                                   (Prims.mk_range
                                      "FStar.Tactics.CanonCommSemiring.fst"
                                      (Prims.of_int (1410))
                                      (Prims.of_int (17))
                                      (Prims.of_int (1410))
                                      (Prims.of_int (47))))))))
             | FStar_Tactics_Result.Failed (e1,ps') ->
                 FStar_Tactics_Result.Failed (e1, ps'))
      | SPvar x ->
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
                                             "FStar.Tactics.CanonCommSemiring.fst"
                                             (Prims.of_int (1411))
                                             (Prims.of_int (33))
                                             (Prims.of_int (1411))
                                             (Prims.of_int (60))))))
                                 (FStar_Range.prims_to_fstar_range
                                    (Prims.mk_range
                                       "FStar.Tactics.CanonCommSemiring.fst"
                                       (Prims.of_int (1411))
                                       (Prims.of_int (34))
                                       (Prims.of_int (1411))
                                       (Prims.of_int (59))))))
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
                                            "FStar.Tactics.CanonCommSemiring.fst"
                                            (Prims.of_int (1411))
                                            (Prims.of_int (33))
                                            (Prims.of_int (1411))
                                            (Prims.of_int (60))))))))
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
                                     "CanonCommSemiring";
                                     "SPvar"]))) a),
                          (FStar_Tactics_Types.decr_depth
                             (FStar_Tactics_Types.set_proofstate_range ps'
                                (FStar_Range.prims_to_fstar_range
                                   (Prims.mk_range
                                      "FStar.Tactics.CanonCommSemiring.fst"
                                      (Prims.of_int (1411))
                                      (Prims.of_int (15))
                                      (Prims.of_int (1411))
                                      (Prims.of_int (60))))))))
             | FStar_Tactics_Result.Failed (e1,ps') ->
                 FStar_Tactics_Result.Failed (e1, ps'))
      | SPplus (e1,e2) ->
          (fun ps  ->
             match match (quote_spolynomial quotea e1)
                           (FStar_Tactics_Types.incr_depth
                              (FStar_Tactics_Types.set_proofstate_range
                                 (FStar_Tactics_Types.incr_depth
                                    (FStar_Tactics_Types.set_proofstate_range
                                       ps
                                       (FStar_Range.prims_to_fstar_range
                                          (Prims.mk_range
                                             "FStar.Tactics.CanonCommSemiring.fst"
                                             (Prims.of_int (1413))
                                             (Prims.of_int (23))
                                             (Prims.of_int (1413))
                                             (Prims.of_int (81))))))
                                 (FStar_Range.prims_to_fstar_range
                                    (Prims.mk_range
                                       "FStar.Tactics.CanonCommSemiring.fst"
                                       (Prims.of_int (1413))
                                       (Prims.of_int (24))
                                       (Prims.of_int (1413))
                                       (Prims.of_int (51))))))
                   with
                   | FStar_Tactics_Result.Success (a,ps') ->
                       (match () with
                        | () ->
                            (match match (quote_spolynomial quotea e2)
                                           (FStar_Tactics_Types.incr_depth
                                              (FStar_Tactics_Types.set_proofstate_range
                                                 (FStar_Tactics_Types.incr_depth
                                                    (FStar_Tactics_Types.set_proofstate_range
                                                       (FStar_Tactics_Types.decr_depth
                                                          (FStar_Tactics_Types.set_proofstate_range
                                                             ps'
                                                             (FStar_Range.prims_to_fstar_range
                                                                (Prims.mk_range
                                                                   "FStar.Tactics.CanonCommSemiring.fst"
                                                                   (Prims.of_int (1413))
                                                                   (Prims.of_int (23))
                                                                   (Prims.of_int (1413))
                                                                   (Prims.of_int (81))))))
                                                       (FStar_Range.prims_to_fstar_range
                                                          (Prims.mk_range
                                                             "FStar.Tactics.CanonCommSemiring.fst"
                                                             (Prims.of_int (1413))
                                                             (Prims.of_int (23))
                                                             (Prims.of_int (1413))
                                                             (Prims.of_int (81))))))
                                                 (FStar_Range.prims_to_fstar_range
                                                    (Prims.mk_range
                                                       "FStar.Tactics.CanonCommSemiring.fst"
                                                       (Prims.of_int (1413))
                                                       (Prims.of_int (53))
                                                       (Prims.of_int (1413))
                                                       (Prims.of_int (80))))))
                                   with
                                   | FStar_Tactics_Result.Success (a1,ps'1)
                                       ->
                                       (match () with
                                        | () ->
                                            FStar_Tactics_Result.Success
                                              ([a1],
                                                (FStar_Tactics_Types.decr_depth
                                                   (FStar_Tactics_Types.set_proofstate_range
                                                      ps'1
                                                      (FStar_Range.prims_to_fstar_range
                                                         (Prims.mk_range
                                                            "FStar.Tactics.CanonCommSemiring.fst"
                                                            (Prims.of_int (1413))
                                                            (Prims.of_int (23))
                                                            (Prims.of_int (1413))
                                                            (Prims.of_int (81))))))))
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
                                                      "FStar.Tactics.CanonCommSemiring.fst"
                                                      (Prims.of_int (1413))
                                                      (Prims.of_int (23))
                                                      (Prims.of_int (1413))
                                                      (Prims.of_int (81))))))))
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
                                     "CanonCommSemiring";
                                     "SPplus"]))) a),
                          (FStar_Tactics_Types.decr_depth
                             (FStar_Tactics_Types.set_proofstate_range ps'
                                (FStar_Range.prims_to_fstar_range
                                   (Prims.mk_range
                                      "FStar.Tactics.CanonCommSemiring.fst"
                                      (Prims.of_int (1413))
                                      (Prims.of_int (4))
                                      (Prims.of_int (1413))
                                      (Prims.of_int (81))))))))
             | FStar_Tactics_Result.Failed (e3,ps') ->
                 FStar_Tactics_Result.Failed (e3, ps'))
      | SPmult (e1,e2) ->
          (fun ps  ->
             match match (quote_spolynomial quotea e1)
                           (FStar_Tactics_Types.incr_depth
                              (FStar_Tactics_Types.set_proofstate_range
                                 (FStar_Tactics_Types.incr_depth
                                    (FStar_Tactics_Types.set_proofstate_range
                                       ps
                                       (FStar_Range.prims_to_fstar_range
                                          (Prims.mk_range
                                             "FStar.Tactics.CanonCommSemiring.fst"
                                             (Prims.of_int (1415))
                                             (Prims.of_int (23))
                                             (Prims.of_int (1415))
                                             (Prims.of_int (81))))))
                                 (FStar_Range.prims_to_fstar_range
                                    (Prims.mk_range
                                       "FStar.Tactics.CanonCommSemiring.fst"
                                       (Prims.of_int (1415))
                                       (Prims.of_int (24))
                                       (Prims.of_int (1415))
                                       (Prims.of_int (51))))))
                   with
                   | FStar_Tactics_Result.Success (a,ps') ->
                       (match () with
                        | () ->
                            (match match (quote_spolynomial quotea e2)
                                           (FStar_Tactics_Types.incr_depth
                                              (FStar_Tactics_Types.set_proofstate_range
                                                 (FStar_Tactics_Types.incr_depth
                                                    (FStar_Tactics_Types.set_proofstate_range
                                                       (FStar_Tactics_Types.decr_depth
                                                          (FStar_Tactics_Types.set_proofstate_range
                                                             ps'
                                                             (FStar_Range.prims_to_fstar_range
                                                                (Prims.mk_range
                                                                   "FStar.Tactics.CanonCommSemiring.fst"
                                                                   (Prims.of_int (1415))
                                                                   (Prims.of_int (23))
                                                                   (Prims.of_int (1415))
                                                                   (Prims.of_int (81))))))
                                                       (FStar_Range.prims_to_fstar_range
                                                          (Prims.mk_range
                                                             "FStar.Tactics.CanonCommSemiring.fst"
                                                             (Prims.of_int (1415))
                                                             (Prims.of_int (23))
                                                             (Prims.of_int (1415))
                                                             (Prims.of_int (81))))))
                                                 (FStar_Range.prims_to_fstar_range
                                                    (Prims.mk_range
                                                       "FStar.Tactics.CanonCommSemiring.fst"
                                                       (Prims.of_int (1415))
                                                       (Prims.of_int (53))
                                                       (Prims.of_int (1415))
                                                       (Prims.of_int (80))))))
                                   with
                                   | FStar_Tactics_Result.Success (a1,ps'1)
                                       ->
                                       (match () with
                                        | () ->
                                            FStar_Tactics_Result.Success
                                              ([a1],
                                                (FStar_Tactics_Types.decr_depth
                                                   (FStar_Tactics_Types.set_proofstate_range
                                                      ps'1
                                                      (FStar_Range.prims_to_fstar_range
                                                         (Prims.mk_range
                                                            "FStar.Tactics.CanonCommSemiring.fst"
                                                            (Prims.of_int (1415))
                                                            (Prims.of_int (23))
                                                            (Prims.of_int (1415))
                                                            (Prims.of_int (81))))))))
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
                                                      "FStar.Tactics.CanonCommSemiring.fst"
                                                      (Prims.of_int (1415))
                                                      (Prims.of_int (23))
                                                      (Prims.of_int (1415))
                                                      (Prims.of_int (81))))))))
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
                                     "CanonCommSemiring";
                                     "SPmult"]))) a),
                          (FStar_Tactics_Types.decr_depth
                             (FStar_Tactics_Types.set_proofstate_range ps'
                                (FStar_Range.prims_to_fstar_range
                                   (Prims.mk_range
                                      "FStar.Tactics.CanonCommSemiring.fst"
                                      (Prims.of_int (1415))
                                      (Prims.of_int (4))
                                      (Prims.of_int (1415))
                                      (Prims.of_int (81))))))))
             | FStar_Tactics_Result.Failed (e3,ps') ->
                 FStar_Tactics_Result.Failed (e3, ps'))
  

let canon_semiring_aux :
  'Aa .
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
                'Aa -> (unit,unit) FStar_Tactics_Effect._dm4f_TAC_repr
  =
  fun ta  ->
    fun unquotea  ->
      fun quotea  ->
        fun tr  ->
          fun tadd  ->
            fun tmult  ->
              fun munit  ->
                FStar_Tactics_Derived.focus
                  (fun uu____8972  ->
                     fun ps  ->
                       match (FStar_Tactics_Builtins.norm [])
                               (FStar_Tactics_Types.incr_depth
                                  (FStar_Tactics_Types.set_proofstate_range
                                     ps
                                     (FStar_Range.prims_to_fstar_range
                                        (Prims.mk_range
                                           "FStar.Tactics.CanonCommSemiring.fst"
                                           (Prims.of_int (1436))
                                           (Prims.of_int (2))
                                           (Prims.of_int (1436))
                                           (Prims.of_int (9))))))
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
                                                           "FStar.Tactics.CanonCommSemiring.fst"
                                                           (Prims.of_int (1437))
                                                           (Prims.of_int (2))
                                                           (Prims.of_int (1481))
                                                           (Prims.of_int (42))))))
                                               (FStar_Range.prims_to_fstar_range
                                                  (Prims.mk_range
                                                     "FStar.Tactics.CanonCommSemiring.fst"
                                                     (Prims.of_int (1437))
                                                     (Prims.of_int (10))
                                                     (Prims.of_int (1437))
                                                     (Prims.of_int (21))))))
                                 with
                                 | FStar_Tactics_Result.Success (a1,ps'1) ->
                                     (match () with
                                      | () ->
                                          (match (FStar_Reflection_Formula.term_as_formula
                                                    a1)
                                                   (FStar_Tactics_Types.incr_depth
                                                      (FStar_Tactics_Types.set_proofstate_range
                                                         (FStar_Tactics_Types.decr_depth
                                                            (FStar_Tactics_Types.set_proofstate_range
                                                               ps'1
                                                               (FStar_Range.prims_to_fstar_range
                                                                  (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1438))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (1481))
                                                                    (Prims.of_int (42))))))
                                                         (FStar_Range.prims_to_fstar_range
                                                            (Prims.mk_range
                                                               "FStar.Tactics.CanonCommSemiring.fst"
                                                               (Prims.of_int (1438))
                                                               (Prims.of_int (8))
                                                               (Prims.of_int (1438))
                                                               (Prims.of_int (25))))))
                                           with
                                           | FStar_Tactics_Result.Success
                                               (a2,ps'2) ->
                                               (match () with
                                                | () ->
                                                    ((match a2 with
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
                                                               match 
                                                                 (reification
                                                                    unquotea
                                                                    quotea
                                                                    tadd
                                                                    tmult
                                                                    munit
                                                                    [t1; t2])
                                                                   (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps1
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1444))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (1444))
                                                                    (Prims.of_int (65))))))
                                                               with
                                                               | FStar_Tactics_Result.Success
                                                                   (a3,ps'3)
                                                                   ->
                                                                   (match ()
                                                                    with
                                                                    | 
                                                                    () ->
                                                                    ((match a3
                                                                    with
                                                                    | (e1::e2::[],vm)
                                                                    ->
                                                                    (fun ps2 
                                                                    ->
                                                                    match 
                                                                    (quote_vm
                                                                    ta quotea
                                                                    vm)
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1458))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (1458))
                                                                    (Prims.of_int (39))))))
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
                                                                    (quote_spolynomial
                                                                    quotea e1)
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'4
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1459))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (1476))
                                                                    (Prims.of_int (16))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1459))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (1459))
                                                                    (Prims.of_int (45))))))
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
                                                                    (quote_spolynomial
                                                                    quotea e2)
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'5
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1461))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (1476))
                                                                    (Prims.of_int (16))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1461))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (1461))
                                                                    (Prims.of_int (45))))))
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
                                                                    (FStar_Reflection_Basic.pack_ln
                                                                    (FStar_Reflection_Data.Tv_App
                                                                    ((FStar_Reflection_Basic.pack_ln
                                                                    (FStar_Reflection_Data.Tv_App
                                                                    ((FStar_Reflection_Basic.pack_ln
                                                                    (FStar_Reflection_Data.Tv_App
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
                                                                    "CanonCommSemiring";
                                                                    "semiring_reflect"]))),
                                                                    (ta,
                                                                    FStar_Reflection_Data.Q_Implicit)))),
                                                                    (tr,
                                                                    FStar_Reflection_Data.Q_Explicit)))),
                                                                    (a4,
                                                                    FStar_Reflection_Data.Q_Explicit)))),
                                                                    (a5,
                                                                    FStar_Reflection_Data.Q_Explicit)))),
                                                                    (a6,
                                                                    FStar_Reflection_Data.Q_Explicit)))),
                                                                    (t1,
                                                                    FStar_Reflection_Data.Q_Explicit)))),
                                                                    (t2,
                                                                    FStar_Reflection_Data.Q_Explicit)))))
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'6
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1463))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (1476))
                                                                    (Prims.of_int (16))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1463))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (1464))
                                                                    (Prims.of_int (64))))))
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
                                                                    (canon_norm
                                                                    ())
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'7
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1466))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (1476))
                                                                    (Prims.of_int (16))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1466))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (1466))
                                                                    (Prims.of_int (21))))))
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
                                                                    (FStar_Tactics_Derived.later
                                                                    ())
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'8
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1468))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (1476))
                                                                    (Prims.of_int (16))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1468))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (1468))
                                                                    (Prims.of_int (16))))))
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
                                                                    (canon_norm
                                                                    ())
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'9
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1470))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (1476))
                                                                    (Prims.of_int (16))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1470))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (1470))
                                                                    (Prims.of_int (21))))))
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
                                                                    (FStar_Tactics_Builtins.trefl
                                                                    ())
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'10
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1472))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (1476))
                                                                    (Prims.of_int (16))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1472))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (1472))
                                                                    (Prims.of_int (16))))))
                                                                    with
                                                                    | 
                                                                    FStar_Tactics_Result.Success
                                                                    (a11,ps'11)
                                                                    ->
                                                                    (match ()
                                                                    with
                                                                    | 
                                                                    () ->
                                                                    (match 
                                                                    (canon_norm
                                                                    ())
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'11
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1474))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (1476))
                                                                    (Prims.of_int (16))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1474))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (1474))
                                                                    (Prims.of_int (21))))))
                                                                    with
                                                                    | 
                                                                    FStar_Tactics_Result.Success
                                                                    (a12,ps'12)
                                                                    ->
                                                                    (match ()
                                                                    with
                                                                    | 
                                                                    () ->
                                                                    (FStar_Tactics_Builtins.trefl
                                                                    ())
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'12
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1476))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (1476))
                                                                    (Prims.of_int (16)))))))
                                                                    | 
                                                                    FStar_Tactics_Result.Failed
                                                                    (e,ps'12)
                                                                    ->
                                                                    FStar_Tactics_Result.Failed
                                                                    (e,
                                                                    ps'12)))
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
                                                                    ps'10)))
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
                                                                    (e, ps'6)))
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
                                                                    (e, ps'4))
                                                                    | uu____9584
                                                                    ->
                                                                    FStar_Tactics_Derived.fail
                                                                    "Unexpected"))
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1444))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (1477))
                                                                    (Prims.of_int (30)))))))
                                                               | FStar_Tactics_Result.Failed
                                                                   (e,ps'3)
                                                                   ->
                                                                   FStar_Tactics_Result.Failed
                                                                    (e, ps'3))
                                                          else
                                                            FStar_Tactics_Derived.fail
                                                              "Found equality, but terms do not have the expected type"
                                                      | uu____9611 ->
                                                          FStar_Tactics_Derived.fail
                                                            "Goal should be an equality"))
                                                      (FStar_Tactics_Types.decr_depth
                                                         (FStar_Tactics_Types.set_proofstate_range
                                                            ps'2
                                                            (FStar_Range.prims_to_fstar_range
                                                               (Prims.mk_range
                                                                  "FStar.Tactics.CanonCommSemiring.fst"
                                                                  (Prims.of_int (1438))
                                                                  (Prims.of_int (2))
                                                                  (Prims.of_int (1481))
                                                                  (Prims.of_int (42)))))))
                                           | FStar_Tactics_Result.Failed
                                               (e,ps'2) ->
                                               FStar_Tactics_Result.Failed
                                                 (e, ps'2)))
                                 | FStar_Tactics_Result.Failed (e,ps'1) ->
                                     FStar_Tactics_Result.Failed (e, ps'1)))
                       | FStar_Tactics_Result.Failed (e,ps') ->
                           FStar_Tactics_Result.Failed (e, ps'))
  
let canon_semiring :
  'Aa . 'Aa cr -> (unit,unit) FStar_Tactics_Effect._dm4f_TAC_repr =
  fun r  ->
    fun ps  ->
      match () with
      | () ->
          (match () with
           | () ->
               (match match () with
                      | () ->
                          (FStar_Tactics_Derived.norm_term steps
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
                                                    (FStar_Tactics_Types.incr_depth
                                                       (FStar_Tactics_Types.set_proofstate_range
                                                          (FStar_Tactics_Types.decr_depth
                                                             (FStar_Tactics_Types.set_proofstate_range
                                                                (FStar_Tactics_Types.incr_depth
                                                                   (FStar_Tactics_Types.set_proofstate_range
                                                                    ps
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1485))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (1485))
                                                                    (Prims.of_int (13))))))
                                                                (FStar_Range.prims_to_fstar_range
                                                                   (Prims.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1484))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (1488))
                                                                    (Prims.of_int (17))))))
                                                          (FStar_Range.prims_to_fstar_range
                                                             (Prims.mk_range
                                                                "FStar.Tactics.CanonCommSemiring.fst"
                                                                (Prims.of_int (1485))
                                                                (Prims.of_int (50))
                                                                (Prims.of_int (1485))
                                                                (Prims.of_int (59))))))
                                                    (FStar_Range.prims_to_fstar_range
                                                       (Prims.mk_range
                                                          "FStar.Tactics.CanonCommSemiring.fst"
                                                          (Prims.of_int (1484))
                                                          (Prims.of_int (2))
                                                          (Prims.of_int (1488))
                                                          (Prims.of_int (17))))))
                                              (FStar_Range.prims_to_fstar_range
                                                 (Prims.mk_range
                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                    (Prims.of_int (1486))
                                                    (Prims.of_int (4))
                                                    (Prims.of_int (1486))
                                                    (Prims.of_int (43))))))
                                        (FStar_Range.prims_to_fstar_range
                                           (Prims.mk_range
                                              "FStar.Tactics.CanonCommSemiring.fst"
                                              (Prims.of_int (1486))
                                              (Prims.of_int (21))
                                              (Prims.of_int (1486))
                                              (Prims.of_int (42))))))
                                  (FStar_Range.prims_to_fstar_range
                                     (Prims.mk_range
                                        "FStar.Tactics.CanonCommSemiring.fst"
                                        (Prims.of_int (1486))
                                        (Prims.of_int (4))
                                        (Prims.of_int (1486))
                                        (Prims.of_int (43))))))
                with
                | FStar_Tactics_Result.Success (a,ps') ->
                    (match () with
                     | () ->
                         (match match () with
                                | () ->
                                    (FStar_Tactics_Derived.norm_term steps
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
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1484))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (1488))
                                                                    (Prims.of_int (17))))))
                                                        (FStar_Range.prims_to_fstar_range
                                                           (Prims.mk_range
                                                              "FStar.Tactics.CanonCommSemiring.fst"
                                                              (Prims.of_int (1487))
                                                              (Prims.of_int (4))
                                                              (Prims.of_int (1487))
                                                              (Prims.of_int (44))))))
                                                  (FStar_Range.prims_to_fstar_range
                                                     (Prims.mk_range
                                                        "FStar.Tactics.CanonCommSemiring.fst"
                                                        (Prims.of_int (1487))
                                                        (Prims.of_int (21))
                                                        (Prims.of_int (1487))
                                                        (Prims.of_int (43))))))
                                            (FStar_Range.prims_to_fstar_range
                                               (Prims.mk_range
                                                  "FStar.Tactics.CanonCommSemiring.fst"
                                                  (Prims.of_int (1487))
                                                  (Prims.of_int (4))
                                                  (Prims.of_int (1487))
                                                  (Prims.of_int (44))))))
                          with
                          | FStar_Tactics_Result.Success (a1,ps'1) ->
                              (match () with
                               | () ->
                                   (canon_semiring_aux
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
                                      a a1
                                      (FStar_Algebra_CommMonoid.__proj__CM__item__unit
                                         (__proj__CR__item__cm_add r)))
                                     (FStar_Tactics_Types.decr_depth
                                        (FStar_Tactics_Types.set_proofstate_range
                                           ps'1
                                           (FStar_Range.prims_to_fstar_range
                                              (Prims.mk_range
                                                 "FStar.Tactics.CanonCommSemiring.fst"
                                                 (Prims.of_int (1484))
                                                 (Prims.of_int (2))
                                                 (Prims.of_int (1488))
                                                 (Prims.of_int (17)))))))
                          | FStar_Tactics_Result.Failed (e,ps'1) ->
                              FStar_Tactics_Result.Failed (e, ps'1)))
                | FStar_Tactics_Result.Failed (e,ps') ->
                    FStar_Tactics_Result.Failed (e, ps')))
  
let (int_cr : Prims.int cr) =
  CR
    (FStar_Algebra_CommMonoid.int_plus_cm,
      FStar_Algebra_CommMonoid.int_multiply_cm, (), ())
  
let (int_semiring : unit -> (unit,unit) FStar_Tactics_Effect._dm4f_TAC_repr)
  = fun uu____9827  -> canon_semiring int_cr 
