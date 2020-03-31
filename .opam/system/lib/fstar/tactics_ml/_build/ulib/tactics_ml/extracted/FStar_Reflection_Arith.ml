open Prims
type expr =
  | Lit of Prims.int 
  | Atom of Prims.nat * FStar_Reflection_Types.term 
  | Plus of expr * expr 
  | Mult of expr * expr 
  | Minus of expr * expr 
  | Land of expr * expr 
  | Lxor of expr * expr 
  | Lor of expr * expr 
  | Ladd of expr * expr 
  | Lsub of expr * expr 
  | Shl of expr * expr 
  | Shr of expr * expr 
  | Neg of expr 
  | Udiv of expr * expr 
  | Umod of expr * expr 
  | MulMod of expr * expr 
  | NatToBv of expr 
let (uu___is_Lit : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | Lit _0 -> true | uu____170 -> false
  
let (__proj__Lit__item___0 : expr -> Prims.int) =
  fun projectee  -> match projectee with | Lit _0 -> _0 
let (uu___is_Atom : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | Atom (_0,_1) -> true | uu____197 -> false
  
let (__proj__Atom__item___0 : expr -> Prims.nat) =
  fun projectee  -> match projectee with | Atom (_0,_1) -> _0 
let (__proj__Atom__item___1 : expr -> FStar_Reflection_Types.term) =
  fun projectee  -> match projectee with | Atom (_0,_1) -> _1 
let (uu___is_Plus : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | Plus (_0,_1) -> true | uu____235 -> false
  
let (__proj__Plus__item___0 : expr -> expr) =
  fun projectee  -> match projectee with | Plus (_0,_1) -> _0 
let (__proj__Plus__item___1 : expr -> expr) =
  fun projectee  -> match projectee with | Plus (_0,_1) -> _1 
let (uu___is_Mult : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | Mult (_0,_1) -> true | uu____273 -> false
  
let (__proj__Mult__item___0 : expr -> expr) =
  fun projectee  -> match projectee with | Mult (_0,_1) -> _0 
let (__proj__Mult__item___1 : expr -> expr) =
  fun projectee  -> match projectee with | Mult (_0,_1) -> _1 
let (uu___is_Minus : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | Minus (_0,_1) -> true | uu____311 -> false
  
let (__proj__Minus__item___0 : expr -> expr) =
  fun projectee  -> match projectee with | Minus (_0,_1) -> _0 
let (__proj__Minus__item___1 : expr -> expr) =
  fun projectee  -> match projectee with | Minus (_0,_1) -> _1 
let (uu___is_Land : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | Land (_0,_1) -> true | uu____349 -> false
  
let (__proj__Land__item___0 : expr -> expr) =
  fun projectee  -> match projectee with | Land (_0,_1) -> _0 
let (__proj__Land__item___1 : expr -> expr) =
  fun projectee  -> match projectee with | Land (_0,_1) -> _1 
let (uu___is_Lxor : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | Lxor (_0,_1) -> true | uu____387 -> false
  
let (__proj__Lxor__item___0 : expr -> expr) =
  fun projectee  -> match projectee with | Lxor (_0,_1) -> _0 
let (__proj__Lxor__item___1 : expr -> expr) =
  fun projectee  -> match projectee with | Lxor (_0,_1) -> _1 
let (uu___is_Lor : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | Lor (_0,_1) -> true | uu____425 -> false
  
let (__proj__Lor__item___0 : expr -> expr) =
  fun projectee  -> match projectee with | Lor (_0,_1) -> _0 
let (__proj__Lor__item___1 : expr -> expr) =
  fun projectee  -> match projectee with | Lor (_0,_1) -> _1 
let (uu___is_Ladd : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | Ladd (_0,_1) -> true | uu____463 -> false
  
let (__proj__Ladd__item___0 : expr -> expr) =
  fun projectee  -> match projectee with | Ladd (_0,_1) -> _0 
let (__proj__Ladd__item___1 : expr -> expr) =
  fun projectee  -> match projectee with | Ladd (_0,_1) -> _1 
let (uu___is_Lsub : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | Lsub (_0,_1) -> true | uu____501 -> false
  
let (__proj__Lsub__item___0 : expr -> expr) =
  fun projectee  -> match projectee with | Lsub (_0,_1) -> _0 
let (__proj__Lsub__item___1 : expr -> expr) =
  fun projectee  -> match projectee with | Lsub (_0,_1) -> _1 
let (uu___is_Shl : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | Shl (_0,_1) -> true | uu____539 -> false
  
let (__proj__Shl__item___0 : expr -> expr) =
  fun projectee  -> match projectee with | Shl (_0,_1) -> _0 
let (__proj__Shl__item___1 : expr -> expr) =
  fun projectee  -> match projectee with | Shl (_0,_1) -> _1 
let (uu___is_Shr : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | Shr (_0,_1) -> true | uu____577 -> false
  
let (__proj__Shr__item___0 : expr -> expr) =
  fun projectee  -> match projectee with | Shr (_0,_1) -> _0 
let (__proj__Shr__item___1 : expr -> expr) =
  fun projectee  -> match projectee with | Shr (_0,_1) -> _1 
let (uu___is_Neg : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | Neg _0 -> true | uu____613 -> false
  
let (__proj__Neg__item___0 : expr -> expr) =
  fun projectee  -> match projectee with | Neg _0 -> _0 
let (uu___is_Udiv : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | Udiv (_0,_1) -> true | uu____638 -> false
  
let (__proj__Udiv__item___0 : expr -> expr) =
  fun projectee  -> match projectee with | Udiv (_0,_1) -> _0 
let (__proj__Udiv__item___1 : expr -> expr) =
  fun projectee  -> match projectee with | Udiv (_0,_1) -> _1 
let (uu___is_Umod : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | Umod (_0,_1) -> true | uu____676 -> false
  
let (__proj__Umod__item___0 : expr -> expr) =
  fun projectee  -> match projectee with | Umod (_0,_1) -> _0 
let (__proj__Umod__item___1 : expr -> expr) =
  fun projectee  -> match projectee with | Umod (_0,_1) -> _1 
let (uu___is_MulMod : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | MulMod (_0,_1) -> true | uu____714 -> false
  
let (__proj__MulMod__item___0 : expr -> expr) =
  fun projectee  -> match projectee with | MulMod (_0,_1) -> _0 
let (__proj__MulMod__item___1 : expr -> expr) =
  fun projectee  -> match projectee with | MulMod (_0,_1) -> _1 
let (uu___is_NatToBv : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | NatToBv _0 -> true | uu____750 -> false
  
let (__proj__NatToBv__item___0 : expr -> expr) =
  fun projectee  -> match projectee with | NatToBv _0 -> _0 
type connective =
  | C_Lt 
  | C_Eq 
  | C_Gt 
  | C_Ne 
let (uu___is_C_Lt : connective -> Prims.bool) =
  fun projectee  -> match projectee with | C_Lt  -> true | uu____771 -> false 
let (uu___is_C_Eq : connective -> Prims.bool) =
  fun projectee  -> match projectee with | C_Eq  -> true | uu____783 -> false 
let (uu___is_C_Gt : connective -> Prims.bool) =
  fun projectee  -> match projectee with | C_Gt  -> true | uu____795 -> false 
let (uu___is_C_Ne : connective -> Prims.bool) =
  fun projectee  -> match projectee with | C_Ne  -> true | uu____807 -> false 
type prop =
  | CompProp of expr * connective * expr 
  | AndProp of prop * prop 
  | OrProp of prop * prop 
  | NotProp of prop 
let (uu___is_CompProp : prop -> Prims.bool) =
  fun projectee  ->
    match projectee with | CompProp (_0,_1,_2) -> true | uu____865 -> false
  
let (__proj__CompProp__item___0 : prop -> expr) =
  fun projectee  -> match projectee with | CompProp (_0,_1,_2) -> _0 
let (__proj__CompProp__item___1 : prop -> connective) =
  fun projectee  -> match projectee with | CompProp (_0,_1,_2) -> _1 
let (__proj__CompProp__item___2 : prop -> expr) =
  fun projectee  -> match projectee with | CompProp (_0,_1,_2) -> _2 
let (uu___is_AndProp : prop -> Prims.bool) =
  fun projectee  ->
    match projectee with | AndProp (_0,_1) -> true | uu____920 -> false
  
let (__proj__AndProp__item___0 : prop -> prop) =
  fun projectee  -> match projectee with | AndProp (_0,_1) -> _0 
let (__proj__AndProp__item___1 : prop -> prop) =
  fun projectee  -> match projectee with | AndProp (_0,_1) -> _1 
let (uu___is_OrProp : prop -> Prims.bool) =
  fun projectee  ->
    match projectee with | OrProp (_0,_1) -> true | uu____958 -> false
  
let (__proj__OrProp__item___0 : prop -> prop) =
  fun projectee  -> match projectee with | OrProp (_0,_1) -> _0 
let (__proj__OrProp__item___1 : prop -> prop) =
  fun projectee  -> match projectee with | OrProp (_0,_1) -> _1 
let (uu___is_NotProp : prop -> Prims.bool) =
  fun projectee  ->
    match projectee with | NotProp _0 -> true | uu____994 -> false
  
let (__proj__NotProp__item___0 : prop -> prop) =
  fun projectee  -> match projectee with | NotProp _0 -> _0 
let (lt : expr -> expr -> prop) =
  fun e1  -> fun e2  -> CompProp (e1, C_Lt, e2) 
let (le : expr -> expr -> prop) =
  fun e1  -> fun e2  -> CompProp (e1, C_Lt, (Plus ((Lit Prims.int_one), e2))) 
let (eq : expr -> expr -> prop) =
  fun e1  -> fun e2  -> CompProp (e1, C_Eq, e2) 
let (ne : expr -> expr -> prop) =
  fun e1  -> fun e2  -> CompProp (e1, C_Ne, e2) 
let (gt : expr -> expr -> prop) =
  fun e1  -> fun e2  -> CompProp (e1, C_Gt, e2) 
let (ge : expr -> expr -> prop) =
  fun e1  -> fun e2  -> CompProp ((Plus ((Lit Prims.int_one), e1)), C_Gt, e2) 
type st = (Prims.nat * FStar_Reflection_Types.term Prims.list)
type 'Aa tm =
  st ->
    ((Prims.string,('Aa * st)) FStar_Pervasives.either,unit)
      FStar_Tactics_Effect._dm4f_TAC_repr
let return : 'a . 'a -> 'a tm =
  fun x  ->
    fun i  ->
      fun s  ->
        FStar_Tactics_Result.Success ((FStar_Pervasives.Inr (x, i)), s)
  
let bind : 'a 'b . 'a tm -> ('a -> 'b tm) -> 'b tm =
  fun m  ->
    fun f  ->
      fun i  ->
        fun ps  ->
          match (m i)
                  (FStar_Tactics_Types.incr_depth
                     (FStar_Tactics_Types.set_proofstate_range ps
                        (FStar_Range.prims_to_fstar_range
                           (Prims.mk_range "FStar.Reflection.Arith.fst"
                              (Prims.of_int (77)) (Prims.of_int (19))
                              (Prims.of_int (77)) (Prims.of_int (22))))))
          with
          | FStar_Tactics_Result.Success (a,ps') ->
              (match () with
               | () ->
                   ((match a with
                     | FStar_Pervasives.Inr (x,j) -> f x j
                     | s ->
                         (fun s1  ->
                            FStar_Tactics_Result.Success
                              ((FStar_Pervasives.Inl
                                  (FStar_Pervasives.__proj__Inl__item__v s)),
                                s1))))
                     (FStar_Tactics_Types.decr_depth
                        (FStar_Tactics_Types.set_proofstate_range ps'
                           (FStar_Range.prims_to_fstar_range
                              (Prims.mk_range "FStar.Reflection.Arith.fst"
                                 (Prims.of_int (77)) (Prims.of_int (13))
                                 (Prims.of_int (79)) (Prims.of_int (34)))))))
          | FStar_Tactics_Result.Failed (e,ps') ->
              FStar_Tactics_Result.Failed (e, ps')
  
let lift :
  'a 'b .
    ('a -> ('b,unit) FStar_Tactics_Effect._dm4f_TAC_repr) -> 'a -> 'b tm
  =
  fun f  ->
    fun x  ->
      fun st  ->
        fun ps  ->
          match match (f x)
                        (FStar_Tactics_Types.incr_depth
                           (FStar_Tactics_Types.set_proofstate_range
                              (FStar_Tactics_Types.incr_depth
                                 (FStar_Tactics_Types.set_proofstate_range ps
                                    (FStar_Range.prims_to_fstar_range
                                       (Prims.mk_range
                                          "FStar.Reflection.Arith.fst"
                                          (Prims.of_int (83))
                                          (Prims.of_int (8))
                                          (Prims.of_int (83))
                                          (Prims.of_int (17))))))
                              (FStar_Range.prims_to_fstar_range
                                 (Prims.mk_range "FStar.Reflection.Arith.fst"
                                    (Prims.of_int (83)) (Prims.of_int (9))
                                    (Prims.of_int (83)) (Prims.of_int (12))))))
                with
                | FStar_Tactics_Result.Success (a,ps') ->
                    (match () with
                     | () ->
                         FStar_Tactics_Result.Success
                           ((a, st),
                             (FStar_Tactics_Types.decr_depth
                                (FStar_Tactics_Types.set_proofstate_range ps'
                                   (FStar_Range.prims_to_fstar_range
                                      (Prims.mk_range
                                         "FStar.Reflection.Arith.fst"
                                         (Prims.of_int (83))
                                         (Prims.of_int (8))
                                         (Prims.of_int (83))
                                         (Prims.of_int (17))))))))
                | FStar_Tactics_Result.Failed (e,ps') ->
                    FStar_Tactics_Result.Failed (e, ps')
          with
          | FStar_Tactics_Result.Success (a,ps') ->
              (match () with
               | () ->
                   FStar_Tactics_Result.Success
                     ((FStar_Pervasives.Inr a),
                       (FStar_Tactics_Types.decr_depth
                          (FStar_Tactics_Types.set_proofstate_range ps'
                             (FStar_Range.prims_to_fstar_range
                                (Prims.mk_range "FStar.Reflection.Arith.fst"
                                   (Prims.of_int (83)) (Prims.of_int (4))
                                   (Prims.of_int (83)) (Prims.of_int (17))))))))
          | FStar_Tactics_Result.Failed (e,ps') ->
              FStar_Tactics_Result.Failed (e, ps')
  
let liftM : 'a 'b . ('a -> 'b) -> 'a tm -> 'b tm =
  fun f  -> fun x  -> bind x (fun xx  -> return (f xx)) 
let liftM2 : 'a 'b 'c . ('a -> 'b -> 'c) -> 'a tm -> 'b tm -> 'c tm =
  fun f  ->
    fun x  ->
      fun y  -> bind x (fun xx  -> bind y (fun yy  -> return (f xx yy)))
  
let liftM3 :
  'a 'b 'c 'd . ('a -> 'b -> 'c -> 'd) -> 'a tm -> 'b tm -> 'c tm -> 'd tm =
  fun f  ->
    fun x  ->
      fun y  ->
        fun z  ->
          bind x
            (fun xx  ->
               bind y (fun yy  -> bind z (fun zz  -> return (f xx yy zz))))
  
let rec find_idx :
  'a .
    ('a -> Prims.bool) ->
      'a Prims.list -> (Prims.nat * 'a) FStar_Pervasives_Native.option
  =
  fun f  ->
    fun l  ->
      match l with
      | [] -> FStar_Pervasives_Native.None
      | x::xs ->
          if f x
          then FStar_Pervasives_Native.Some (Prims.int_zero, x)
          else
            (match find_idx f xs with
             | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
             | FStar_Pervasives_Native.Some (i,x1) ->
                 FStar_Pervasives_Native.Some ((i + Prims.int_one), x1))
  
let (atom : FStar_Reflection_Types.term -> expr tm) =
  fun t  ->
    fun uu____1975  ->
      fun s  ->
        FStar_Tactics_Result.Success
          ((match uu____1975 with
            | (n1,atoms) ->
                (match find_idx (FStar_Reflection_Basic.term_eq t) atoms with
                 | FStar_Pervasives_Native.None  ->
                     FStar_Pervasives.Inr
                       ((Atom (n1, t)), ((n1 + Prims.int_one), (t :: atoms)))
                 | FStar_Pervasives_Native.Some (i,t1) ->
                     FStar_Pervasives.Inr
                       ((Atom (((n1 - Prims.int_one) - i), t1)), (n1, atoms)))),
            s)
  
let fail : 'Aa . Prims.string -> 'Aa tm =
  fun s  ->
    fun i  ->
      fun s1  -> FStar_Tactics_Result.Success ((FStar_Pervasives.Inl s), s1)
  
type ('Aa,'Ap) refined_list_t = 'Aa Prims.list
let rec list_unref : 'Aa 'Ap . ('Aa,'Ap) refined_list_t -> 'Aa Prims.list =
  fun l  -> match l with | [] -> [] | x::xs -> x :: (list_unref xs) 
let (collect_app_ref :
  FStar_Reflection_Types.term ->
    (FStar_Reflection_Types.term *
      (FStar_Reflection_Data.argv,(FStar_Reflection_Types.term,FStar_Reflection_Types.term,
                                    unit,unit) Prims.precedes)
      refined_list_t))
  = fun t  -> FStar_Reflection_Derived_Lemmas.collect_app_ref t 
let rec (as_arith_expr : FStar_Reflection_Types.term -> expr tm) =
  fun t  ->
    let uu____2246 = collect_app_ref t  in
    match uu____2246 with
    | (hd1,tl1) ->
        let tl2 = list_unref tl1  in
        (match ((FStar_Reflection_Basic.inspect_ln hd1), tl2) with
         | (FStar_Reflection_Data.Tv_FVar
            fv,(e1,FStar_Reflection_Data.Q_Implicit )::(e2,FStar_Reflection_Data.Q_Explicit
                                                        )::(e3,FStar_Reflection_Data.Q_Explicit
                                                            )::[])
             ->
             let qn = FStar_Reflection_Basic.inspect_fv fv  in
             let e2' = as_arith_expr e2  in
             let e3' = as_arith_expr e3  in
             if qn = FStar_Reflection_Const.land_qn
             then
               liftM2 (fun _2362  -> fun _2363  -> Land (_2362, _2363)) e2'
                 e3'
             else
               if qn = FStar_Reflection_Const.lxor_qn
               then
                 liftM2 (fun _2370  -> fun _2371  -> Lxor (_2370, _2371)) e2'
                   e3'
               else
                 if qn = FStar_Reflection_Const.lor_qn
                 then
                   liftM2 (fun _2378  -> fun _2379  -> Lor (_2378, _2379))
                     e2' e3'
                 else
                   if qn = FStar_Reflection_Const.shiftr_qn
                   then
                     liftM2 (fun _2386  -> fun _2387  -> Shr (_2386, _2387))
                       e2' e3'
                   else
                     if qn = FStar_Reflection_Const.shiftl_qn
                     then
                       liftM2
                         (fun _2394  -> fun _2395  -> Shl (_2394, _2395)) e2'
                         e3'
                     else
                       if qn = FStar_Reflection_Const.udiv_qn
                       then
                         liftM2
                           (fun _2402  -> fun _2403  -> Udiv (_2402, _2403))
                           e2' e3'
                       else
                         if qn = FStar_Reflection_Const.umod_qn
                         then
                           liftM2
                             (fun _2410  -> fun _2411  -> Umod (_2410, _2411))
                             e2' e3'
                         else
                           if qn = FStar_Reflection_Const.mul_mod_qn
                           then
                             liftM2
                               (fun _2418  ->
                                  fun _2419  -> MulMod (_2418, _2419)) e2'
                               e3'
                           else
                             if qn = FStar_Reflection_Const.ladd_qn
                             then
                               liftM2
                                 (fun _2426  ->
                                    fun _2427  -> Ladd (_2426, _2427)) e2'
                                 e3'
                             else
                               if qn = FStar_Reflection_Const.lsub_qn
                               then
                                 liftM2
                                   (fun _2434  ->
                                      fun _2435  -> Lsub (_2434, _2435)) e2'
                                   e3'
                               else atom t
         | (FStar_Reflection_Data.Tv_FVar
            fv,(l,FStar_Reflection_Data.Q_Explicit )::(r,FStar_Reflection_Data.Q_Explicit
                                                       )::[])
             ->
             let qn = FStar_Reflection_Basic.inspect_fv fv  in
             let ll = as_arith_expr l  in
             let rr = as_arith_expr r  in
             if qn = FStar_Reflection_Const.add_qn
             then
               liftM2 (fun _2475  -> fun _2476  -> Plus (_2475, _2476)) ll rr
             else
               if qn = FStar_Reflection_Const.minus_qn
               then
                 liftM2 (fun _2483  -> fun _2484  -> Minus (_2483, _2484)) ll
                   rr
               else
                 if qn = FStar_Reflection_Const.mult_qn
                 then
                   liftM2 (fun _2491  -> fun _2492  -> Mult (_2491, _2492))
                     ll rr
                 else
                   if qn = FStar_Reflection_Const.mult'_qn
                   then
                     liftM2 (fun _2499  -> fun _2500  -> Mult (_2499, _2500))
                       ll rr
                   else atom t
         | (FStar_Reflection_Data.Tv_FVar
            fv,(l,FStar_Reflection_Data.Q_Implicit )::(r,FStar_Reflection_Data.Q_Explicit
                                                       )::[])
             ->
             let qn = FStar_Reflection_Basic.inspect_fv fv  in
             let ll = as_arith_expr l  in
             let rr = as_arith_expr r  in
             if qn = FStar_Reflection_Const.nat_bv_qn
             then liftM (fun _2540  -> NatToBv _2540) rr
             else atom t
         | (FStar_Reflection_Data.Tv_FVar
            fv,(a,FStar_Reflection_Data.Q_Explicit )::[]) ->
             let qn = FStar_Reflection_Basic.inspect_fv fv  in
             let aa = as_arith_expr a  in
             if qn = FStar_Reflection_Const.neg_qn
             then liftM (fun _2570  -> Neg _2570) aa
             else atom t
         | (FStar_Reflection_Data.Tv_Const (FStar_Reflection_Data.C_Int
            i),uu____2574) -> return (Lit i)
         | uu____2588 -> atom t)
  
let (is_arith_expr : FStar_Reflection_Types.term -> expr tm) =
  fun t  ->
    bind (as_arith_expr t)
      (fun a  ->
         match a with
         | Atom (uu____2633,t1) ->
             let uu____2635 = collect_app_ref t1  in
             (match uu____2635 with
              | (hd1,tl1) ->
                  (match ((FStar_Reflection_Basic.inspect_ln hd1), tl1) with
                   | (FStar_Reflection_Data.Tv_FVar uu____2692,[]) ->
                       return a
                   | (FStar_Reflection_Data.Tv_BVar uu____2695,[]) ->
                       return a
                   | (FStar_Reflection_Data.Tv_Var uu____2698,[]) -> return a
                   | uu____2701 ->
                       fail
                         (Prims.strcat "not an arithmetic expression: ("
                            (Prims.strcat
                               (FStar_Reflection_Basic.term_to_string t1) ")"))))
         | uu____2710 -> return a)
  
let rec (is_arith_prop :
  FStar_Reflection_Types.term ->
    st ->
      ((Prims.string,(prop * st)) FStar_Pervasives.either,unit)
        FStar_Tactics_Effect._dm4f_TAC_repr)
  =
  fun t  ->
    fun i  ->
      bind (lift FStar_Reflection_Formula.term_as_formula t)
        (fun f  ->
           match f with
           | FStar_Reflection_Formula.Comp
               (FStar_Reflection_Formula.Eq uu____2818,l,r) ->
               liftM2 eq (is_arith_expr l) (is_arith_expr r)
           | FStar_Reflection_Formula.Comp
               (FStar_Reflection_Formula.BoolEq uu____2823,l,r) ->
               liftM2 eq (is_arith_expr l) (is_arith_expr r)
           | FStar_Reflection_Formula.Comp (FStar_Reflection_Formula.Lt ,l,r)
               -> liftM2 lt (is_arith_expr l) (is_arith_expr r)
           | FStar_Reflection_Formula.Comp (FStar_Reflection_Formula.Le ,l,r)
               -> liftM2 le (is_arith_expr l) (is_arith_expr r)
           | FStar_Reflection_Formula.And (l,r) ->
               liftM2 (fun _2834  -> fun _2835  -> AndProp (_2834, _2835))
                 (is_arith_prop l) (is_arith_prop r)
           | FStar_Reflection_Formula.Or (l,r) ->
               liftM2 (fun _2838  -> fun _2839  -> OrProp (_2838, _2839))
                 (is_arith_prop l) (is_arith_prop r)
           | uu____2840 ->
               fail
                 (Prims.strcat "connector ("
                    (Prims.strcat (FStar_Reflection_Basic.term_to_string t)
                       ")"))) i
  
let run_tm :
  'a .
    'a tm ->
      ((Prims.string,'a) FStar_Pervasives.either,unit)
        FStar_Tactics_Effect._dm4f_TAC_repr
  =
  fun m  ->
    fun ps  ->
      match (m (Prims.int_zero, []))
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "FStar.Reflection.Arith.fst"
                          (Prims.of_int (214)) (Prims.of_int (10))
                          (Prims.of_int (214)) (Prims.of_int (19))))))
      with
      | FStar_Tactics_Result.Success (a,ps') ->
          (match () with
           | () ->
               ((match a with
                 | FStar_Pervasives.Inr (x,uu____2998) ->
                     (fun s  ->
                        FStar_Tactics_Result.Success
                          ((FStar_Pervasives.Inr x), s))
                 | s ->
                     (fun s1  ->
                        FStar_Tactics_Result.Success
                          ((FStar_Pervasives.Inl
                              (FStar_Pervasives.__proj__Inl__item__v s)), s1))))
                 (FStar_Tactics_Types.decr_depth
                    (FStar_Tactics_Types.set_proofstate_range ps'
                       (FStar_Range.prims_to_fstar_range
                          (Prims.mk_range "FStar.Reflection.Arith.fst"
                             (Prims.of_int (214)) (Prims.of_int (4))
                             (Prims.of_int (216)) (Prims.of_int (25)))))))
      | FStar_Tactics_Result.Failed (e,ps') ->
          FStar_Tactics_Result.Failed (e, ps')
  
let rec (expr_to_string : expr -> Prims.string) =
  fun e  ->
    match e with
    | Atom (i,uu____3103) -> Prims.strcat "a" (Prims.string_of_int i)
    | Lit i -> Prims.string_of_int i
    | Plus (l,r) ->
        Prims.strcat "("
          (Prims.strcat (expr_to_string l)
             (Prims.strcat " + " (Prims.strcat (expr_to_string r) ")")))
    | Minus (l,r) ->
        Prims.strcat "("
          (Prims.strcat (expr_to_string l)
             (Prims.strcat " - " (Prims.strcat (expr_to_string r) ")")))
    | Mult (l,r) ->
        Prims.strcat "("
          (Prims.strcat (expr_to_string l)
             (Prims.strcat " * " (Prims.strcat (expr_to_string r) ")")))
    | Neg l -> Prims.strcat "(- " (Prims.strcat (expr_to_string l) ")")
    | Land (l,r) ->
        Prims.strcat "("
          (Prims.strcat (expr_to_string l)
             (Prims.strcat " & " (Prims.strcat (expr_to_string r) ")")))
    | Lor (l,r) ->
        Prims.strcat "("
          (Prims.strcat (expr_to_string l)
             (Prims.strcat " | " (Prims.strcat (expr_to_string r) ")")))
    | Lxor (l,r) ->
        Prims.strcat "("
          (Prims.strcat (expr_to_string l)
             (Prims.strcat " ^ " (Prims.strcat (expr_to_string r) ")")))
    | Ladd (l,r) ->
        Prims.strcat "("
          (Prims.strcat (expr_to_string l)
             (Prims.strcat " >> " (Prims.strcat (expr_to_string r) ")")))
    | Lsub (l,r) ->
        Prims.strcat "("
          (Prims.strcat (expr_to_string l)
             (Prims.strcat " >> " (Prims.strcat (expr_to_string r) ")")))
    | Shl (l,r) ->
        Prims.strcat "("
          (Prims.strcat (expr_to_string l)
             (Prims.strcat " << " (Prims.strcat (expr_to_string r) ")")))
    | Shr (l,r) ->
        Prims.strcat "("
          (Prims.strcat (expr_to_string l)
             (Prims.strcat " >> " (Prims.strcat (expr_to_string r) ")")))
    | NatToBv l ->
        Prims.strcat "("
          (Prims.strcat "to_vec " (Prims.strcat (expr_to_string l) ")"))
    | Udiv (l,r) ->
        Prims.strcat "("
          (Prims.strcat (expr_to_string l)
             (Prims.strcat " / " (Prims.strcat (expr_to_string r) ")")))
    | Umod (l,r) ->
        Prims.strcat "("
          (Prims.strcat (expr_to_string l)
             (Prims.strcat " % " (Prims.strcat (expr_to_string r) ")")))
    | MulMod (l,r) ->
        Prims.strcat "("
          (Prims.strcat (expr_to_string l)
             (Prims.strcat " ** " (Prims.strcat (expr_to_string r) ")")))
  
let rec (compare_expr : expr -> expr -> FStar_Order.order) =
  fun e1  ->
    fun e2  ->
      match (e1, e2) with
      | (Lit i,Lit j) -> FStar_Order.compare_int i j
      | (Atom (uu____3246,t),Atom (uu____3248,s)) ->
          FStar_Reflection_Derived.compare_term t s
      | (Plus (l1,l2),Plus (r1,r2)) ->
          FStar_Order.lex (compare_expr l1 r1)
            (fun uu____3255  -> compare_expr l2 r2)
      | (Minus (l1,l2),Minus (r1,r2)) ->
          FStar_Order.lex (compare_expr l1 r1)
            (fun uu____3261  -> compare_expr l2 r2)
      | (Mult (l1,l2),Mult (r1,r2)) ->
          FStar_Order.lex (compare_expr l1 r1)
            (fun uu____3267  -> compare_expr l2 r2)
      | (Neg e11,Neg e21) -> compare_expr e11 e21
      | (Lit uu____3270,uu____3271) -> FStar_Order.Lt
      | (uu____3273,Lit uu____3274) -> FStar_Order.Gt
      | (Atom (uu____3276,uu____3277),uu____3278) -> FStar_Order.Lt
      | (uu____3279,Atom (uu____3280,uu____3281)) -> FStar_Order.Gt
      | (Plus (uu____3282,uu____3283),uu____3284) -> FStar_Order.Lt
      | (uu____3285,Plus (uu____3286,uu____3287)) -> FStar_Order.Gt
      | (Mult (uu____3288,uu____3289),uu____3290) -> FStar_Order.Lt
      | (uu____3291,Mult (uu____3292,uu____3293)) -> FStar_Order.Gt
      | (Neg uu____3294,uu____3295) -> FStar_Order.Lt
      | (uu____3296,Neg uu____3297) -> FStar_Order.Gt
      | uu____3298 -> FStar_Order.Gt
  