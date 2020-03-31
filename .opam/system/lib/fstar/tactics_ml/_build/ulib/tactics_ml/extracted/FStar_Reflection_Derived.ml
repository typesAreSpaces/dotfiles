open Prims
let (name_of_bv : FStar_Reflection_Types.bv -> Prims.string) =
  fun bv  ->
    (FStar_Reflection_Basic.inspect_bv bv).FStar_Reflection_Data.bv_ppname
  
let (type_of_bv : FStar_Reflection_Types.bv -> FStar_Reflection_Types.typ) =
  fun bv  ->
    (FStar_Reflection_Basic.inspect_bv bv).FStar_Reflection_Data.bv_sort
  
let (bv_to_string : FStar_Reflection_Types.bv -> Prims.string) =
  fun bv  ->
    let bvv = FStar_Reflection_Basic.inspect_bv bv  in
    Prims.strcat "("
      (Prims.strcat bvv.FStar_Reflection_Data.bv_ppname
         (Prims.strcat ":"
            (Prims.strcat
               (FStar_Reflection_Basic.term_to_string
                  bvv.FStar_Reflection_Data.bv_sort) ")")))
  
let (bv_of_binder :
  FStar_Reflection_Types.binder -> FStar_Reflection_Types.bv) =
  fun b  ->
    let uu____37 = FStar_Reflection_Basic.inspect_binder b  in
    match uu____37 with | (bv,uu____43) -> bv
  
let (mk_binder : FStar_Reflection_Types.bv -> FStar_Reflection_Types.binder)
  =
  fun bv  ->
    FStar_Reflection_Basic.pack_binder bv FStar_Reflection_Data.Q_Explicit
  
let (name_of_binder : FStar_Reflection_Types.binder -> Prims.string) =
  fun b  -> name_of_bv (bv_of_binder b) 
let (type_of_binder :
  FStar_Reflection_Types.binder -> FStar_Reflection_Types.typ) =
  fun b  -> type_of_bv (bv_of_binder b) 
let (binder_to_string : FStar_Reflection_Types.binder -> Prims.string) =
  fun b  -> bv_to_string (bv_of_binder b) 
let rec (flatten_name : FStar_Reflection_Types.name -> Prims.string) =
  fun ns  ->
    match ns with
    | [] -> ""
    | n1::[] -> n1
    | n1::ns1 -> Prims.strcat n1 (Prims.strcat "." (flatten_name ns1))
  
let rec (collect_app' :
  FStar_Reflection_Data.argv Prims.list ->
    FStar_Reflection_Types.term ->
      (FStar_Reflection_Types.term * FStar_Reflection_Data.argv Prims.list))
  =
  fun args  ->
    fun t  ->
      match FStar_Reflection_Basic.inspect_ln t with
      | FStar_Reflection_Data.Tv_App (l,r) -> collect_app' (r :: args) l
      | uu____129 -> (t, args)
  
let (collect_app :
  FStar_Reflection_Types.term ->
    (FStar_Reflection_Types.term * FStar_Reflection_Data.argv Prims.list))
  = collect_app' [] 
let rec (mk_app :
  FStar_Reflection_Types.term ->
    FStar_Reflection_Data.argv Prims.list -> FStar_Reflection_Types.term)
  =
  fun t  ->
    fun args  ->
      match args with
      | [] -> t
      | x::xs ->
          mk_app
            (FStar_Reflection_Basic.pack_ln
               (FStar_Reflection_Data.Tv_App (t, x))) xs
  
let (mk_e_app :
  FStar_Reflection_Types.term ->
    FStar_Reflection_Types.term Prims.list -> FStar_Reflection_Types.term)
  =
  fun t  ->
    fun args  ->
      let e t1 = (t1, FStar_Reflection_Data.Q_Explicit)  in
      mk_app t (FStar_List_Tot_Base.map e args)
  
let rec (mk_tot_arr_ln :
  FStar_Reflection_Types.binder Prims.list ->
    FStar_Reflection_Types.term -> FStar_Reflection_Types.term)
  =
  fun bs  ->
    fun cod  ->
      match bs with
      | [] -> cod
      | b::bs1 ->
          FStar_Reflection_Basic.pack_ln
            (FStar_Reflection_Data.Tv_Arrow
               (b,
                 (FStar_Reflection_Basic.pack_comp
                    (FStar_Reflection_Data.C_Total
                       ((mk_tot_arr_ln bs1 cod),
                         FStar_Pervasives_Native.None)))))
  
let rec (collect_arr' :
  FStar_Reflection_Types.binder Prims.list ->
    FStar_Reflection_Types.comp ->
      (FStar_Reflection_Types.binder Prims.list *
        FStar_Reflection_Types.comp))
  =
  fun bs  ->
    fun c  ->
      match FStar_Reflection_Basic.inspect_comp c with
      | FStar_Reflection_Data.C_Total (t,uu____249) ->
          (match FStar_Reflection_Basic.inspect_ln t with
           | FStar_Reflection_Data.Tv_Arrow (b,c1) ->
               collect_arr' (b :: bs) c1
           | uu____254 -> (bs, c))
      | uu____257 -> (bs, c)
  
let (collect_arr_ln_bs :
  FStar_Reflection_Types.typ ->
    (FStar_Reflection_Types.binder Prims.list * FStar_Reflection_Types.comp))
  =
  fun t  ->
    let uu____276 =
      collect_arr' []
        (FStar_Reflection_Basic.pack_comp
           (FStar_Reflection_Data.C_Total (t, FStar_Pervasives_Native.None)))
       in
    match uu____276 with | (bs,c) -> ((FStar_List_Tot_Base.rev bs), c)
  
let (collect_arr_ln :
  FStar_Reflection_Types.typ ->
    (FStar_Reflection_Types.typ Prims.list * FStar_Reflection_Types.comp))
  =
  fun t  ->
    let uu____308 =
      collect_arr' []
        (FStar_Reflection_Basic.pack_comp
           (FStar_Reflection_Data.C_Total (t, FStar_Pervasives_Native.None)))
       in
    match uu____308 with
    | (bs,c) ->
        let ts = FStar_List_Tot_Base.map type_of_binder bs  in
        ((FStar_List_Tot_Base.rev ts), c)
  
let rec (collect_abs' :
  FStar_Reflection_Types.binder Prims.list ->
    FStar_Reflection_Types.term ->
      (FStar_Reflection_Types.binder Prims.list *
        FStar_Reflection_Types.term))
  =
  fun bs  ->
    fun t  ->
      match FStar_Reflection_Basic.inspect_ln t with
      | FStar_Reflection_Data.Tv_Abs (b,t') -> collect_abs' (b :: bs) t'
      | uu____354 -> (bs, t)
  
let (collect_abs_ln :
  FStar_Reflection_Types.term ->
    (FStar_Reflection_Types.binder Prims.list * FStar_Reflection_Types.term))
  =
  fun t  ->
    let uu____373 = collect_abs' [] t  in
    match uu____373 with | (bs,t') -> ((FStar_List_Tot_Base.rev bs), t')
  
let (explode_qn : Prims.string -> Prims.string Prims.list) =
  FStar_String.split [46] 
let (implode_qn : Prims.string Prims.list -> Prims.string) =
  FStar_String.concat "." 
let (fv_to_string : FStar_Reflection_Types.fv -> Prims.string) =
  fun fv  -> implode_qn (FStar_Reflection_Basic.inspect_fv fv) 
let (compare_name :
  FStar_Reflection_Types.name ->
    FStar_Reflection_Types.name -> FStar_Order.order)
  =
  fun n1  ->
    fun n2  ->
      FStar_Order.compare_list
        (fun s1  ->
           fun s2  -> FStar_Order.order_from_int (FStar_String.compare s1 s2))
        n1 n2
  
let (compare_fv :
  FStar_Reflection_Types.fv -> FStar_Reflection_Types.fv -> FStar_Order.order)
  =
  fun f1  ->
    fun f2  ->
      compare_name (FStar_Reflection_Basic.inspect_fv f1)
        (FStar_Reflection_Basic.inspect_fv f2)
  
let (compare_const :
  FStar_Reflection_Data.vconst ->
    FStar_Reflection_Data.vconst -> FStar_Order.order)
  =
  fun c1  ->
    fun c2  ->
      match (c1, c2) with
      | (FStar_Reflection_Data.C_Unit ,FStar_Reflection_Data.C_Unit ) ->
          FStar_Order.Eq
      | (FStar_Reflection_Data.C_Int i,FStar_Reflection_Data.C_Int j) ->
          FStar_Order.order_from_int (i - j)
      | (FStar_Reflection_Data.C_True ,FStar_Reflection_Data.C_True ) ->
          FStar_Order.Eq
      | (FStar_Reflection_Data.C_False ,FStar_Reflection_Data.C_False ) ->
          FStar_Order.Eq
      | (FStar_Reflection_Data.C_String s1,FStar_Reflection_Data.C_String s2)
          -> FStar_Order.order_from_int (FStar_String.compare s1 s2)
      | (FStar_Reflection_Data.C_Range r1,FStar_Reflection_Data.C_Range r2)
          -> FStar_Order.Eq
      | (FStar_Reflection_Data.C_Reify ,FStar_Reflection_Data.C_Reify ) ->
          FStar_Order.Eq
      | (FStar_Reflection_Data.C_Reflect l1,FStar_Reflection_Data.C_Reflect
         l2) -> compare_name l1 l2
      | (FStar_Reflection_Data.C_Unit ,uu____516) -> FStar_Order.Lt
      | (uu____517,FStar_Reflection_Data.C_Unit ) -> FStar_Order.Gt
      | (FStar_Reflection_Data.C_Int uu____518,uu____519) -> FStar_Order.Lt
      | (uu____521,FStar_Reflection_Data.C_Int uu____522) -> FStar_Order.Gt
      | (FStar_Reflection_Data.C_True ,uu____524) -> FStar_Order.Lt
      | (uu____525,FStar_Reflection_Data.C_True ) -> FStar_Order.Gt
      | (FStar_Reflection_Data.C_False ,uu____526) -> FStar_Order.Lt
      | (uu____527,FStar_Reflection_Data.C_False ) -> FStar_Order.Gt
      | (FStar_Reflection_Data.C_String uu____528,uu____529) ->
          FStar_Order.Lt
      | (uu____531,FStar_Reflection_Data.C_String uu____532) ->
          FStar_Order.Gt
      | (FStar_Reflection_Data.C_Range uu____534,uu____535) -> FStar_Order.Lt
      | (uu____536,FStar_Reflection_Data.C_Range uu____537) -> FStar_Order.Gt
      | (FStar_Reflection_Data.C_Reify ,uu____538) -> FStar_Order.Lt
      | (uu____539,FStar_Reflection_Data.C_Reify ) -> FStar_Order.Gt
      | (FStar_Reflection_Data.C_Reflect uu____540,uu____541) ->
          FStar_Order.Lt
      | (uu____543,FStar_Reflection_Data.C_Reflect uu____544) ->
          FStar_Order.Gt
  
let (compare_binder :
  FStar_Reflection_Types.binder ->
    FStar_Reflection_Types.binder -> FStar_Order.order)
  =
  fun b1  ->
    fun b2  ->
      let uu____565 = FStar_Reflection_Basic.inspect_binder b1  in
      match uu____565 with
      | (bv1,uu____571) ->
          let uu____572 = FStar_Reflection_Basic.inspect_binder b2  in
          (match uu____572 with
           | (bv2,uu____578) -> FStar_Reflection_Basic.compare_bv bv1 bv2)
  
let rec (compare_term :
  FStar_Reflection_Types.term ->
    FStar_Reflection_Types.term -> FStar_Order.order)
  =
  fun s  ->
    fun t  ->
      match ((FStar_Reflection_Basic.inspect_ln s),
              (FStar_Reflection_Basic.inspect_ln t))
      with
      | (FStar_Reflection_Data.Tv_Var sv,FStar_Reflection_Data.Tv_Var tv) ->
          FStar_Reflection_Basic.compare_bv sv tv
      | (FStar_Reflection_Data.Tv_BVar sv,FStar_Reflection_Data.Tv_BVar tv)
          -> FStar_Reflection_Basic.compare_bv sv tv
      | (FStar_Reflection_Data.Tv_FVar sv,FStar_Reflection_Data.Tv_FVar tv)
          -> compare_fv sv tv
      | (FStar_Reflection_Data.Tv_App (h1,a1),FStar_Reflection_Data.Tv_App
         (h2,a2)) ->
          FStar_Order.lex (compare_term h1 h2)
            (fun uu____805  -> compare_argv a1 a2)
      | (FStar_Reflection_Data.Tv_Abs (b1,e1),FStar_Reflection_Data.Tv_Abs
         (b2,e2)) ->
          FStar_Order.lex (compare_binder b1 b2)
            (fun uu____811  -> compare_term e1 e2)
      | (FStar_Reflection_Data.Tv_Refine
         (bv1,e1),FStar_Reflection_Data.Tv_Refine (bv2,e2)) ->
          FStar_Order.lex (FStar_Reflection_Basic.compare_bv bv1 bv2)
            (fun uu____817  -> compare_term e1 e2)
      | (FStar_Reflection_Data.Tv_Arrow
         (b1,e1),FStar_Reflection_Data.Tv_Arrow (b2,e2)) ->
          FStar_Order.lex (compare_binder b1 b2)
            (fun uu____823  -> compare_comp e1 e2)
      | (FStar_Reflection_Data.Tv_Type (),FStar_Reflection_Data.Tv_Type ())
          -> FStar_Order.Eq
      | (FStar_Reflection_Data.Tv_Const c1,FStar_Reflection_Data.Tv_Const c2)
          -> compare_const c1 c2
      | (FStar_Reflection_Data.Tv_Uvar
         (u1,uu____827),FStar_Reflection_Data.Tv_Uvar (u2,uu____829)) ->
          FStar_Order.compare_int u1 u2
      | (FStar_Reflection_Data.Tv_Let
         (_r1,_attrs1,bv1,t1,t1'),FStar_Reflection_Data.Tv_Let
         (_r2,_attrs2,bv2,t2,t2')) ->
          FStar_Order.lex (FStar_Reflection_Basic.compare_bv bv1 bv2)
            (fun uu____849  ->
               FStar_Order.lex (compare_term t1 t2)
                 (fun uu____851  -> compare_term t1' t2'))
      | (FStar_Reflection_Data.Tv_Match
         (uu____852,uu____853),FStar_Reflection_Data.Tv_Match
         (uu____854,uu____855)) -> FStar_Order.Eq
      | (FStar_Reflection_Data.Tv_AscribedT
         (e1,t1,tac1),FStar_Reflection_Data.Tv_AscribedT (e2,t2,tac2)) ->
          FStar_Order.lex (compare_term e1 e2)
            (fun uu____871  ->
               FStar_Order.lex (compare_term t1 t2)
                 (fun uu____873  ->
                    match (tac1, tac2) with
                    | (FStar_Pervasives_Native.None
                       ,FStar_Pervasives_Native.None ) -> FStar_Order.Eq
                    | (FStar_Pervasives_Native.None ,uu____882) ->
                        FStar_Order.Lt
                    | (uu____889,FStar_Pervasives_Native.None ) ->
                        FStar_Order.Gt
                    | (FStar_Pervasives_Native.Some
                       e11,FStar_Pervasives_Native.Some e21) ->
                        compare_term e11 e21))
      | (FStar_Reflection_Data.Tv_AscribedC
         (e1,c1,tac1),FStar_Reflection_Data.Tv_AscribedC (e2,c2,tac2)) ->
          FStar_Order.lex (compare_term e1 e2)
            (fun uu____913  ->
               FStar_Order.lex (compare_comp c1 c2)
                 (fun uu____915  ->
                    match (tac1, tac2) with
                    | (FStar_Pervasives_Native.None
                       ,FStar_Pervasives_Native.None ) -> FStar_Order.Eq
                    | (FStar_Pervasives_Native.None ,uu____924) ->
                        FStar_Order.Lt
                    | (uu____931,FStar_Pervasives_Native.None ) ->
                        FStar_Order.Gt
                    | (FStar_Pervasives_Native.Some
                       e11,FStar_Pervasives_Native.Some e21) ->
                        compare_term e11 e21))
      | (FStar_Reflection_Data.Tv_Unknown ,FStar_Reflection_Data.Tv_Unknown )
          -> FStar_Order.Eq
      | (FStar_Reflection_Data.Tv_Var uu____944,uu____945) -> FStar_Order.Lt
      | (uu____946,FStar_Reflection_Data.Tv_Var uu____947) -> FStar_Order.Gt
      | (FStar_Reflection_Data.Tv_BVar uu____948,uu____949) -> FStar_Order.Lt
      | (uu____950,FStar_Reflection_Data.Tv_BVar uu____951) -> FStar_Order.Gt
      | (FStar_Reflection_Data.Tv_FVar uu____952,uu____953) -> FStar_Order.Lt
      | (uu____954,FStar_Reflection_Data.Tv_FVar uu____955) -> FStar_Order.Gt
      | (FStar_Reflection_Data.Tv_App (uu____956,uu____957),uu____958) ->
          FStar_Order.Lt
      | (uu____959,FStar_Reflection_Data.Tv_App (uu____960,uu____961)) ->
          FStar_Order.Gt
      | (FStar_Reflection_Data.Tv_Abs (uu____962,uu____963),uu____964) ->
          FStar_Order.Lt
      | (uu____965,FStar_Reflection_Data.Tv_Abs (uu____966,uu____967)) ->
          FStar_Order.Gt
      | (FStar_Reflection_Data.Tv_Arrow (uu____968,uu____969),uu____970) ->
          FStar_Order.Lt
      | (uu____971,FStar_Reflection_Data.Tv_Arrow (uu____972,uu____973)) ->
          FStar_Order.Gt
      | (FStar_Reflection_Data.Tv_Type (),uu____974) -> FStar_Order.Lt
      | (uu____975,FStar_Reflection_Data.Tv_Type ()) -> FStar_Order.Gt
      | (FStar_Reflection_Data.Tv_Refine (uu____976,uu____977),uu____978) ->
          FStar_Order.Lt
      | (uu____979,FStar_Reflection_Data.Tv_Refine (uu____980,uu____981)) ->
          FStar_Order.Gt
      | (FStar_Reflection_Data.Tv_Const uu____982,uu____983) ->
          FStar_Order.Lt
      | (uu____984,FStar_Reflection_Data.Tv_Const uu____985) ->
          FStar_Order.Gt
      | (FStar_Reflection_Data.Tv_Uvar (uu____986,uu____987),uu____988) ->
          FStar_Order.Lt
      | (uu____990,FStar_Reflection_Data.Tv_Uvar (uu____991,uu____992)) ->
          FStar_Order.Gt
      | (FStar_Reflection_Data.Tv_Match (uu____994,uu____995),uu____996) ->
          FStar_Order.Lt
      | (uu____999,FStar_Reflection_Data.Tv_Match (uu____1000,uu____1001)) ->
          FStar_Order.Gt
      | (FStar_Reflection_Data.Tv_AscribedT
         (uu____1004,uu____1005,uu____1006),uu____1007) -> FStar_Order.Lt
      | (uu____1010,FStar_Reflection_Data.Tv_AscribedT
         (uu____1011,uu____1012,uu____1013)) -> FStar_Order.Gt
      | (FStar_Reflection_Data.Tv_AscribedC
         (uu____1016,uu____1017,uu____1018),uu____1019) -> FStar_Order.Lt
      | (uu____1022,FStar_Reflection_Data.Tv_AscribedC
         (uu____1023,uu____1024,uu____1025)) -> FStar_Order.Gt
      | (FStar_Reflection_Data.Tv_Unknown ,uu____1028) -> FStar_Order.Lt
      | (uu____1029,FStar_Reflection_Data.Tv_Unknown ) -> FStar_Order.Gt

and (compare_argv :
  FStar_Reflection_Data.argv ->
    FStar_Reflection_Data.argv -> FStar_Order.order)
  =
  fun a1  ->
    fun a2  ->
      let uu____1032 = a1  in
      match uu____1032 with
      | (a11,q1) ->
          let uu____1035 = a2  in
          (match uu____1035 with
           | (a21,q2) ->
               (match (q1, q2) with
                | (FStar_Reflection_Data.Q_Implicit
                   ,FStar_Reflection_Data.Q_Explicit ) -> FStar_Order.Lt
                | (FStar_Reflection_Data.Q_Explicit
                   ,FStar_Reflection_Data.Q_Implicit ) -> FStar_Order.Gt
                | (uu____1038,uu____1039) -> compare_term a11 a21))

and (compare_comp :
  FStar_Reflection_Types.comp ->
    FStar_Reflection_Types.comp -> FStar_Order.order)
  =
  fun c1  ->
    fun c2  ->
      let cv1 = FStar_Reflection_Basic.inspect_comp c1  in
      let cv2 = FStar_Reflection_Basic.inspect_comp c2  in
      match (cv1, cv2) with
      | (FStar_Reflection_Data.C_Total (t1,md1),FStar_Reflection_Data.C_Total
         (t2,md2)) ->
          FStar_Order.lex (compare_term t1 t2)
            (fun uu____1053  ->
               match (md1, md2) with
               | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.None
                  ) -> FStar_Order.Eq
               | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.Some
                  uu____1062) -> FStar_Order.Lt
               | (FStar_Pervasives_Native.Some
                  uu____1067,FStar_Pervasives_Native.None ) -> FStar_Order.Gt
               | (FStar_Pervasives_Native.Some x,FStar_Pervasives_Native.Some
                  y) -> compare_term x y)
      | (FStar_Reflection_Data.C_Lemma (p1,q1),FStar_Reflection_Data.C_Lemma
         (p2,q2)) ->
          FStar_Order.lex (compare_term p1 p2)
            (fun uu____1083  -> compare_term q1 q2)
      | (FStar_Reflection_Data.C_Unknown ,FStar_Reflection_Data.C_Unknown )
          -> FStar_Order.Eq
      | (FStar_Reflection_Data.C_Total (uu____1084,uu____1085),uu____1086) ->
          FStar_Order.Lt
      | (uu____1089,FStar_Reflection_Data.C_Total (uu____1090,uu____1091)) ->
          FStar_Order.Gt
      | (FStar_Reflection_Data.C_Lemma (uu____1094,uu____1095),uu____1096) ->
          FStar_Order.Lt
      | (uu____1097,FStar_Reflection_Data.C_Lemma (uu____1098,uu____1099)) ->
          FStar_Order.Gt
      | (FStar_Reflection_Data.C_Unknown ,uu____1100) -> FStar_Order.Lt
      | (uu____1101,FStar_Reflection_Data.C_Unknown ) -> FStar_Order.Gt

let (mk_stringlit : Prims.string -> FStar_Reflection_Types.term) =
  fun s  ->
    FStar_Reflection_Basic.pack_ln
      (FStar_Reflection_Data.Tv_Const (FStar_Reflection_Data.C_String s))
  
let (mk_strcat :
  FStar_Reflection_Types.term ->
    FStar_Reflection_Types.term -> FStar_Reflection_Types.term)
  =
  fun t1  ->
    fun t2  ->
      mk_e_app
        (FStar_Reflection_Basic.pack_ln
           (FStar_Reflection_Data.Tv_FVar
              (FStar_Reflection_Basic.pack_fv ["Prims"; "strcat"]))) 
        [t1; t2]
  
let (mk_cons :
  FStar_Reflection_Types.term ->
    FStar_Reflection_Types.term -> FStar_Reflection_Types.term)
  =
  fun h  ->
    fun t  ->
      mk_e_app
        (FStar_Reflection_Basic.pack_ln
           (FStar_Reflection_Data.Tv_FVar
              (FStar_Reflection_Basic.pack_fv FStar_Reflection_Const.cons_qn)))
        [h; t]
  
let (mk_cons_t :
  FStar_Reflection_Types.term ->
    FStar_Reflection_Types.term ->
      FStar_Reflection_Types.term -> FStar_Reflection_Types.term)
  =
  fun ty  ->
    fun h  ->
      fun t  ->
        mk_app
          (FStar_Reflection_Basic.pack_ln
             (FStar_Reflection_Data.Tv_FVar
                (FStar_Reflection_Basic.pack_fv
                   FStar_Reflection_Const.cons_qn)))
          [(ty, FStar_Reflection_Data.Q_Implicit);
          (h, FStar_Reflection_Data.Q_Explicit);
          (t, FStar_Reflection_Data.Q_Explicit)]
  
let rec (mk_list :
  FStar_Reflection_Types.term Prims.list -> FStar_Reflection_Types.term) =
  fun ts  ->
    match ts with
    | [] ->
        FStar_Reflection_Basic.pack_ln
          (FStar_Reflection_Data.Tv_FVar
             (FStar_Reflection_Basic.pack_fv FStar_Reflection_Const.nil_qn))
    | t::ts1 -> mk_cons t (mk_list ts1)
  
let (mktuple_n :
  FStar_Reflection_Types.term Prims.list -> FStar_Reflection_Types.term) =
  fun ts  ->
    match FStar_List_Tot_Base.length ts with
    | _1193 when _1193 = Prims.int_zero ->
        FStar_Reflection_Basic.pack_ln
          (FStar_Reflection_Data.Tv_Const FStar_Reflection_Data.C_Unit)
    | _1194 when _1194 = Prims.int_one ->
        let uu____1195 = ts  in (match uu____1195 with | x::[] -> x)
    | n1 ->
        let qn =
          match n1 with
          | _1202 when _1202 = (Prims.of_int (2)) ->
              FStar_Reflection_Const.mktuple2_qn
          | _1203 when _1203 = (Prims.of_int (3)) ->
              FStar_Reflection_Const.mktuple3_qn
          | _1204 when _1204 = (Prims.of_int (4)) ->
              FStar_Reflection_Const.mktuple4_qn
          | _1205 when _1205 = (Prims.of_int (5)) ->
              FStar_Reflection_Const.mktuple5_qn
          | _1206 when _1206 = (Prims.of_int (6)) ->
              FStar_Reflection_Const.mktuple6_qn
          | _1207 when _1207 = (Prims.of_int (7)) ->
              FStar_Reflection_Const.mktuple7_qn
          | _1208 when _1208 = (Prims.of_int (8)) ->
              FStar_Reflection_Const.mktuple8_qn
           in
        mk_e_app
          (FStar_Reflection_Basic.pack_ln
             (FStar_Reflection_Data.Tv_FVar
                (FStar_Reflection_Basic.pack_fv qn))) ts
  
let (destruct_tuple :
  FStar_Reflection_Types.term ->
    FStar_Reflection_Types.term Prims.list FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____1230 = collect_app t  in
    match uu____1230 with
    | (head1,args) ->
        (match FStar_Reflection_Basic.inspect_ln head1 with
         | FStar_Reflection_Data.Tv_FVar fv ->
             if
               FStar_List_Tot_Base.mem (FStar_Reflection_Basic.inspect_fv fv)
                 [FStar_Reflection_Const.mktuple2_qn;
                 FStar_Reflection_Const.mktuple3_qn;
                 FStar_Reflection_Const.mktuple4_qn;
                 FStar_Reflection_Const.mktuple5_qn;
                 FStar_Reflection_Const.mktuple6_qn;
                 FStar_Reflection_Const.mktuple7_qn;
                 FStar_Reflection_Const.mktuple8_qn]
             then
               FStar_Pervasives_Native.Some
                 (FStar_List_Tot_Base.concatMap
                    (fun uu____1281  ->
                       match uu____1281 with
                       | (t1,q) ->
                           (match q with
                            | FStar_Reflection_Data.Q_Explicit  -> [t1]
                            | uu____1288 -> [])) args)
             else FStar_Pervasives_Native.None
         | uu____1293 -> FStar_Pervasives_Native.None)
  
let (mkpair :
  FStar_Reflection_Types.term ->
    FStar_Reflection_Types.term -> FStar_Reflection_Types.term)
  = fun t1  -> fun t2  -> mktuple_n [t1; t2] 
let rec (head : FStar_Reflection_Types.term -> FStar_Reflection_Types.term) =
  fun t  ->
    match FStar_Reflection_Basic.inspect_ln t with
    | FStar_Reflection_Data.Tv_Match (t1,uu____1345) -> head t1
    | FStar_Reflection_Data.Tv_Let
        (uu____1348,uu____1349,uu____1350,t1,uu____1352) -> head t1
    | FStar_Reflection_Data.Tv_Abs (uu____1356,t1) -> head t1
    | FStar_Reflection_Data.Tv_Refine (uu____1358,t1) -> head t1
    | FStar_Reflection_Data.Tv_App (t1,uu____1361) -> head t1
    | FStar_Reflection_Data.Tv_AscribedT (t1,uu____1363,uu____1364) ->
        head t1
    | FStar_Reflection_Data.Tv_AscribedC (t1,uu____1368,uu____1369) ->
        head t1
    | FStar_Reflection_Data.Tv_Unknown  -> t
    | FStar_Reflection_Data.Tv_Uvar (uu____1372,uu____1373) -> t
    | FStar_Reflection_Data.Tv_Const uu____1375 -> t
    | FStar_Reflection_Data.Tv_Type uu____1376 -> t
    | FStar_Reflection_Data.Tv_Var uu____1377 -> t
    | FStar_Reflection_Data.Tv_BVar uu____1378 -> t
    | FStar_Reflection_Data.Tv_FVar uu____1379 -> t
    | FStar_Reflection_Data.Tv_Arrow (uu____1380,uu____1381) -> t
  
let (nameof : FStar_Reflection_Types.term -> Prims.string) =
  fun t  ->
    match FStar_Reflection_Basic.inspect_ln t with
    | FStar_Reflection_Data.Tv_FVar fv ->
        FStar_String.concat "." (FStar_Reflection_Basic.inspect_fv fv)
    | uu____1394 -> "?"
  
let (is_uvar : FStar_Reflection_Types.term -> Prims.bool) =
  fun t  ->
    match FStar_Reflection_Basic.inspect_ln (head t) with
    | FStar_Reflection_Data.Tv_Uvar (uu____1407,uu____1408) -> true
    | uu____1411 -> false
  