open Prims
type 'Aa __tac =
  FStar_Tactics_Types.proofstate -> 'Aa FStar_Tactics_Result.__result
let __ret : 'Aa . 'Aa -> 'Aa __tac =
  fun x  -> fun s  -> FStar_Tactics_Result.Success (x, s) 
let __bind :
  'Aa 'Ab .
    Prims.range ->
      Prims.range -> 'Aa __tac -> ('Aa -> 'Ab __tac) -> 'Ab __tac
  =
  fun r1  ->
    fun r2  ->
      fun t1  ->
        fun t2  ->
          fun ps  ->
            let ps1 =
              FStar_Tactics_Types.set_proofstate_range ps
                (FStar_Range.prims_to_fstar_range r1)
               in
            let ps2 = FStar_Tactics_Types.incr_depth ps1  in
            let r = t1 ps2  in
            match r with
            | FStar_Tactics_Result.Success (a,ps') ->
                let ps'1 =
                  FStar_Tactics_Types.set_proofstate_range ps'
                    (FStar_Range.prims_to_fstar_range r2)
                   in
                (match () with
                 | () -> t2 a (FStar_Tactics_Types.decr_depth ps'1))
            | FStar_Tactics_Result.Failed (e,ps') ->
                FStar_Tactics_Result.Failed (e, ps')
  
let (__get : unit -> FStar_Tactics_Types.proofstate __tac) =
  fun uu____163  -> fun s0  -> FStar_Tactics_Result.Success (s0, s0) 
let __raise : 'Aa . Prims.exn -> 'Aa __tac =
  fun e  -> fun ps  -> FStar_Tactics_Result.Failed (e, ps) 
type 'Aa __tac_wp = unit
type ('Aa,'Ab,'Awp,'Af,'Aps,'Apost) g_bind = 'Awp
type ('Aa,'Awp,'Aps,'Apost) g_compact = unit
type ('Ar,'Aa,'Ab,'Awp,'Af,'Auu____287,'Auu____288) __TAC_eff_override_bind_wp =
  unit
type ('Aa,'Awp,'As,'Ap') _dm4f_TAC_lift_from_pure = 'Awp
type ('Aa,'Ax,'As,'Ap') _dm4f_TAC_return_wp = 'Ap'
let _dm4f_TAC_return_elab :
  'Aa .
    'Aa ->
      FStar_Tactics_Types.proofstate -> 'Aa FStar_Tactics_Result.__result
  = fun x  -> fun s  -> FStar_Tactics_Result.Success (x, s) 
let _dm4f_TAC_bind_elab :
  'Aa 'Ab .
    Prims.range ->
      Prims.range ->
        unit ->
          (FStar_Tactics_Types.proofstate ->
             'Aa FStar_Tactics_Result.__result)
            ->
            unit ->
              ('Aa ->
                 FStar_Tactics_Types.proofstate ->
                   'Ab FStar_Tactics_Result.__result)
                ->
                FStar_Tactics_Types.proofstate ->
                  'Ab FStar_Tactics_Result.__result
  =
  fun r1  ->
    fun r2  ->
      fun t1__w  ->
        fun t1  ->
          fun t2__w  ->
            fun t2  ->
              fun ps  ->
                let ps1 =
                  FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range r1)
                   in
                let ps2 = FStar_Tactics_Types.incr_depth ps1  in
                let r = t1 ps2  in
                match r with
                | FStar_Tactics_Result.Success (a,ps') ->
                    let ps'1 =
                      FStar_Tactics_Types.set_proofstate_range ps'
                        (FStar_Range.prims_to_fstar_range r2)
                       in
                    (match () with
                     | () -> t2 a (FStar_Tactics_Types.decr_depth ps'1))
                | FStar_Tactics_Result.Failed (e,ps') ->
                    FStar_Tactics_Result.Failed (e, ps')
  
let _dm4f_TAC___proj__TAC__item____raise_elab :
  'Aa .
    Prims.exn ->
      FStar_Tactics_Types.proofstate -> 'Aa FStar_Tactics_Result.__result
  = fun e  -> fun ps  -> FStar_Tactics_Result.Failed (e, ps) 
type _dm4f_TAC___proj__TAC__item____raise_complete_type =
  unit ->
    Prims.exn ->
      FStar_Tactics_Types.proofstate -> Obj.t FStar_Tactics_Result.__result
let (_dm4f_TAC___proj__TAC__item____get_elab :
  unit ->
    FStar_Tactics_Types.proofstate ->
      FStar_Tactics_Types.proofstate FStar_Tactics_Result.__result)
  = fun uu____548  -> fun s0  -> FStar_Tactics_Result.Success (s0, s0) 
type _dm4f_TAC___proj__TAC__item____get_complete_type =
  unit ->
    FStar_Tactics_Types.proofstate ->
      FStar_Tactics_Types.proofstate FStar_Tactics_Result.__result
type ('Aa,'Awp_a) _dm4f_TAC_repr =
  FStar_Tactics_Types.proofstate -> 'Aa FStar_Tactics_Result.__result
type _dm4f_TAC_pre = unit
type 'Aa _dm4f_TAC_post = unit
type 'Aa _dm4f_TAC_wp = unit
type ('Aa,'At) _dm4f_TAC_ctx = FStar_Tactics_Types.proofstate -> unit -> 'At
type ('Aa,'At) _dm4f_TAC_gctx = unit
let _dm4f_TAC_pure :
  'Aa 'At . 'At -> FStar_Tactics_Types.proofstate -> unit -> 'At =
  fun x  -> fun uu____651  -> fun uu____652  -> x 




type ('Aa,'Ac,'Auu____768,'Auu____769,'Auu____770,'Auu____771) _dm4f_TAC_wp_if_then_else =
  unit
type ('Aa,'Ab,'Af,'Auu____793,'Auu____794) _dm4f_TAC_wp_close = unit
type ('Aa,'Awp1,'Awp2) _dm4f_TAC_stronger = unit
type ('Aa,'Awp,'Auu____836,'Auu____837) _dm4f_TAC_ite_wp = unit
type ('Aa,'Auu____853,'Auu____854) _dm4f_TAC_null_wp = unit
type ('Aa,'Awp) _dm4f_TAC_wp_trivial = unit
let __proj__TAC__item__return = _dm4f_TAC_return_elab 
let __proj__TAC__item__bind = _dm4f_TAC_bind_elab 
let __proj__TAC__item____raise e ps = FStar_Tactics_Result.Failed (e, ps) 
let __proj__TAC__item____get uu____915 s0 =
  FStar_Tactics_Result.Success (s0, s0) 
type ('Aa,'Awp,'Aps,'Ap) lift_div_tac = 'Awp
let (get : unit -> (FStar_Tactics_Types.proofstate,unit) _dm4f_TAC_repr) =
  __proj__TAC__item____get 
let raise : 'Aa . Prims.exn -> ('Aa,unit) _dm4f_TAC_repr =
  fun e  -> __proj__TAC__item____raise e 
type ('At,'Ap) with_tactic = 'Ap
let synth_by_tactic : 'At . (unit -> (unit,unit) _dm4f_TAC_repr) -> 'At =
  fun uu____1032  -> failwith "Not yet implemented:synth_by_tactic" 


let assume_safe :
  'Aa . (unit -> ('Aa,unit) _dm4f_TAC_repr) -> ('Aa,unit) _dm4f_TAC_repr =
  fun tau  -> tau () 
type ('Aa,'Ab) tac = 'Aa -> ('Ab,unit) _dm4f_TAC_repr
type 'Aa tactic = (unit,'Aa) tac


