open Prims
let read_rel1 :
  'Auu____9 .
    'Auu____9 FStar_ST.ref -> 'Auu____9 FStar_Relational_Relational.double
  =
  fun r  ->
    FStar_Relational_Comp.compose2_self FStar_Ref.read
      (FStar_Relational_Relational.twice r)
  
let read_rel2 :
  'Auu____46 .
    unit ->
      'Auu____46 FStar_ST.ref FStar_Relational_Relational.double ->
        'Auu____46 FStar_Relational_Relational.double
  = fun uu____60  -> FStar_Relational_Comp.compose2_self FStar_Ref.read 
let assign_rel1 :
  'Auu____91 .
    'Auu____91 FStar_ST.ref ->
      ('Auu____91,'Auu____91) FStar_Relational_Relational.rel ->
        unit FStar_Relational_Relational.double
  =
  fun r  ->
    fun v  ->
      FStar_Relational_Comp.compose2_self
        (fun uu____153  ->
           match uu____153 with | (a,b) -> FStar_Ref.write a b)
        (FStar_Relational_Relational.pair_rel
           (FStar_Relational_Relational.twice r) v)
  
let assign_rel2 :
  'Auu____192 .
    ('Auu____192 FStar_ST.ref,'Auu____192 FStar_ST.ref)
      FStar_Relational_Relational.rel ->
      ('Auu____192,'Auu____192) FStar_Relational_Relational.rel ->
        unit FStar_Relational_Relational.double
  =
  fun r  ->
    fun v  ->
      FStar_Relational_Comp.compose2_self
        (fun uu____266  ->
           match uu____266 with | (a,b) -> FStar_Ref.write a b)
        (FStar_Relational_Relational.pair_rel r v)
  