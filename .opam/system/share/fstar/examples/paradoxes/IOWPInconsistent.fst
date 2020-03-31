(*
   Copyright 2008-2018 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
module IOWPInconsistent

(* Showing that the WP that would result from using DM4F on the IO monad transformer leads to inconsistency.             *)
(*                                                                                                                       *)
(* To simplify the proof, here we show that considering just unit-output already leads to inconsistency,                 *)
(* where by unit-output we mean the algebraically given effect with one unary operation symbol `out : 1`.                *)
(*                                                                                                                       *)
(* Based on:                                                                                                             *)
(*   - the unit-output monad transformer, if it exists, given by                                                         *)
(*       Out_T T X = mu Z . T (Z + X)                                                                                    *)
(*                                                                                                                       *)
(*     which is also the counterexample used to the existence of the sum of continuations with arbitrary other monads in *)
(*       M. Hyland et al. Combining algebraic effects with continuations. Theor. Comput. Sci. 375(1-3): 20-40 (2007)     *)
(*                                                                                                                       *)
(*   - the DM4F construction amounting to applying Out_T to the prop-valued continuation monad, resulting in             *)
(*       Out_WP X = mu Z . ((Z + X) -> prop) -> prop                                                                     *)
(*                                                                                                                       *)
(*   - the counterexample to allowing inductive types to be not strictly positive given in                               *)
(*       FStar/examples/paradoxes/propImpredicativeAndNonStrictlyPositiveinductives.fst                                  *)
(*                                                                                                                       *)
(*     which itself is based on the following note about (non) strict positivity and impredicativity                     *)
(*       http://vilhelms.github.io/posts/why-must-inductive-types-be-strictly-positive/                                  *)


#set-options "--__no_positivity"                   (* enabling non strict positivity so as to ensure Out_WP exists in F* *)

let prop = p:Type0{forall (x y:p). x == y}

noeq type out_wp (a:Type) =                      (* the non strictly positive WP type for output one would get from DM4F *)
  | Intro : ((either (out_wp a) a -> prop) -> prop) -> out_wp a

                                                          (* The rest is simply a recreation of the paradoxes considered *)
                                                          (* in the notes above, adapted to the case of unit-output.     *)
let intro_injective (#a:Type) (p p': (either (out_wp a) a -> prop) -> prop) 
  : Lemma (Intro p == Intro p' ==> p == p) = 
  ()

let inj (#x:Type) : x -> (x -> prop) = fun x0 y0 -> x0 == y0

let inj_injective (#x:Type) (x0 x0':x) 
  : Lemma (requires (inj x0 == inj x0')) 
          (ensures  (x0 == x0')) =
  assert (inj x0 x0) ;
  assert (inj x0' x0)

let f (#a:Type) (p:either (out_wp a) a -> prop) : either (out_wp a) a = 
  Inl (Intro (inj p))

let f_injective (#a:Type) (p p' : either (out_wp a) a -> prop) 
  : Lemma (requires (f p == f p')) 
          (ensures  (p == p')) =
  inj_injective p p' ;
  intro_injective (inj p) (inj p')

let p0 : #a:Type -> either (out_wp a) a -> prop = fun #a x ->
  exists (p:either (out_wp a) a -> prop).
    f #a p == x /\ ~(p x)
let x0 (#a:Type) = f #a p0

open FStar.Classical

let bad1 (a:Type) 
  : Lemma (requires (p0 (x0 #a))) 
          (ensures  (~(p0 (x0 #a)))) =
  let aux (p:(either (out_wp a) a -> prop){f p == (x0 #a) /\ ~(p (x0 #a))}) 
    : GTot (squash (~(p0 (x0 #a)))) =
    f_injective p p0
  in 
  exists_elim (~(p0 (x0 #a))) (FStar.Squash.get_proof (p0 (x0 #a))) aux

let bad2 (a:Type) 
  : Lemma (requires (~(p0 (x0 #a)))) 
          (ensures  (p0 (x0 #a))) =
  exists_intro (fun (p:either (out_wp a) a -> prop) ->
    f p == x0 #a /\ ~(p (x0 #a))) p0

let out_wp_inconsistent (a:Type) 
  : Lemma False = 
  move_requires (fun _ -> bad1 a) ();                                                  (* giving us (p0 x0 ==> ~(p0 x0)) *)
  move_requires (fun _ -> bad2 a) ();                                                  (* giving us (~(p0 x0) ==> p0 x0) *)
  assert (~(p0 (x0 #a)) /\ p0 (x0 #a));
  assert (False)
