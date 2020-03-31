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
module MiniParse.Impl.Int
include MiniParse.Spec.Int
include MiniParse.Impl.Combinators

module U16 = FStar.UInt16
module B = LowStar.Buffer
module U32 = FStar.UInt32
module HST = FStar.HyperStack.ST
module Aux = MiniParse.Spec.Int.Aux

inline_for_extraction
let parse_u8_impl : parser_impl parse_u8 = make_total_constant_size_parser_impl 1 1ul (fun x -> Seq.index x 0) () (fun x -> B.index x 0ul)

inline_for_extraction
let serialize_u8_impl : serializer_impl serialize_u8 =
  (fun output (len: U32.t { len == B.len output } ) x ->
    let h = HST.get () in
    if len `U32.lt` 1ul
    then None
    else begin
      let output' = B.sub output 0ul 1ul in
      B.upd output' 0ul x;
      let h' = HST.get () in
      assert (B.as_seq h' output' `Seq.equal` Seq.create 1 x);
      Some 1ul
    end)

inline_for_extraction
let parse_u16_impl : parser_impl parse_u16 = make_total_constant_size_parser_impl 2 2ul parse_u16_aux () (fun x ->
  let lo = B.index x 0ul in
  let hi = B.index x 1ul in
  Aux.decode_u16 (lo, hi)
)

inline_for_extraction
let serialize_u16_impl : serializer_impl serialize_u16 =
  fun output (len: U32.t { len == B.len output } ) x ->
    if len `U32.lt` 2ul
    then None
    else begin
      let (lo, hi) = Aux.encode_u16 x in
      let output' = B.sub output 0ul 2ul in
      B.upd output' 0ul lo;
      B.upd output' 1ul hi;
      let h' = HST.get () in
      assert (B.as_seq h' output' `Seq.equal` Seq.append (Seq.create 1 lo) (Seq.create 1 hi));
      Some 2ul
    end

#set-options "--z3rlimit 64"

inline_for_extraction
let parse_bounded_u16_impl
  (b: nat)
: Tot (parser_impl (parse_bounded_u16 b)) =
  if b >= 65536
  then (fun input len -> parse_synth_impl parse_u16_impl (fun x -> x <: bounded_u16 b) (fun x -> x <: bounded_u16 b) (fun x -> x) () input len)
  else
    [@inline_let]
    let b' = U16.uint_to_t b in
    parse_synth_impl
      (parse_filter_impl parse_u16_impl (fun x -> U16.v x < b) (fun x -> x `U16.lt` b'))
      (fun x -> x <: bounded_u16 b)
      (fun x -> x <: bounded_u16 b)
      (fun x -> x)
      ()

#reset-options

inline_for_extraction
let serialize_bounded_u16_impl (b: nat) : Tot (serializer_impl (serialize_bounded_u16 b)) =
  fun output len x -> serialize_u16_impl output len x
