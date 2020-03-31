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
module Test
open FStar.Pointer

let nested_st: struct_typ = {
  name = "nested_st";
  fields = [
    ("X", TBase TUInt32);
    ("Y", TArray 5ul (TBase TUInt32))
  ]
}

let ty: typ =
  TStruct ({
    name = "ty";
    fields = [
      ("A", TStruct nested_st);
      ("B", TArray 3ul (TBase TUInt64))
    ]
  })

val f : unit -> FStar.HyperStack.ST.Stack unit (requires (fun _ -> True)) (ensures (fun _ _ _ -> True))

let f () =
  FStar.HyperStack.ST.push_frame ();
  let s : Pointer.pointer ty = screate ty None in
  let h = FStar.HyperStack.ST.get () in
  let p : pointer (TArray 5ul (TBase TUInt32)) = Pointer.field #nested_st (Pointer.field s "A") "Y" in
  let _ = Pointer.write (Pointer.cell p 1ul) 19ul in
  let b = Pointer.buffer_of_array_pointer p in
  let c = Pointer.sub_buffer b 1ul 3ul in
  let _ = Pointer.write_buffer c 2ul 21ul in
  let u = Pointer.read (Pointer.cell p 1ul) in
  let v = Pointer.read (Pointer.cell p 3ul) in
  assert (u == 19ul /\ v == 21ul);
  FStar.HyperStack.ST.pop_frame ();
  ()
