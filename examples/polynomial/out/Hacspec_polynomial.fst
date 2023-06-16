module Hacspec_polynomial
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Hacspec.Lib
open Hacspec_lib_tc

unfold
type fpPallas_t = nat_mod 0x40000000000000000000000000000000224698FC094CF91B992D30ED00000001
unfold
type pallasCanvas_t = lseq pub_uint8 255

type polynomial_t = { coefficients:Hacspec_lib_tc.seq_t t }

(* item error backend *)

let impl
      (#t: Type)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] __0: Core.Marker.sized_t t)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] __1: Hacspec_lib_tc.numeric_t t)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] __2: Hacspec_lib_tc.numericCopy_t t)
    : Core.Ops.Arith.Add (polynomial_t t) (polynomial_t t) =
  {
    output = polynomial_t t;
    add
    =
    fun
      (#t: Type)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] __0: Core.Marker.sized_t t)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] __1: Hacspec_lib_tc.numeric_t t)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] __2: Hacspec_lib_tc.numericCopy_t t)
      (self: polynomial_t t)
      (other: polynomial_t t)
      ->
      Hacspec.Lib.run (let lhs:Hacspec_lib_tc.seq_t t = self.coefficients in
          let rhs:Hacspec_lib_tc.seq_t t = other.coefficients in
          let big, small:(Hacspec_lib_tc.seq_t t & Hacspec_lib_tc.seq_t t) =
            if Prims.op_GreaterThanOrEqual (Hacspec_lib_tc.len lhs) (Hacspec_lib_tc.len rhs)
            then lhs, rhs
            else rhs, lhs
          in
          let result:Hacspec_lib_tc.seq_t t = Core.Clone.Clone.clone big in
          let result:Hacspec_lib_tc.seq_t t =
            Core.Iter.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter ({
                      start = 0;
                      end = Hacspec_lib_tc.len small
                    }))
              result
              (fun i result -> result.[ i ] <- result.[ i ] +. small.[ i ])
          in
          Std.Ops.ControlFlow.break ({ coefficients = result }))
  }

let impl
      (#t: Type)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] __0: Core.Marker.sized_t t)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] __1: Hacspec_lib_tc.numeric_t t)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] __2: Hacspec_lib_tc.numericCopy_t t)
    : Core.Ops.Arith.Sub (polynomial_t t) (polynomial_t t) =
  {
    output = polynomial_t t;
    sub
    =
    fun
      (#t: Type)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] __0: Core.Marker.sized_t t)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] __1: Hacspec_lib_tc.numeric_t t)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] __2: Hacspec_lib_tc.numericCopy_t t)
      (self: polynomial_t t)
      (other: polynomial_t t)
      ->
      Hacspec.Lib.run (let rhs:Hacspec_lib_tc.seq_t t = other.coefficients in
          let neg_rhs:Hacspec_lib_tc.seq_t t = Hacspec_lib_tc.create (Hacspec_lib_tc.len rhs) in
          let neg_rhs:Hacspec_lib_tc.seq_t t =
            Core.Iter.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter ({
                      start = 0;
                      end = Hacspec_lib_tc.len rhs
                    }))
              neg_rhs
              (fun i neg_rhs -> neg_rhs.[ i ] <- Core.Default.Default.default -. rhs.[ i ])
          in
          Std.Ops.ControlFlow.break (Core.Clone.Clone.clone self +. { coefficients = neg_rhs }))
  }

let impl
      (#t: Type)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] __0: Core.Marker.sized_t t)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] __1: Hacspec_lib_tc.numeric_t t)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] __2: Hacspec_lib_tc.numericCopy_t t)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] __3: Core.Cmp.partialEq_t t t)
    : Core.Cmp.PartialEq (polynomial_t t) (polynomial_t t) =
  {
    eq
    =
    fun
      (#t: Type)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] __0: Core.Marker.sized_t t)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] __1: Hacspec_lib_tc.numeric_t t)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] __2: Hacspec_lib_tc.numericCopy_t t)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] __3: Core.Cmp.partialEq_t t t)
      (self: polynomial_t t)
      (other: polynomial_t t)
      ->
      let equal:Prims.bool = true in
      let lhs:Hacspec_lib_tc.seq_t t = self.coefficients in
      let rhs:Hacspec_lib_tc.seq_t t = other.coefficients in
      let equal:Prims.bool =
        if Hacspec_lib_tc.len lhs <> Hacspec_lib_tc.len rhs
        then
          let equal:Prims.bool = false in
          equal
        else
          Core.Iter.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter ({
                    start = 0;
                    end = Hacspec_lib_tc.len lhs
                  }))
            equal
            (fun i equal ->
                if Core.Cmp.PartialEq.ne lhs.[ i ] rhs.[ i ]
                then
                  let equal:Prims.bool = false in
                  equal
                else equal)
      in
      equal
  }

let impl
      (#t: Type)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] __0: Core.Marker.sized_t t)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] __1: Hacspec_lib_tc.numeric_t t)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] __2: Hacspec_lib_tc.numericCopy_t t)
    : Core.Clone.Clone (polynomial_t t) =
  {
    clone
    =
    fun
      (#t: Type)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] __0: Core.Marker.sized_t t)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] __1: Hacspec_lib_tc.numeric_t t)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] __2: Hacspec_lib_tc.numericCopy_t t)
      (self: polynomial_t t)
      ->
      { coefficients = Core.Clone.Clone.clone self.coefficients }
  }

let gen_zero_polyx: polynomial_t fpPallas_t =
  let coef:Hacspec_lib_tc.seq_t fpPallas_t = Hacspec_lib_tc.create 1 in
  { coefficients = coef }

let gen_one_polyx: polynomial_t fpPallas_t =
  let coef:Hacspec_lib_tc.seq_t fpPallas_t = Hacspec_lib_tc.create 1 in
  let coef:Hacspec_lib_tc.seq_t fpPallas_t =
    coef.[ Num_traits.Identities.Zero.zero ] <- Hacspec_lib_tc.oNE
  in
  { coefficients = coef }