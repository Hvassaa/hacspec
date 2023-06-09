module Hacspec_pasta
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Hacspec.Lib
open Hacspec_lib_tc

unfold
type fpPallas_t = nat_mod 0x40000000000000000000000000000000224698FC094CF91B992D30ED00000001
unfold
type pallasCanvas_t = lseq pub_uint8 255

unfold
type fpVesta_t = nat_mod 0x40000000000000000000000000000000224698FC0994A8DD8C46EB2100000001
unfold
type vestaCanvas_t = lseq pub_uint8 255

let g1_pallas = (fpPallas_t & fpPallas_t & Prims.bool)

let g1_vesta = (fpVesta_t & fpVesta_t & Prims.bool)

let g1_default_pallas: (fpPallas_t & fpPallas_t & Prims.bool) =
  Hacspec_lib_tc.zero, Hacspec_lib_tc.zero, true

let g1_default_vesta: (fpVesta_t & fpVesta_t & Prims.bool) =
  Hacspec_lib_tc.zero, Hacspec_lib_tc.zero, true

let g1add_a_pallas (p q: (fpPallas_t & fpPallas_t & Prims.bool))
    : (fpPallas_t & fpPallas_t & Prims.bool) =
  let x1, y1, _:(fpPallas_t & fpPallas_t & Prims.bool) = p in
  let x2, y2, _:(fpPallas_t & fpPallas_t & Prims.bool) = q in
  let x_diff = x2 -. x1 in
  let y_diff = y2 -. y1 in
  let xovery = y_diff *. inv x_diff in
  let x3 = Hacspec_lib_tc.exp xovery 2ul -. x1 -. x2 in
  let y3 = xovery *. (x1 -. x3) -. y1 in
  x3, y3, false

let g1add_a_vesta (p q: (fpVesta_t & fpVesta_t & Prims.bool)) : (fpVesta_t & fpVesta_t & Prims.bool) =
  let x1, y1, _:(fpVesta_t & fpVesta_t & Prims.bool) = p in
  let x2, y2, _:(fpVesta_t & fpVesta_t & Prims.bool) = q in
  let x_diff = x2 -. x1 in
  let y_diff = y2 -. y1 in
  let xovery = y_diff *. inv x_diff in
  let x3 = Hacspec_lib_tc.exp xovery 2ul -. x1 -. x2 in
  let y3 = xovery *. (x1 -. x3) -. y1 in
  x3, y3, false

let g1double_a_pallas (p: (fpPallas_t & fpPallas_t & Prims.bool))
    : (fpPallas_t & fpPallas_t & Prims.bool) =
  let x1, y1, _:(fpPallas_t & fpPallas_t & Prims.bool) = p in
  let x12:fpPallas_t = Hacspec_lib_tc.exp x1 2ul in
  let xovery = from_literal (pub_u128 3) *. x12 *. inv (Hacspec_lib_tc.tWO *. y1) in
  let x3 = Hacspec_lib_tc.exp xovery 2ul -. Hacspec_lib_tc.tWO *. x1 in
  let y3 = xovery *. (x1 -. x3) -. y1 in
  x3, y3, false

let g1double_a_vesta (p: (fpVesta_t & fpVesta_t & Prims.bool))
    : (fpVesta_t & fpVesta_t & Prims.bool) =
  let x1, y1, _:(fpVesta_t & fpVesta_t & Prims.bool) = p in
  let x12:fpVesta_t = Hacspec_lib_tc.exp x1 2ul in
  let xovery = from_literal (pub_u128 3) *. x12 *. inv (Hacspec_lib_tc.tWO *. y1) in
  let x3 = Hacspec_lib_tc.exp xovery 2ul -. Hacspec_lib_tc.tWO *. x1 in
  let y3 = xovery *. (x1 -. x3) -. y1 in
  x3, y3, false

let g1double_pallas (p: (fpPallas_t & fpPallas_t & Prims.bool))
    : (fpPallas_t & fpPallas_t & Prims.bool) =
  let _x1, y1, inf1:(fpPallas_t & fpPallas_t & Prims.bool) = p in
  if Prims.op_AmpAmp (Core.Cmp.PartialEq.ne y1 Hacspec_lib_tc.zero) (Prims.l_Not inf1)
  then g1double_a_pallas p
  else Hacspec_lib_tc.zero, Hacspec_lib_tc.zero, true

let g1double_vesta (p: (fpVesta_t & fpVesta_t & Prims.bool)) : (fpVesta_t & fpVesta_t & Prims.bool) =
  let _x1, y1, inf1:(fpVesta_t & fpVesta_t & Prims.bool) = p in
  if Prims.op_AmpAmp (Core.Cmp.PartialEq.ne y1 Hacspec_lib_tc.zero) (Prims.l_Not inf1)
  then g1double_a_vesta p
  else Hacspec_lib_tc.zero, Hacspec_lib_tc.zero, true

let g1add_pallas (p q: (fpPallas_t & fpPallas_t & Prims.bool))
    : (fpPallas_t & fpPallas_t & Prims.bool) =
  let x1, y1, inf1:(fpPallas_t & fpPallas_t & Prims.bool) = p in
  let x2, y2, inf2:(fpPallas_t & fpPallas_t & Prims.bool) = q in
  if inf1
  then q
  else
    if inf2
    then p
    else
      if Core.Cmp.PartialEq.eq p q
      then g1double_pallas p
      else
        if
          Prims.l_Not (Prims.op_AmpAmp (Core.Cmp.PartialEq.eq x1 x2)
                (Core.Cmp.PartialEq.eq y1 (Hacspec_lib_tc.zero -. y2)))
        then g1add_a_pallas p q
        else Hacspec_lib_tc.zero, Hacspec_lib_tc.zero, true

let g1add_vesta (p q: (fpVesta_t & fpVesta_t & Prims.bool)) : (fpVesta_t & fpVesta_t & Prims.bool) =
  let x1, y1, inf1:(fpVesta_t & fpVesta_t & Prims.bool) = p in
  let x2, y2, inf2:(fpVesta_t & fpVesta_t & Prims.bool) = q in
  if inf1
  then q
  else
    if inf2
    then p
    else
      if Core.Cmp.PartialEq.eq p q
      then g1double_vesta p
      else
        if
          Prims.l_Not (Prims.op_AmpAmp (Core.Cmp.PartialEq.eq x1 x2)
                (Core.Cmp.PartialEq.eq y1 (Hacspec_lib_tc.zero -. y2)))
        then g1add_a_vesta p q
        else Hacspec_lib_tc.zero, Hacspec_lib_tc.zero, true

let g1mul_pallas (m: fpVesta_t) (p: (fpPallas_t & fpPallas_t & Prims.bool))
    : (fpPallas_t & fpPallas_t & Prims.bool) =
  let t:(fpPallas_t & fpPallas_t & Prims.bool) = Hacspec_lib_tc.zero, Hacspec_lib_tc.zero, true in
  let t:(fpPallas_t & fpPallas_t & Prims.bool) =
    Hacspec.Lib.foldi 0
      255
      (fun i t ->
          let t:(fpPallas_t & fpPallas_t & Prims.bool) = g1double_pallas t in
          if bit m (254 - i)
          then
            let t:(fpPallas_t & fpPallas_t & Prims.bool) = g1add_pallas t p in
            t
          else t)
      t
  in
  t

let g1mul_vesta (m: fpPallas_t) (p: (fpVesta_t & fpVesta_t & Prims.bool))
    : (fpVesta_t & fpVesta_t & Prims.bool) =
  let t:(fpVesta_t & fpVesta_t & Prims.bool) = Hacspec_lib_tc.zero, Hacspec_lib_tc.zero, true in
  let t:(fpVesta_t & fpVesta_t & Prims.bool) =
    Hacspec.Lib.foldi 0
      255
      (fun i t ->
          let t:(fpVesta_t & fpVesta_t & Prims.bool) = g1double_vesta t in
          if bit m (254 - i)
          then
            let t:(fpVesta_t & fpVesta_t & Prims.bool) = g1add_vesta t p in
            t
          else t)
      t
  in
  t

let g1neg_pallas (p: (fpPallas_t & fpPallas_t & Prims.bool))
    : (fpPallas_t & fpPallas_t & Prims.bool) =
  let x, y, inf:(fpPallas_t & fpPallas_t & Prims.bool) = p in
  x, Hacspec_lib_tc.zero -. y, inf

let g1neg_vesta (p: (fpVesta_t & fpVesta_t & Prims.bool)) : (fpVesta_t & fpVesta_t & Prims.bool) =
  let x, y, inf:(fpVesta_t & fpVesta_t & Prims.bool) = p in
  x, Hacspec_lib_tc.zero -. y, inf

let g1_on_curve_pallas (p: (fpPallas_t & fpPallas_t & Prims.bool)) : Prims.bool =
  let x, y, inf:(fpPallas_t & fpPallas_t & Prims.bool) = p in
  let y_squared = y *. y in
  let x_cubed = x *. x *. x in
  let fp5 = Hacspec_lib_tc.tWO +. Hacspec_lib_tc.tWO +. Hacspec_lib_tc.oNE in
  Prims.op_BarBar (Core.Cmp.PartialEq.eq y_squared (x_cubed +. fp5)) inf

let g1_on_curve_vesta (p: (fpVesta_t & fpVesta_t & Prims.bool)) : Prims.bool =
  let x, y, inf:(fpVesta_t & fpVesta_t & Prims.bool) = p in
  let y_squared = y *. y in
  let x_cubed = x *. x *. x in
  let fp5 = Hacspec_lib_tc.tWO +. Hacspec_lib_tc.tWO +. Hacspec_lib_tc.oNE in
  Prims.op_BarBar (Core.Cmp.PartialEq.eq y_squared (x_cubed +. fp5)) inf

let g1_is_identity_pallas (p: (fpPallas_t & fpPallas_t & Prims.bool)) : Prims.bool =
  let _, _, inf:(fpPallas_t & fpPallas_t & Prims.bool) = p in
  inf

let g1_is_identity_vesta (p: (fpVesta_t & fpVesta_t & Prims.bool)) : Prims.bool =
  let _, _, inf:(fpVesta_t & fpVesta_t & Prims.bool) = p in
  inf

let polyx = Hacspec_lib_tc.seq_t fpVesta_t

let add_polyx (p1 p2: Hacspec_lib_tc.seq_t fpVesta_t) : Hacspec_lib_tc.seq_t fpVesta_t =
  let res:Hacspec_lib_tc.seq_t fpVesta_t = Hacspec_lib_tc.create 0 in
  let short_len:uint_size = 0 in
  let res, short_len:(Hacspec_lib_tc.seq_t fpVesta_t & uint_size) =
    if Prims.op_GreaterThanOrEqual (Hacspec_lib_tc.len p1) (Hacspec_lib_tc.len p2)
    then
      let res:Hacspec_lib_tc.seq_t fpVesta_t = Core.Clone.Clone.clone p1 in
      let short_len:uint_size = Hacspec_lib_tc.len p2 in
      res, short_len
    else
      let res:Hacspec_lib_tc.seq_t fpVesta_t = Core.Clone.Clone.clone p2 in
      let short_len:uint_size = Hacspec_lib_tc.len p1 in
      res, short_len
  in
  let res:Hacspec_lib_tc.seq_t fpVesta_t =
    Hacspec.Lib.foldi 0 short_len (fun i res -> res.[ i ] <- p1.[ i ] +. p2.[ i ]) res
  in
  trim_polyx res

let sub_polyx (p1 p2: Hacspec_lib_tc.seq_t fpVesta_t) : Hacspec_lib_tc.seq_t fpVesta_t =
  let largest:uint_size = Hacspec_lib_tc.len p1 in
  let largest:uint_size =
    if Prims.op_GreaterThanOrEqual (Hacspec_lib_tc.len p2) (Hacspec_lib_tc.len p1)
    then
      let largest:uint_size = Hacspec_lib_tc.len p2 in
      largest
    else largest
  in
  let res:Hacspec_lib_tc.seq_t fpVesta_t = Hacspec_lib_tc.create largest in
  let res:Hacspec_lib_tc.seq_t fpVesta_t =
    Hacspec.Lib.foldi 0 (Hacspec_lib_tc.len p1) (fun i res -> res.[ i ] <- p1.[ i ]) res
  in
  let res:Hacspec_lib_tc.seq_t fpVesta_t =
    Hacspec.Lib.foldi 0
      (Hacspec_lib_tc.len p2)
      (fun i res -> res.[ i ] <- res.[ i ] -. p2.[ i ])
      res
  in
  trim_polyx res

let mul_polyx (a b: Hacspec_lib_tc.seq_t fpVesta_t) : Hacspec_lib_tc.seq_t fpVesta_t =
  let result:Hacspec_lib_tc.seq_t fpVesta_t =
    Hacspec_lib_tc.create (Hacspec_lib_tc.len a + Hacspec_lib_tc.len b)
  in
  let result:Hacspec_lib_tc.seq_t fpVesta_t =
    Hacspec.Lib.foldi 0
      (Hacspec_lib_tc.len a)
      (fun i result ->
          if Prims.l_Not (Hacspec_lib_tc.equal a.[ i ] Core.Default.Default.default)
          then
            Hacspec.Lib.foldi 0
              (Hacspec_lib_tc.len b)
              (fun j result ->
                  if Prims.l_Not (Hacspec_lib_tc.equal b.[ j ] Core.Default.Default.default)
                  then
                    let result:Hacspec_lib_tc.seq_t fpVesta_t =
                      result.[ i + j ] <- result.[ i + j ] +. a.[ i ] *. b.[ j ]
                    in
                    result
                  else result)
              result
          else result)
      result
  in
  trim_polyx result

let mul_scalar_polyx (p: Hacspec_lib_tc.seq_t fpVesta_t) (s: fpVesta_t)
    : Hacspec_lib_tc.seq_t fpVesta_t =
  let res:Hacspec_lib_tc.seq_t fpVesta_t = Core.Clone.Clone.clone p in
  let res:Hacspec_lib_tc.seq_t fpVesta_t =
    Hacspec.Lib.foldi 0 (Hacspec_lib_tc.len res) (fun i res -> res.[ i ] <- p.[ i ] *. s) res
  in
  res

let add_scalar_polyx (p: Hacspec_lib_tc.seq_t fpVesta_t) (s: fpVesta_t)
    : Hacspec_lib_tc.seq_t fpVesta_t =
  let res:Hacspec_lib_tc.seq_t fpVesta_t = Core.Clone.Clone.clone p in
  let res:Hacspec_lib_tc.seq_t fpVesta_t =
    if Hacspec_lib_tc.len res = 0
    then
      let res:Hacspec_lib_tc.seq_t fpVesta_t = Hacspec_lib_tc.create 1 in
      res
    else res
  in
  let res:Hacspec_lib_tc.seq_t fpVesta_t = res.[ 0l ] <- res.[ 0l ] +. s in
  res

let sub_scalar_polyx (p: Hacspec_lib_tc.seq_t fpVesta_t) (s: fpVesta_t)
    : Hacspec_lib_tc.seq_t fpVesta_t =
  let res:Hacspec_lib_tc.seq_t fpVesta_t = Core.Clone.Clone.clone p in
  let res:Hacspec_lib_tc.seq_t fpVesta_t =
    if Hacspec_lib_tc.len res = 0
    then
      let res:Hacspec_lib_tc.seq_t fpVesta_t = Hacspec_lib_tc.create 1 in
      res
    else res
  in
  let res:Hacspec_lib_tc.seq_t fpVesta_t = res.[ 0l ] <- res.[ 0l ] -. s in
  res

let eval_polyx (p: Hacspec_lib_tc.seq_t fpVesta_t) (x: fpVesta_t) : fpVesta_t =
  let res:fpVesta_t = Hacspec_lib_tc.zero in
  let res =
    Hacspec.Lib.foldi 0
      (Hacspec_lib_tc.len p)
      (fun i res -> res +. p.[ i ] *. Hacspec_lib_tc.exp x (cast i))
      res
  in
  res

let degree_polyx (p: Hacspec_lib_tc.seq_t fpVesta_t) : UInt128.t =
  let len:uint_size = Hacspec_lib_tc.len (trim_polyx p) in
  if len = 0 then pub_u128 0 else cast (len - 1)

let check_not_zero_polyx (p: Hacspec_lib_tc.seq_t fpVesta_t) : Prims.bool =
  let sum:fpVesta_t = Hacspec_lib_tc.zero in
  let all_zero:Prims.bool = false in
  let all_zero:Prims.bool =
    Hacspec.Lib.foldi 0
      (Hacspec_lib_tc.len p)
      (fun i all_zero ->
          if Core.Cmp.PartialOrd.gt p.[ i ] Hacspec_lib_tc.zero
          then
            let all_zero:Prims.bool = true in
            all_zero
          else all_zero)
      all_zero
  in
  all_zero

let trim_polyx (p: Hacspec_lib_tc.seq_t fpVesta_t) : Hacspec_lib_tc.seq_t fpVesta_t =
  let last_val_idx:uint_size = 0 in
  let last_val_idx:uint_size =
    Hacspec.Lib.foldi 0
      (Hacspec_lib_tc.len p)
      (fun i last_val_idx ->
          if Core.Cmp.PartialEq.ne p.[ i ] Hacspec_lib_tc.zero
          then
            let last_val_idx:uint_size = i + 1 in
            last_val_idx
          else last_val_idx)
      last_val_idx
  in
  let res:Hacspec_lib_tc.seq_t fpVesta_t = Hacspec_lib_tc.create last_val_idx in
  let res:Hacspec_lib_tc.seq_t fpVesta_t =
    if Hacspec_lib_tc.len p <> 0
    then Hacspec.Lib.foldi 0 (Hacspec_lib_tc.len res) (fun i res -> res.[ i ] <- p.[ i ]) res
    else res
  in
  let res:Hacspec_lib_tc.seq_t fpVesta_t =
    if Hacspec_lib_tc.len p = 0
    then
      let res:Hacspec_lib_tc.seq_t fpVesta_t = p in
      res
    else res
  in
  res

let divide_leading_terms (n d: Hacspec_lib_tc.seq_t fpVesta_t) : Hacspec_lib_tc.seq_t fpVesta_t =
  let (n: Hacspec_lib_tc.seq_t fpVesta_t):Hacspec_lib_tc.seq_t fpVesta_t = trim_polyx n in
  let (d: Hacspec_lib_tc.seq_t fpVesta_t):Hacspec_lib_tc.seq_t fpVesta_t = trim_polyx d in
  let (x_pow: uint_size):uint_size = Hacspec_lib_tc.len n - Hacspec_lib_tc.len d in
  let (n_coeff: fpVesta_t):fpVesta_t = n.[ Hacspec_lib_tc.len n - 1 ] in
  let (d_coeff: fpVesta_t):fpVesta_t = d.[ Hacspec_lib_tc.len d - 1 ] in
  let coeff:fpVesta_t = Core.Ops.Arith.Div.div n_coeff d_coeff in
  let (res: Hacspec_lib_tc.seq_t fpVesta_t):Hacspec_lib_tc.seq_t fpVesta_t =
    Hacspec_lib_tc.create (x_pow + 1)
  in
  let res:Hacspec_lib_tc.seq_t fpVesta_t = res.[ x_pow ] <- coeff in
  res

let divide_polyx (n d: Hacspec_lib_tc.seq_t fpVesta_t)
    : (Hacspec_lib_tc.seq_t fpVesta_t & Hacspec_lib_tc.seq_t fpVesta_t) =
  let (q: Hacspec_lib_tc.seq_t fpVesta_t):Hacspec_lib_tc.seq_t fpVesta_t =
    Hacspec_lib_tc.create (Hacspec_lib_tc.len n)
  in
  let (r: Hacspec_lib_tc.seq_t fpVesta_t):Hacspec_lib_tc.seq_t fpVesta_t =
    Core.Clone.Clone.clone n
  in
  let loop_upper_bound:uint_size = Hacspec_lib_tc.len d in
  let loop_upper_bound:uint_size =
    if Prims.op_GreaterThanOrEqual (Hacspec_lib_tc.len q) (Hacspec_lib_tc.len d)
    then
      let loop_upper_bound:uint_size = Hacspec_lib_tc.len q in
      loop_upper_bound
    else loop_upper_bound
  in
  let q, r:(Hacspec_lib_tc.seq_t fpVesta_t & Hacspec_lib_tc.seq_t fpVesta_t) =
    match
      Core.Iter.Traits.Collect.IntoIterator.into_iter ({
            Core.Ops.Range.start = 0;
            Core.Ops.Range.end = loop_upper_bound
          })
    with
    | iter ->
      let iter, q, r:(Core.Ops.Range.range_t uint_size & Hacspec_lib_tc.seq_t fpVesta_t &
        Hacspec_lib_tc.seq_t fpVesta_t) =
        Hax_error.hax_failure "(Diagnostics.Context.Phase FunctionalizeLoops): something is not implemented yet.\nOnly for loop are being functionalized for now\n"
          "{\n        (loop {\n            |Tuple3(iter, q, r)| {\n                let Tuple2(todo_fresh_var, iter_temp): tuple2<\n                    core::option::Option<proj_asso_type!()>,\n                    core::ops::range::Range<int>,\n                > = { core::iter::traits::iterator::Iterator::next(iter) };\n                {\n                    let iter: core::ops::range::Range<int> = { iter_temp };\n                    {\n                        let hoist1: core::option::Option<proj_asso_type!()> = { todo_fresh_var };\n                        {\n                            let Tuple2(q, r): tuple2<\n                                hacspec_lib::seq::Seq<hacspec_pasta::FpVesta>,\n                                hacspec_lib::seq::Seq<hacspec_pasta::FpVesta>,\n                            > = {\n                                (match hoist1 {\n                                    core::option::None => {\n                                        let _: tuple0 = {\n                                            hax_error::hax_failure(\"(Diagnostics.Context.Phase CfIntoMonads): something is not implemented yet.This is discussed in issue https://github.com/hacspec/hacspec-v2/issues/96.\nPlease upvote or comment this issue if you see this error message.\nTODO: Monad for loop-related control flow\n\",\"(break (Tuple0))\")\n                                        };\n                                        Tuple2(q, r)\n                                    }\n                                    core::option::Some(_) => {\n                                        (if BinOp::Ast.And(\n                                            hacspec_pasta::check_not_zero_polyx(\n                                                core::clone::Clone::clone(r),\n                                            ),\n                                            BinOp::Ast.Ge(\n                                                hacspec_pasta::degree_polyx(\n                                                    core::clone::Clone::clone(r),\n                                                ),\n                                                hacspec_pasta::degree_polyx(\n                                                    core::clone::Clone::clone(d),\n                                                ),\n                                            ),\n                                        ) {\n                                            {\n                                                let pat_ascription!(t as hacspec_lib::seq::Seq<hacspec_pasta::FpVesta>): hacspec_lib::seq::Seq<hacspec_pasta::FpVesta> = {hacspec_pasta::divide_leading_terms(core::clone::Clone::clone(r),core::clone::Clone::clone(d))};\n                                                {\n                                                    let q: hacspec_lib::seq::Seq<\n                                                        hacspec_pasta::FpVesta,\n                                                    > = {\n                                                        hacspec_pasta::add_polyx(\n                                                            q,\n                                                            core::clone::Clone::clone(t),\n                                                        )\n                                                    };\n                                                    {\n                                                        let pat_ascription!(aux_prod as hacspec_lib::seq::Seq<hacspec_pasta::FpVesta>): hacspec_lib::seq::Seq<hacspec_pasta::FpVesta> = {hacspec_pasta::mul_polyx(core::clone::Clone::clone(d),core::clone::Clone::clone(t))};\n                                                        {\n                                                            let r: hacspec_lib::seq::Seq<\n                                                                hacspec_pasta::FpVesta,\n                                                            > = {\n                                                                hacspec_pasta::sub_polyx(\n                                                                    r, aux_prod,\n                                                                )\n                                                            };\n                                                            Tuple2(q, r)\n                                                        }\n                                                    }\n                                                }\n                                            }\n                                        } else {\n                                            Tuple2(q, r)\n                                        })\n                                    }\n                                })\n                            };\n                            Tuple3(iter, q, r)\n                        }\n                    }\n                }\n            }\n        })(Tuple3(iter, q, r))\n    }"

      in
      q, r
  in
  trim_polyx q, trim_polyx r

let multi_poly_with_x (p: Hacspec_lib_tc.seq_t fpVesta_t) : Hacspec_lib_tc.seq_t fpVesta_t =
  multi_poly_with_x_pow p 1

let multi_poly_with_x_pow (p: Hacspec_lib_tc.seq_t fpVesta_t) (power: uint_size)
    : Hacspec_lib_tc.seq_t fpVesta_t =
  let (p: Hacspec_lib_tc.seq_t fpVesta_t):Hacspec_lib_tc.seq_t fpVesta_t = trim_polyx p in
  let (res: Hacspec_lib_tc.seq_t fpVesta_t):Hacspec_lib_tc.seq_t fpVesta_t =
    Hacspec_lib_tc.create (Hacspec_lib_tc.len p + power)
  in
  let res:Hacspec_lib_tc.seq_t fpVesta_t =
    Hacspec.Lib.foldi 0 (Hacspec_lib_tc.len p) (fun i res -> res.[ i + power ] <- p.[ i ]) res
  in
  res

let lagrange_polyx (points: Hacspec_lib_tc.seq_t (fpVesta_t & fpVesta_t))
    : Hacspec_lib_tc.seq_t fpVesta_t =
  let poly:Hacspec_lib_tc.seq_t fpVesta_t = Hacspec_lib_tc.create (Hacspec_lib_tc.len points) in
  let poly:Hacspec_lib_tc.seq_t fpVesta_t =
    Hacspec.Lib.foldi 0
      (Hacspec_lib_tc.len points)
      (fun i poly ->
          let (x: fpVesta_t):fpVesta_t = (points.[ i ])._1 in
          let (y: fpVesta_t):fpVesta_t = (points.[ i ])._2 in
          let basis:Hacspec_lib_tc.seq_t fpVesta_t =
            lagrange_basis (Core.Clone.Clone.clone points) x
          in
          let scaled_basis:Hacspec_lib_tc.seq_t fpVesta_t = mul_scalar_polyx basis y in
          let poly:Hacspec_lib_tc.seq_t fpVesta_t =
            add_polyx (Core.Clone.Clone.clone poly) (Core.Clone.Clone.clone scaled_basis)
          in
          poly)
      poly
  in
  let poly:Hacspec_lib_tc.seq_t fpVesta_t = trim_polyx poly in
  poly

let lagrange_basis (points: Hacspec_lib_tc.seq_t (fpVesta_t & fpVesta_t)) (x: fpVesta_t)
    : Hacspec_lib_tc.seq_t fpVesta_t =
  let basis:Hacspec_lib_tc.seq_t fpVesta_t = Hacspec_lib_tc.create (Hacspec_lib_tc.len points) in
  let basis:Hacspec_lib_tc.seq_t fpVesta_t = basis.[ 0l ] <- Hacspec_lib_tc.oNE in
  let devisor:fpVesta_t = Hacspec_lib_tc.oNE in
  let basis, devisor:(Hacspec_lib_tc.seq_t fpVesta_t & _) =
    Hacspec.Lib.foldi 0
      (Hacspec_lib_tc.len points)
      (fun i (basis, devisor) ->
          let point:(fpVesta_t & fpVesta_t) = points.[ i ] in
          let p_x:fpVesta_t = point._1 in
          if Core.Cmp.PartialEq.ne p_x x
          then
            let devisor = devisor *. (x -. p_x) in
            let poly_mul_x:Hacspec_lib_tc.seq_t fpVesta_t =
              multi_poly_with_x (Core.Clone.Clone.clone basis)
            in
            let (poly_mul_scalar: Hacspec_lib_tc.seq_t fpVesta_t):Hacspec_lib_tc.seq_t fpVesta_t =
              mul_scalar_polyx (Core.Clone.Clone.clone basis) (neg p_x)
            in
            let basis:Hacspec_lib_tc.seq_t fpVesta_t = add_polyx poly_mul_x poly_mul_scalar in
            basis, devisor
          else basis, devisor)
      (basis, devisor)
  in
  let test:fpVesta_t = eval_polyx (Core.Clone.Clone.clone basis) Hacspec_lib_tc.oNE in
  let division_poly:Hacspec_lib_tc.seq_t fpVesta_t =
    Hacspec_lib_tc.create (Hacspec_lib_tc.len points)
  in
  let division_poly:Hacspec_lib_tc.seq_t fpVesta_t = division_poly.[ 0l ] <- devisor in
  let output:(Hacspec_lib_tc.seq_t fpVesta_t & Hacspec_lib_tc.seq_t fpVesta_t) =
    divide_polyx (Core.Clone.Clone.clone basis) (Core.Clone.Clone.clone division_poly)
  in
  let final_basis, _:(Hacspec_lib_tc.seq_t fpVesta_t & Hacspec_lib_tc.seq_t fpVesta_t) = output in
  final_basis

let gen_zero_polyx: Hacspec_lib_tc.seq_t fpVesta_t = Hacspec_lib_tc.create 1

let gen_one_polyx: Hacspec_lib_tc.seq_t fpVesta_t =
  let poly:Hacspec_lib_tc.seq_t fpVesta_t = Hacspec_lib_tc.create 1 in
  let poly:Hacspec_lib_tc.seq_t fpVesta_t = poly.[ 0l ] <- Hacspec_lib_tc.oNE in
  poly

let check_equal_polyx (p1 p2: Hacspec_lib_tc.seq_t fpVesta_t) : Prims.bool =
  let is_equal:Prims.bool = false in
  let is_equal:Prims.bool =
    if
      Hacspec_lib_tc.len (trim_polyx (Core.Clone.Clone.clone p1)) =
      Hacspec_lib_tc.len (trim_polyx (Core.Clone.Clone.clone p2))
    then
      let is_equal:Prims.bool = true in
      Hacspec.Lib.foldi 0
        (Hacspec_lib_tc.len (trim_polyx (Core.Clone.Clone.clone p1)))
        (fun i is_equal ->
            let p1_scaler_i:fpVesta_t = Core.Clone.Clone.clone p1.[ i ] in
            let p2_scaler_i:fpVesta_t = Core.Clone.Clone.clone p2.[ i ] in
            if Core.Cmp.PartialEq.ne p1_scaler_i p2_scaler_i
            then
              let is_equal:Prims.bool = false in
              is_equal
            else is_equal)
        is_equal
    else is_equal
  in
  is_equal