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
    Core.Iter.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter ({
              start = 0;
              end = 255
            }))
      t
      (fun i t ->
          let t:(fpPallas_t & fpPallas_t & Prims.bool) = g1double_pallas t in
          if bit m (254 - i)
          then
            let t:(fpPallas_t & fpPallas_t & Prims.bool) = g1add_pallas t p in
            t
          else t)
  in
  t

let g1mul_vesta (m: fpPallas_t) (p: (fpVesta_t & fpVesta_t & Prims.bool))
    : (fpVesta_t & fpVesta_t & Prims.bool) =
  let t:(fpVesta_t & fpVesta_t & Prims.bool) = Hacspec_lib_tc.zero, Hacspec_lib_tc.zero, true in
  let t:(fpVesta_t & fpVesta_t & Prims.bool) =
    Core.Iter.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter ({
              start = 0;
              end = 255
            }))
      t
      (fun i t ->
          let t:(fpVesta_t & fpVesta_t & Prims.bool) = g1double_vesta t in
          if bit m (254 - i)
          then
            let t:(fpVesta_t & fpVesta_t & Prims.bool) = g1add_vesta t p in
            t
          else t)
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