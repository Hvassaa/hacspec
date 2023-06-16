(* File automatically generated by Hacspec *)
From Hacspec Require Import Hacspec_Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.

(*Not implemented yet? todo(item)*)

Require Import Hacspec_lib.

Notation PallasCanvas := (nseq int8 255).
Notation FpPallas_t := (nat_mod 0x40000000000000000000000000000000224698FC094CF91B992D30ED00000001).
Definition FpPallas : FpPallas_t -> FpPallas_t :=
  id.

Record Polynomial_tPolynomial : Type :={
  coefficients : Seq_t T;
}.

(*trait self todo(item)*)

(*item error backend*)

(*item error backend*)

Instance Polynomial_t T_PartialEq : PartialEq Polynomial_t T Polynomial_t T := {
  eq (self : Polynomial_t T) (other : Polynomial_t T) := let equal := (true) : bool in
  let lhs := (coefficients self) : Seq_t T in
  let rhs := (coefficients other) : Seq_t T in
  let equal := (if
      (len lhs)<>(len rhs)
    then
      let equal := (false) : bool in
      equal
    else
      fold (into_iter (Build_Range_t (@repr WORDSIZE32 0)(len lhs))) equal (fun i equal =>
        if
          ne (lhs.[i]) (rhs.[i])
        then
          let equal := (false) : bool in
          equal
        else
          equal)) : bool in
  equal;
}.

Instance Polynomial_t T_Clone : Clone Polynomial_t T := {
  clone (self : Polynomial_t T) := Build_Polynomial_t (clone (coefficients self));
}.
