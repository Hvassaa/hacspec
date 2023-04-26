#![allow(non_snake_case)]
#![allow(warnings, unused)]

use hacspec_lib::*;

// Pallas: y^2 = x^3 + 5

// The base field for Pallas, from https://o1-labs.github.io/proof-systems/specs/pasta.html#pallas:
// 28948022309329048855892746252171976963363056481941560715954676764349967630337, or
// 0x40000000000000000000000000000000224698FC094CF91B992D30ED00000001
public_nat_mod!(
    type_name: FpCurve,
    type_of_canvas: FpCanvas,
    bit_size_of_field: 255,
    modulo_value: "40000000000000000000000000000000224698FC094CF91B992D30ED00000001"
);

// The scalar field for Pallas, from https://o1-labs.github.io/proof-systems/specs/pasta.html#pallas:
// 28948022309329048855892746252171976963363056481941647379679742748393362948097, or
// 0x40000000000000000000000000000000224698FC0994A8DD8C46EB2100000001
public_nat_mod!(
    type_name: Fp,
    type_of_canvas: ScalarCanvas,
    bit_size_of_field: 255,
    modulo_value: "40000000000000000000000000000000224698FC0994A8DD8C46EB2100000001"
);

//bool is "isPointAtInfinity"
pub type G1 = (FpCurve, FpCurve, bool);

/* Arithmetic in G1 */

// Create 'default' G1 element (0,0,true)
pub fn g1_default() -> G1 {
    (FpCurve::ZERO(), FpCurve::ZERO(), true)
}

//g1 add with no Point at Infinity
fn g1add_a(p: G1, q: G1) -> G1 {
    let (x1, y1, _) = p;
    let (x2, y2, _) = q;

    let x_diff = x2 - x1;
    let y_diff = y2 - y1;
    let xovery = y_diff * x_diff.inv(); //  x / y = x * y^-1
    let x3 = xovery.exp(2u32) - x1 - x2;
    let y3 = xovery * (x1 - x3) - y1;
    (x3, y3, false)
}

//g1 double with no Point at Infinity
fn g1double_a(p: G1) -> G1 {
    let (x1, y1, _) = p;

    let x12 = x1.exp(2u32);
    let xovery = (FpCurve::from_literal(3u128) * x12) * (FpCurve::TWO() * y1).inv();
    let x3 = xovery.exp(2u32) - FpCurve::TWO() * x1;
    let y3 = xovery * (x1 - x3) - y1;
    (x3, y3, false)
}

/* Wrapper functions with Point of Infinity */
pub fn g1double(p: G1) -> G1 {
    let (_x1, y1, inf1) = p;
    if y1 != FpCurve::ZERO() && !inf1 {
        g1double_a(p)
    } else {
        (FpCurve::ZERO(), FpCurve::ZERO(), true)
    }
}

pub fn g1add(p: G1, q: G1) -> G1 {
    let (x1, y1, inf1) = p;
    let (x2, y2, inf2) = q;

    if inf1 {
        q
    } else {
        if inf2 {
            p
        } else {
            if p == q {
                g1double(p)
            } else {
                if !(x1 == x2 && y1 == FpCurve::ZERO() - y2) {
                    g1add_a(p, q)
                } else {
                    (FpCurve::ZERO(), FpCurve::ZERO(), true)
                }
            }
        }
    }
}

pub fn g1mul(m: Fp, p: G1) -> G1 {
    let mut t = (FpCurve::ZERO(), FpCurve::ZERO(), true);
    for i in 0..256 {
        //starting from second most significant bit
        t = g1double(t);
        if m.bit(255 - i) {
            t = g1add(t, p);
        }
    }
    t
}

pub fn g1neg(p: G1) -> G1 {
    let (x, y, inf) = p;
    (x, FpCurve::ZERO() - y, inf)
}

pub fn g1_on_curve(p: G1) -> bool {
    let (x, y, inf) = p;
    let y_squared = y * y;
    let x_cubed = x * x * x;
    let fp5 = FpCurve::TWO() + FpCurve::TWO() + FpCurve::ONE();
    // the point is on the curve IFF
    // the point satisfies y^2 = x^3 + 5
    // or it is the infinity point
    (y_squared == x_cubed + fp5) || inf
}

pub fn g1_is_identity(p: G1) -> bool {
    let (_, _, inf) = p;
    inf
}

#[cfg(test)]
extern crate quickcheck;
#[cfg(test)]
#[macro_use(quickcheck)]
extern crate quickcheck_macros;
#[cfg(test)]
use quickcheck::*;

// Arbitrary implementation is needed to randomly generate arbitrary elements of the specified type.
// Used in Property based testing to generate random tests

/* Arbitrary Implementation used for Property Based Tests */
#[cfg(test)]
impl Arbitrary for FpCurve {
    fn arbitrary(g: &mut Gen) -> FpCurve {
        let mut a: [u64; 6] = [0; 6];
        for i in 0..6 {
            a[i] = u64::arbitrary(g);
        }
        let mut b: [u8; 48] = [0; 48];
        for i in 0..6 {
            let val: u64 = a[i];
            b[(i * 8)..((i + 1) * 8)].copy_from_slice(&(val.to_le_bytes()));
        }
        FpCurve::from_byte_seq_le(Seq::<U8>::from_public_slice(&b))
    }
}

/* Arbitrary Implementation used for Property Based Tests */
#[cfg(test)]
impl Arbitrary for Fp {
    fn arbitrary(g: &mut Gen) -> Fp {
        let mut a: [u64; 4] = [0; 4];
        for i in 0..4 {
            a[i] = u64::arbitrary(g);
        }
        let mut b: [u8; 32] = [0; 32];
        for i in 0..4 {
            let val: u64 = a[i];
            b[(i * 8)..((i + 1) * 8)].copy_from_slice(&(val.to_le_bytes()));
        }
        Fp::from_byte_seq_le(Seq::<U8>::from_public_slice(&b))
    }
}

#[cfg(test)]
#[derive(Clone, Debug)]
struct G1_container(G1);

#[cfg(test)]
impl Arbitrary for G1_container {
    fn arbitrary(g: &mut Gen) -> G1_container {
        let a = Fp::from_literal(u128::arbitrary(g));
        let generator = g1_generator();
        G1_container(g1mul(a, generator))
    }
}

#[cfg(test)]
#[quickcheck]
fn test_g1_closure(a: G1_container, b: G1_container) {
    let a = a.0;
    let b = b.0;

    let sum = g1add(a, b);
    assert!(g1_on_curve(sum));
}

#[cfg(test)]
#[quickcheck]
fn test_g1_associativity(a: G1_container, b: G1_container, c: G1_container) {
    let a = a.0;
    let b = b.0;
    let c = c.0;

    let sum1 = g1add(g1add(a, b), c);
    let sum2 = g1add(a, g1add(b, c));
    assert_eq!(sum1, sum2);
}

#[cfg(test)]
#[quickcheck]
fn test_g1_identity(a: G1_container) {
    let a = a.0;
    let identity = g1_default();

    let sum = g1add(a, identity);

    assert_eq!(sum, a);
}

#[cfg(test)]
#[quickcheck]
fn test_g1_inverse(a: G1_container) {
    let a = a.0;
    let a_neg = g1neg(a);

    let sum = g1add(a, a_neg);

    assert!(g1_is_identity(sum));
}

#[cfg(test)]
#[test]
fn test_g1_arithmetic() {
    let g = g1_generator();

    let g2 = g1double(g);
    let g4a = g1double(g2);
    let g3 = g1add(g2, g);
    let g4b = g1add(g3, g);
    assert_eq!(g4a, g4b);
}

#[cfg(test)]
#[test]
fn test_g1_mul_standard() {
    let g = g1_generator();
    let m = Fp::ONE();
    assert_eq!(g, g1mul(m, g));
    let m = Fp::from_literal(2u128);
    let g2 = g1double(g);
    assert_eq!(g2, g1mul(m, g));
    let m = Fp::from_literal(3u128);
    let g3 = g1add(g, g2);
    assert_eq!(g3, g1mul(m, g));
}

#[cfg(test)]
#[test]
fn test_g1_mul_zero() {
    let g = g1_generator();
    let m = Fp::ZERO();
    let h = g1mul(m, g);
    assert!(h.2);
}

#[cfg(test)]
#[test]
fn test_g1_mul_prop() {
    fn test_g1_mul(a: Fp) -> bool {
        let g = g1mul(a, g1_generator());
        let r = Fp::from_hex("40000000000000000000000000000000224698fc0994a8dd8c46eb2100000001"); //r
        let h = g1mul(r, g);
        h.2
    }
    //Only needing 5 successes, slow because affine
    QuickCheck::new()
        .tests(5)
        .quickcheck(test_g1_mul as fn(Fp) -> bool);
}

#[cfg(test)]
#[test]
fn test_g1_add_double_equiv() {
    fn test_g1_mul(a: Fp) -> bool {
        let g = g1mul(a, g1_generator());
        g1add(g, g) == g1double(g)
    }
    //Only needing 5 successes, slow because affine
    QuickCheck::new()
        .tests(5)
        .quickcheck(test_g1_mul as fn(Fp) -> bool);
}

#[cfg(test)]
#[test]
fn test_g1_add_double_special_case() {
    let g = (FpCurve::TWO(), FpCurve::ZERO(), false);
    assert_eq!(g1add(g, g), g1double(g));
}

// Generators taken from:
// https://o1-labs.github.io/proof-systems/specs/pasta.html#pallas
// (mina generator: (1,12418654782883325593414442427049395787963493412651469444558597405572177144507))
#[cfg(test)]
pub fn g1_generator() -> G1 {
    (
        FpCurve::from_hex("1"),
        FpCurve::from_hex("1B74B5A30A12937C53DFA9F06378EE548F655BD4333D477119CF7A23CAED2ABB"),
        false,
    )
}
