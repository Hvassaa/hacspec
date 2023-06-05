#![allow(non_snake_case)]
#![allow(warnings, unused)]

use hacspec_lib::*;

// Pallas: y^2 = x^3 + 5
// Vesta: y^2 = x^3 + 5

// The base field for Pallas and the scalar field for Vesta, from https://o1-labs.github.io/proof-systems/specs/pasta.html#pallas:
// 28948022309329048855892746252171976963363056481941560715954676764349967630337, or
// 0x40000000000000000000000000000000224698FC094CF91B992D30ED00000001
public_nat_mod!(
    type_name: FpPallas,
    type_of_canvas: PallasCanvas,
    bit_size_of_field: 255,
    modulo_value: "40000000000000000000000000000000224698FC094CF91B992D30ED00000001"
);

// The scalar field for Vesta and the scalar field for Pallas, from https://o1-labs.github.io/proof-systems/specs/pasta.html#pallas:
// 28948022309329048855892746252171976963363056481941647379679742748393362948097, or
// 422226856838314419923949393447878586741291908259801035138795735055355382073928
// 0x40000000000000000000000000000000224698FC0994A8DD8C46EB2100000001
public_nat_mod!(
    type_name: FpVesta,
    type_of_canvas: VestaCanvas,
    bit_size_of_field: 255,
    modulo_value: "40000000000000000000000000000000224698FC0994A8DD8C46EB2100000001"
);

//bool is "isPointAtInfinity"
pub type G1_pallas = (FpPallas, FpPallas, bool);
pub type G1_vesta = (FpVesta, FpVesta, bool);

/* Arithmetic in G1 */

// Create 'default' G1 element (0,0,true)
pub fn g1_default_pallas() -> G1_pallas {
    (FpPallas::ZERO(), FpPallas::ZERO(), true)
}
pub fn g1_default_vesta() -> G1_vesta {
    (FpVesta::ZERO(), FpVesta::ZERO(), true)
}

//g1 add with no Point at Infinity
fn g1add_a_pallas(p: G1_pallas, q: G1_pallas) -> G1_pallas {
    let (x1, y1, _) = p;
    let (x2, y2, _) = q;

    let x_diff = x2 - x1;
    let y_diff = y2 - y1;
    let xovery = y_diff * x_diff.inv(); //  x / y = x * y^-1
    let x3 = xovery.exp(2u32) - x1 - x2;
    let y3 = xovery * (x1 - x3) - y1;
    (x3, y3, false)
}
fn g1add_a_vesta(p: G1_vesta, q: G1_vesta) -> G1_vesta {
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
fn g1double_a_pallas(p: G1_pallas) -> G1_pallas {
    let (x1, y1, _) = p;

    let x12 = x1.exp(2u32);
    let xovery = (FpPallas::from_literal(3u128) * x12) * (FpPallas::TWO() * y1).inv();
    let x3 = xovery.exp(2u32) - FpPallas::TWO() * x1;
    let y3 = xovery * (x1 - x3) - y1;
    (x3, y3, false)
}
fn g1double_a_vesta(p: G1_vesta) -> G1_vesta {
    let (x1, y1, _) = p;

    let x12 = x1.exp(2u32);
    let xovery = (FpVesta::from_literal(3u128) * x12) * (FpVesta::TWO() * y1).inv();
    let x3 = xovery.exp(2u32) - FpVesta::TWO() * x1;
    let y3 = xovery * (x1 - x3) - y1;
    (x3, y3, false)
}

/* Wrapper functions with Point of Infinity */
pub fn g1double_pallas(p: G1_pallas) -> G1_pallas {
    let (_x1, y1, inf1) = p;
    if y1 != FpPallas::ZERO() && !inf1 {
        g1double_a_pallas(p)
    } else {
        (FpPallas::ZERO(), FpPallas::ZERO(), true)
    }
}
pub fn g1double_vesta(p: G1_vesta) -> G1_vesta {
    let (_x1, y1, inf1) = p;
    if y1 != FpVesta::ZERO() && !inf1 {
        g1double_a_vesta(p)
    } else {
        (FpVesta::ZERO(), FpVesta::ZERO(), true)
    }
}

pub fn g1add_pallas(p: G1_pallas, q: G1_pallas) -> G1_pallas {
    let (x1, y1, inf1) = p;
    let (x2, y2, inf2) = q;

    if inf1 {
        q
    } else {
        if inf2 {
            p
        } else {
            if p == q {
                g1double_pallas(p)
            } else {
                if !(x1 == x2 && y1 == FpPallas::ZERO() - y2) {
                    g1add_a_pallas(p, q)
                } else {
                    (FpPallas::ZERO(), FpPallas::ZERO(), true)
                }
            }
        }
    }
}
pub fn g1add_vesta(p: G1_vesta, q: G1_vesta) -> G1_vesta {
    let (x1, y1, inf1) = p;
    let (x2, y2, inf2) = q;

    if inf1 {
        q
    } else {
        if inf2 {
            p
        } else {
            if p == q {
                g1double_vesta(p)
            } else {
                if !(x1 == x2 && y1 == FpVesta::ZERO() - y2) {
                    g1add_a_vesta(p, q)
                } else {
                    (FpVesta::ZERO(), FpVesta::ZERO(), true)
                }
            }
        }
    }
}

pub fn g1mul_pallas(m: FpVesta, p: G1_pallas) -> G1_pallas {
    let mut t = (FpPallas::ZERO(), FpPallas::ZERO(), true);
    for i in 0..255 {
        //starting from second most significant bit
        t = g1double_pallas(t);
        if m.bit(254 - i) {
            t = g1add_pallas(t, p);
        }
    }
    t
}
pub fn g1mul_vesta(m: FpPallas, p: G1_vesta) -> G1_vesta {
    let mut t = (FpVesta::ZERO(), FpVesta::ZERO(), true);
    for i in 0..255 {
        //starting from second most significant bit
        t = g1double_vesta(t);
        if m.bit(254 - i) {
            t = g1add_vesta(t, p);
        }
    }
    t
}

pub fn g1neg_pallas(p: G1_pallas) -> G1_pallas {
    let (x, y, inf) = p;
    (x, FpPallas::ZERO() - y, inf)
}

pub fn g1neg_vesta(p: G1_vesta) -> G1_vesta {
    let (x, y, inf) = p;
    (x, FpVesta::ZERO() - y, inf)
}

pub fn g1_on_curve_pallas(p: G1_pallas) -> bool {
    let (x, y, inf) = p;
    let y_squared = y * y;
    let x_cubed = x * x * x;
    let fp5 = FpPallas::TWO() + FpPallas::TWO() + FpPallas::ONE();
    // the point is on the curve IFF
    // the point satisfies y^2 = x^3 + 5
    // or it is the infinity point
    (y_squared == x_cubed + fp5) || inf
}
pub fn g1_on_curve_vesta(p: G1_vesta) -> bool {
    let (x, y, inf) = p;
    let y_squared = y * y;
    let x_cubed = x * x * x;
    let fp5 = FpVesta::TWO() + FpVesta::TWO() + FpVesta::ONE();
    // the point is on the curve IFF
    // the point satisfies y^2 = x^3 + 5
    // or it is the infinity point
    (y_squared == x_cubed + fp5) || inf
}

pub fn g1_is_identity_pallas(p: G1_pallas) -> bool {
    let (_, _, inf) = p;
    inf
}
pub fn g1_is_identity_vesta(p: G1_vesta) -> bool {
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
impl Arbitrary for FpPallas {
    fn arbitrary(g: &mut Gen) -> FpPallas {
        let mut a: [u64; 4] = [0; 4];
        for i in 0..4 {
            a[i] = u64::arbitrary(g);
        }
        let mut b: [u8; 32] = [0; 32];
        for i in 0..4 {
            let val: u64 = a[i];
            b[(i * 8)..((i + 1) * 8)].copy_from_slice(&(val.to_le_bytes()));
        }
        b[31] = b[31] & 127;
        FpPallas::from_byte_seq_le(Seq::<U8>::from_public_slice(&b))
    }
}

/* Arbitrary Implementation used for Property Based Tests */
#[cfg(test)]
impl Arbitrary for FpVesta {
    fn arbitrary(g: &mut Gen) -> FpVesta {
        let mut a: [u64; 4] = [0; 4];
        for i in 0..4 {
            a[i] = u64::arbitrary(g);
        }
        let mut b: [u8; 32] = [0; 32];
        for i in 0..4 {
            let val: u64 = a[i];
            b[(i * 8)..((i + 1) * 8)].copy_from_slice(&(val.to_le_bytes()));
        }
        b[31] = b[31] & 127;
        FpVesta::from_byte_seq_le(Seq::<U8>::from_public_slice(&b))
    }
}

#[cfg(test)]
#[derive(Clone, Debug)]
pub struct G1PallasContainer(G1_pallas);

#[cfg(test)]
impl Arbitrary for G1PallasContainer {
    fn arbitrary(g: &mut Gen) -> G1PallasContainer {
        let a = FpVesta::from_literal(u128::arbitrary(g));
        let generator = g1_generator_pallas();
        G1PallasContainer(g1mul_pallas(a, generator))
    }
}

#[cfg(test)]
#[derive(Clone, Debug)]
pub struct G1VestaContainer(G1_vesta);

#[cfg(test)]
impl Arbitrary for G1VestaContainer {
    fn arbitrary(g: &mut Gen) -> G1VestaContainer {
        let a = FpPallas::from_literal(u128::arbitrary(g));
        let generator = g1_generator_vesta();
        G1VestaContainer(g1mul_vesta(a, generator))
    }
}

#[cfg(test)]
#[quickcheck]
fn test_g1_closure_pallas(a: G1PallasContainer, b: G1PallasContainer) {
    let a = a.0;
    let b = b.0;

    let sum = g1add_pallas(a, b);
    assert!(g1_on_curve_pallas(sum));
}
#[cfg(test)]
#[quickcheck]
fn test_g1_closure_vesta(a: G1VestaContainer, b: G1VestaContainer) {
    let a = a.0;
    let b = b.0;

    let sum = g1add_vesta(a, b);
    assert!(g1_on_curve_vesta(sum));
}

#[cfg(test)]
#[quickcheck]
fn test_g1_associativity_pallas(a: G1PallasContainer, b: G1PallasContainer, c: G1PallasContainer) {
    let a = a.0;
    let b = b.0;
    let c = c.0;

    let sum1 = g1add_pallas(g1add_pallas(a, b), c);
    let sum2 = g1add_pallas(a, g1add_pallas(b, c));
    assert_eq!(sum1, sum2);
}
#[cfg(test)]
#[quickcheck]
fn test_g1_associativity_vesta(a: G1VestaContainer, b: G1VestaContainer, c: G1VestaContainer) {
    let a = a.0;
    let b = b.0;
    let c = c.0;

    let sum1 = g1add_vesta(g1add_vesta(a, b), c);
    let sum2 = g1add_vesta(a, g1add_vesta(b, c));
    assert_eq!(sum1, sum2);
}

#[cfg(test)]
#[quickcheck]
fn test_g1_identity_pallas(a: G1PallasContainer) {
    let a = a.0;
    let identity = g1_default_pallas();

    let sum = g1add_pallas(a, identity);

    assert_eq!(sum, a);
}

#[cfg(test)]
#[quickcheck]
fn test_g1_identity_vesta(a: G1VestaContainer) {
    let a = a.0;
    let identity = g1_default_vesta();

    let sum = g1add_vesta(a, identity);

    assert_eq!(sum, a);
}

#[cfg(test)]
#[quickcheck]
fn test_g1_inverse_pallas(a: G1PallasContainer) {
    let a = a.0;
    let a_neg = g1neg_pallas(a);

    let sum = g1add_pallas(a, a_neg);

    assert!(g1_is_identity_pallas(sum));
}
#[cfg(test)]
#[quickcheck]
fn test_g1_inverse_vesta(a: G1VestaContainer) {
    let a = a.0;
    let a_neg = g1neg_vesta(a);

    let sum = g1add_vesta(a, a_neg);

    assert!(g1_is_identity_vesta(sum));
}

#[cfg(test)]
#[test]
fn test_g1_arithmetic_pallas() {
    let g = g1_generator_pallas();

    let g2 = g1double_pallas(g);
    let g4a = g1double_pallas(g2);
    let g3 = g1add_pallas(g2, g);
    let g4b = g1add_pallas(g3, g);
    assert_eq!(g4a, g4b);
}
#[cfg(test)]
#[test]
fn test_g1_arithmetic_vesta() {
    let g = g1_generator_vesta();

    let g2 = g1double_vesta(g);
    let g4a = g1double_vesta(g2);
    let g3 = g1add_vesta(g2, g);
    let g4b = g1add_vesta(g3, g);
    assert_eq!(g4a, g4b);
}

#[cfg(test)]
#[test]
fn test_g1_mul_standard_pallas() {
    let g = g1_generator_pallas();
    let m = FpVesta::ONE();
    assert_eq!(g, g1mul_pallas(m, g));
    let m = FpVesta::from_literal(2u128);
    let g2 = g1double_pallas(g);
    assert_eq!(g2, g1mul_pallas(m, g));
    let m = FpVesta::from_literal(3u128);
    let g3 = g1add_pallas(g, g2);
    assert_eq!(g3, g1mul_pallas(m, g));
}

#[cfg(test)]
#[test]
fn test_g1_mul_standard_vesta() {
    let g = g1_generator_vesta();
    let m = FpPallas::ONE();
    assert_eq!(g, g1mul_vesta(m, g));
    let m = FpPallas::from_literal(2u128);
    let g2 = g1double_vesta(g);
    assert_eq!(g2, g1mul_vesta(m, g));
    let m = FpPallas::from_literal(3u128);
    let g3 = g1add_vesta(g, g2);
    assert_eq!(g3, g1mul_vesta(m, g));
}

#[cfg(test)]
#[test]
fn test_g1_mul_zero_pallas() {
    let g = g1_generator_pallas();
    let m = FpVesta::ZERO();
    let h = g1mul_pallas(m, g);
    assert!(h.2);
}
#[cfg(test)]
#[test]
fn test_g1_mul_zero_vesta() {
    let g = g1_generator_vesta();
    let m = FpPallas::ZERO();
    let h = g1mul_vesta(m, g);
    assert!(h.2);
}

#[cfg(test)]
#[test]
fn test_g1_mul_prop_pallas() {
    fn test_g1_mul_pallas(a: FpVesta) -> bool {
        let g = g1mul_pallas(a, g1_generator_pallas());
        let r = FpVesta::from_hex("0"); //r
        let h = g1mul_pallas(r, g);
        h.2
    }
    //Only needing 5 successes, slow because affine
    QuickCheck::new()
        .tests(5)
        .quickcheck(test_g1_mul_pallas as fn(FpVesta) -> bool);
}

#[cfg(test)]
#[test]
fn test_g1_mul_prop_vesta() {
    fn test_g1_mul_vesta(a: FpPallas) -> bool {
        let g = g1mul_vesta(a, g1_generator_vesta());
        let r = FpPallas::from_hex("0"); //r
        let h = g1mul_vesta(r, g);
        h.2
    }
    //Only needing 5 successes, slow because affine
    QuickCheck::new()
        .tests(5)
        .quickcheck(test_g1_mul_vesta as fn(FpPallas) -> bool);
}

#[cfg(test)]
#[test]
fn test_g1_add_double_equiv_pallas() {
    fn test_g1_mul_pallas(a: FpVesta) -> bool {
        let g = g1mul_pallas(a, g1_generator_pallas());
        g1add_pallas(g, g) == g1double_pallas(g)
    }
    //Only needing 5 successes, slow because affine
    QuickCheck::new()
        .tests(5)
        .quickcheck(test_g1_mul_pallas as fn(FpVesta) -> bool);
}

#[cfg(test)]
#[test]
fn test_g1_add_double_equiv_vesta() {
    fn test_g1_mul_vesta(a: FpPallas) -> bool {
        let g = g1mul_vesta(a, g1_generator_vesta());
        g1add_vesta(g, g) == g1double_vesta(g)
    }
    //Only needing 5 successes, slow because affine
    QuickCheck::new()
        .tests(5)
        .quickcheck(test_g1_mul_vesta as fn(FpPallas) -> bool);
}

#[cfg(test)]
#[test]
fn test_g1_add_double_special_case_pallas() {
    let g = (FpPallas::TWO(), FpPallas::ZERO(), false);
    assert_eq!(g1add_pallas(g, g), g1double_pallas(g));
}

#[cfg(test)]
#[test]
fn test_g1_add_double_special_case_vesta() {
    let g = (FpVesta::TWO(), FpVesta::ZERO(), false);
    assert_eq!(g1add_vesta(g, g), g1double_vesta(g));
}

// Generators taken from:
// https://o1-labs.github.io/proof-systems/specs/pasta.html#pallas
// (mina generator pallas: (1,12418654782883325593414442427049395787963493412651469444558597405572177144507))
#[cfg(test)]
pub fn g1_generator_pallas() -> G1_pallas {
    (
        FpPallas::from_hex("1"),
        FpPallas::from_hex("1B74B5A30A12937C53DFA9F06378EE548F655BD4333D477119CF7A23CAED2ABB"),
        false,
    )
}

// (mina generator vesta: (1,11426906929455361843568202299992114520848200991084027513389447476559454104162))
#[cfg(test)]
pub fn g1_generator_vesta() -> G1_vesta {
    (
        FpVesta::from_hex("1"),
        FpVesta::from_hex("1943666EA922AE6B13B64E3AAE89754CACCE3A7F298BA20C4E4389B9B0276A62"),
        false,
    )
}

/// HERE STARTS IMPLEMENTATION FOR THE POLYNOMIAL RING OVER THE VESTA FIELD ///

pub type Polyx = Seq<FpVesta>;

/// Add two polynomials, return resulting polynomial
///
/// # Arguments
///
/// * `p1` - the LHS polynomial
/// * `p2` - the RHS polynomial
pub fn add_polyx(p1: Polyx, p2: Polyx) -> Polyx {
    let mut res = Seq::<FpVesta>::create(0);
    let mut short_len = 0;

    if p1.len() > p2.len() {
        res = p1.clone();
        short_len = p2.len();
    } else {
        res = p2.clone();
        short_len = p1.len();
    }

    for i in 0..short_len {
        res[i] = p1[i] + p2[i];
    }

    trim_polyx(res)
}

/// Subtract two polynomials, return resulting polynomial
///
/// # Arguments
///
/// * `p1` - the LHS polynomial
/// * `p2` - the RHS polynomial
pub fn sub_polyx(p1: Polyx, p2: Polyx) -> Polyx {
    let mut largest = p1.len();
    if p2.len() > p1.len() {
        largest = p2.len();
    }

    let mut res = Seq::<FpVesta>::create(largest);
    for i in 0..p1.len() {
        res[i] = p1[i];
    }

    for i in 0..p2.len() {
        res[i] = res[i] - p2[i];
    }

    trim_polyx(res)
}

/// Polynomial multiplication using sparse multiplication.
/// This can be more efficient than operand scanning but also prone to side-channel
/// attacks.
/// Mostly copied from hacspec's poly_mul
///
/// # Arguments
///
/// * `p1` LHS polynomial
/// * `p2` RHS polynomial
pub fn mul_polyx(a: Polyx, b: Polyx) -> Polyx {
    let mut result = Seq::<FpVesta>::create(a.len() + b.len());
    for i in 0..a.len() {
        if !a[i].equal(FpVesta::default()) {
            for j in 0..b.len() {
                if !b[j].equal(FpVesta::default()) {
                    result[i + j] = (result[i + j].add(a[i] * b[j]));
                }
            }
        }
    }
    trim_polyx(result)
}

/// Multiply a polynomial by a scalar, return resulting polynomial
///
/// # Arguments
///
/// * `p` - the polynomial
/// * `s` - the scalar
pub fn mul_scalar_polyx(p: Polyx, s: FpVesta) -> Polyx {
    let mut res = p.clone();

    for i in 0..res.len() {
        res[i] = p[i] * s;
    }

    res
}

/// Add a scalar (constant) from a polynomial, return resulting polynomial
///
/// # Arguments
///
/// * `p` - the polynomial
/// * `s` - the scalar
pub fn add_scalar_polyx(p: Polyx, s: FpVesta) -> Polyx {
    let mut res = p.clone();
    if res.len() == 0 {
        // if poly empty, initialize res to zero constant term
        res = Seq::<FpVesta>::create(1);
    }

    // do the addition on constant term
    res[0] = res[0] + s;

    res
}

/// Subtract a scalar (constant) from a polynomial, return resulting polynomial
///
/// # Arguments
///
/// * `p` - the polynomial
/// * `s` - the scalar
pub fn sub_scalar_polyx(p: Polyx, s: FpVesta) -> Polyx {
    let mut res = p.clone();
    if res.len() == 0 {
        // if poly empty, initialize res to zero constant term
        res = Seq::<FpVesta>::create(1);
    }

    // do the subtraction on constant term
    res[0] = res[0] - s;

    res
}

/// Evaluate a polynomial at point, return the evaluation
///
/// # Arguments
///
/// * `p` - the polynomial
/// * `x` - the point
pub fn eval_polyx(p: Polyx, x: FpVesta) -> FpVesta {
    let mut res = FpVesta::ZERO();

    for i in 0..p.len() {
        res = res + p[i] * x.exp(i as u32);
    }

    res
}

/// Get the degree of a polynomial
///
/// # Arguments
///
/// * `p` - the polynomial
pub fn degree_polyx(p: Polyx) -> u128 {
    let len = trim_polyx(p).len();
    if len == 0 {
        0
    } else {
        (len - 1) as u128
    }
}

/// Checks if all entries in a polynomial is 0
/// # Arguments
/// * `p` the polynomial to be checked
/// # Returns
/// * `true` if polynomial is NOT all 0
/// * `false`if polynomial IS all 0
pub fn check_not_zero_polyx(p: Polyx) -> bool {
    let mut sum = FpVesta::ZERO();
    let mut all_zero = false;
    for i in 0..p.len() {
        if p[i] > FpVesta::ZERO() {
            all_zero = true;
        }
    }
    all_zero
}

/// Trim a polynomial of trailing zeros (zero-terms) and return it
///
/// # Arguments
///
/// * `p` - the polynomial
pub fn trim_polyx(p: Polyx) -> Polyx {
    let mut last_val_idx = 0;
    for i in 0..p.len() {
        if p[i] != FpVesta::ZERO() {
            last_val_idx = i + 1;
        }
    }
    let mut res = Seq::<FpVesta>::create(last_val_idx);
    if p.len() != 0 {
        for i in 0..res.len() {
            res[i] = p[i];
        }
    }

    if p.len() == 0 {
        res = p;
    }

    res
}

/// divide the leading terms of two polynomials, returning a single term (e.g. 5x^3) represented as a polynomial
/// (helper function for divide_poly)
///
/// # Arguments
///
/// * `n` - the dividend/enumerator polynomial
/// * `d` - the divisor/denominator polynomial
pub fn divide_leading_terms(n: Polyx, d: Polyx) -> Polyx {
    let n: Polyx = trim_polyx(n);
    let d: Polyx = trim_polyx(d);
    let x_pow: usize = n.len() - d.len();
    let n_coeff: FpVesta = n[n.len() - 1];
    let d_coeff: FpVesta = d[d.len() - 1];
    let coeff: FpVesta = n_coeff / d_coeff;
    let mut res: Polyx = Seq::<FpVesta>::create(x_pow + 1);
    res[x_pow] = coeff;

    res
}

/// Perform polynomial long division, returning the quotient and the remainder.
/// The algorithm is from <https://en.wikipedia.org/wiki/Polynomial_long_division>.
///
/// The pseudo-code is shown here:
///
/// ```text
/// function n / d is
///  require d ≠ 0
///  q ← 0
///  r ← n             // At each step n = d × q + r
///
///  while r ≠ 0 and degree(r) ≥ degree(d) do
///      t ← lead(r) / lead(d)       // Divide the leading terms
///      q ← q + t
///      r ← r − t × d
///
///  return (q, r)
/// ```
///
/// # Arguments
///
/// * `n` - the dividend/enumerator polynomial
/// * `d` - the divisor/denominator polynomial
pub fn divide_polyx(n: Polyx, d: Polyx) -> (Polyx, Polyx) {
    let mut q: Polyx = Seq::<FpVesta>::create(n.len());
    let mut r: Polyx = n.clone();

    let mut loop_upper_bound = d.len();
    if q.len() > d.len() {
        loop_upper_bound = q.len();
    }
    for _ in 0..loop_upper_bound {
        if check_not_zero_polyx(r.clone()) && degree_polyx(r.clone()) >= degree_polyx(d.clone()) {
            let t: Polyx = divide_leading_terms(r.clone(), d.clone());

            q = add_polyx(q, t.clone());
            let aux_prod: Polyx = mul_polyx(d.clone(), t.clone());
            r = sub_polyx(r, aux_prod);
        }
    }

    (trim_polyx(q), trim_polyx(r))
}

/// Wrapper function for multiplying a polynomial with the indeterminate
/// # Arguments
/// * `p` - The polynomial to be multiplied with the indeterminate
pub fn multi_poly_with_x(p: Polyx) -> Polyx {
    multi_poly_with_x_pow(p, 1 as usize)
}

/// Wrapper function for multiplying a polynomial with the indeterminate multiple times
/// # Arguments
/// * `p` - the polynomial to be multiplied with the inderterminate
/// * `power` - the number of times the indeterminate should be multiplied to the polynomial
pub fn multi_poly_with_x_pow(p: Polyx, power: usize) -> Polyx {
    let p: Polyx = trim_polyx(p);
    let mut res: Polyx = Seq::<FpVesta>::create(p.len() + power);

    for i in 0..p.len() {
        res[i + power] = p[i];
    }
    res
}

///Find lowest degree polynomial passing through a set points using legrange interpolation
/// # Arguments
/// * `points`is a sequence of points `(Fp,Fp)` that the polynomial must pass through
/// # Assertions
/// * No two points may have the same x-value.
pub fn lagrange_polyx(points: Seq<(FpVesta, FpVesta)>) -> Polyx {
    let mut poly = Seq::<FpVesta>::create(points.len());

    for i in 0..points.len() {
        let x: FpVesta = points[i].0;
        let y: FpVesta = points[i].1;
        let basis = lagrange_basis(points.clone(), x);
        let scaled_basis = mul_scalar_polyx(basis, y);
        poly = add_polyx(poly.clone(), scaled_basis.clone());
    }
    poly = trim_polyx(poly);
    poly
}
/// Finds the legrange basis for a set of `points` and a single evaluation point `x`
/// This will produce a polynomial that evaluates to 1 at `x`and to 0 at all other x-values in the set `points`
/// No other guarentees are given about the resulting polynomial
/// # Arguments
/// * `points`is a sequence of points `(Fp,Fp)` whose x-values the polynomial wil evaluate to 0 at
/// * `x`is the x-value where the polynomial will evaluate to 1. If `x`is also in `points` the polynomial will still evaluate to 1 at `x``
/// # Assertions
/// * No two points may have the same x-value
pub fn lagrange_basis(points: Seq<(FpVesta, FpVesta)>, x: FpVesta) -> Polyx {
    let mut basis = Seq::<FpVesta>::create(points.len());
    basis[0] = FpVesta::ONE();
    let mut devisor = FpVesta::ONE();
    for i in 0..points.len() {
        let point = points[i];
        let p_x = point.0;
        if p_x != x {
            devisor = devisor.mul(x.sub(p_x));
            let poly_mul_x = multi_poly_with_x(basis.clone());
            let poly_mul_scalar: Polyx = mul_scalar_polyx(basis.clone(), p_x.neg());
            basis = add_polyx(poly_mul_x, poly_mul_scalar);
        }
    }
    let test = eval_polyx(basis.clone(), FpVesta::ONE());
    let mut division_poly = Seq::<FpVesta>::create(points.len());
    division_poly[0] = devisor;

    let output = divide_polyx(basis.clone(), division_poly.clone());

    let (final_basis, _) = output;

    final_basis
}

// functions used for testing of polyx

fn gen_zero_polyx() -> Polyx {
    let poly = Seq::<FpVesta>::create(1);
    poly
}

fn gen_one_polyx() -> Polyx {
    let mut poly = Seq::<FpVesta>::create(1);
    poly[0] = FpVesta::ONE();
    poly
}

fn check_equal_polyx(p1: Polyx, p2: Polyx) -> bool {
    let mut is_equal = false;
    if trim_polyx(p1.clone()).len() == trim_polyx(p2.clone()).len() {
        is_equal = true;
        for i in 0..trim_polyx(p1.clone()).len() {
            let p1_scaler_i = p1[i].clone();
            let p2_scaler_i = p2[i].clone();
            if p1_scaler_i != p2_scaler_i {
                is_equal = false;
            }
        }
    }
    is_equal
}
#[cfg(test)]
#[derive(Clone, Debug, Default)]
struct PolyxContainer(Polyx);
#[cfg(test)]
impl Arbitrary for PolyxContainer {
    fn arbitrary(g: &mut quickcheck::Gen) -> PolyxContainer {
        let size = u8::arbitrary(g);
        let mut v: Vec<FpVesta> = vec![];
        for _ in 0..size {
            let new_val: FpVesta = FpVesta::from_literal(u128::arbitrary(g));
            v.push(new_val);
        }
        PolyxContainer(Seq::<FpVesta>::from_vec(v))
    }
}

#[cfg(test)]
#[derive(Clone, Debug)]
struct Points(Seq<(FpVesta, FpVesta)>);

#[cfg(test)]
impl Arbitrary for Points {
    fn arbitrary(g: &mut quickcheck::Gen) -> Points {
        let size = u8::arbitrary(g);
        let mut x_cords = vec![];
        let mut points = vec![];
        for _ in 0..size {
            let x: FpVesta = FpVesta::from_literal(u128::arbitrary(g));
            let y: FpVesta = FpVesta::from_literal(u128::arbitrary(g));
            if !x_cords.contains(&x) {
                points.push((x, y));
                x_cords.push(x)
            }
        }
        Points(Seq::<(FpVesta, FpVesta)>::from_vec(points))
    }
}

#[cfg(test)]
#[quickcheck]
fn test_poly_add_logic(p1: PolyxContainer, p2: PolyxContainer, x: u128) {
    let p1 = p1.0;
    let p2 = p2.0;
    let x = FpVesta::from_literal(x);
    let sum_poly = add_polyx(p1.clone(), p2.clone());

    let expected = eval_polyx(p1, x) + eval_polyx(p2, x);
    let actual = eval_polyx(sum_poly, x);
    assert_eq!(expected, actual);
}

#[cfg(test)]
#[quickcheck]
fn test_poly_add_closure(p1: PolyxContainer, p2: PolyxContainer) {
    let p1 = p1.0;
    let p2 = p2.0;
    let p3 = add_polyx(p1.clone(), p2.clone());
}

#[cfg(test)]
#[quickcheck]
fn test_poly_add_associativity(p1: PolyxContainer, p2: PolyxContainer, p3: PolyxContainer) {
    let p1 = p1.0;
    let p2 = p2.0;
    let p3 = p3.0;
    let p4 = add_polyx(p1.clone(), p2.clone());
    let p4 = add_polyx(p4.clone(), p3.clone());
    let p5 = add_polyx(p2.clone(), p3.clone());
    let p5 = add_polyx(p5.clone(), p1.clone());
    assert!(check_equal_polyx(p5, p4))
}

#[cfg(test)]
#[quickcheck]
fn test_poly_add_identity(p1: PolyxContainer) {
    let p1 = p1.0;

    let p2 = add_polyx(p1.clone(), gen_zero_polyx());

    let p3 = add_polyx(gen_zero_polyx(), p1.clone());

    assert!(check_equal_polyx(p1, p2.clone()));
    assert!(check_equal_polyx(p3, p2));
}

#[cfg(test)]
#[quickcheck]
fn test_poly_add_inverse(p1: PolyxContainer) {
    let p1 = p1.0;
    let p1_inv = sub_polyx(gen_zero_polyx(), p1.clone());
    let p3 = add_polyx(p1.clone(), p1_inv.clone());
    let p4 = add_polyx(p1_inv, p1);
    assert!(check_equal_polyx(p3.clone(), p4));
    assert!(check_equal_polyx(p3, gen_zero_polyx()));
}

#[cfg(test)]
#[quickcheck]
fn test_poly_add_cummutativity(p1: PolyxContainer, p2: PolyxContainer) {
    let p1 = p1.0;
    let p2 = p2.0;
    let p3 = add_polyx(p1.clone(), p2.clone());
    let p4 = add_polyx(p2.clone(), p1.clone());
    assert!(check_equal_polyx(p3.clone(), p4));
}

#[cfg(test)]
#[quickcheck]
fn test_poly_add_right_distributive(p1: PolyxContainer, p2: PolyxContainer, p3: PolyxContainer) {
    let p1 = p1.0;
    let p2 = p2.0;
    let p3 = p3.0;

    // p4 = p1 * (p2 + p3)
    let p4 = add_polyx(p1.clone(), p2.clone());
    let p4 = mul_polyx(p4.clone(), p3.clone());

    // p5 = (p1 * p2) + (p1 * p3)
    let p5 = mul_polyx(p1.clone(), p3.clone());
    let p6 = mul_polyx(p2.clone(), p3.clone());
    let p5 = add_polyx(p5.clone(), p6.clone());
    assert!(check_equal_polyx(p4, p5));
}

//////////////////

#[cfg(test)]
#[quickcheck]
fn test_poly_mul_logic(p1: PolyxContainer, p2: PolyxContainer, x: u128) {
    let p1 = p1.0;
    let p2 = p2.0;
    let x = FpVesta::from_literal(x);
    let mul_poly = mul_polyx(p1.clone(), p2.clone());

    let expected = eval_polyx(p1, x) * eval_polyx(p2, x);
    let actual = eval_polyx(mul_poly, x);
    assert_eq!(expected, actual);
}

#[cfg(test)]
#[quickcheck]
fn test_poly_mul_closure(p1: PolyxContainer, p2: PolyxContainer) {
    let p1 = p1.0;
    let p2 = p2.0;
    let p3 = mul_polyx(p1.clone(), p2.clone());
}

#[cfg(test)]
#[quickcheck]
fn test_poly_mul_associativity(p1: PolyxContainer, p2: PolyxContainer, p3: PolyxContainer) {
    let p1 = p1.0;
    let p2 = p2.0;
    let p3 = p3.0;
    let p4 = mul_polyx(p1.clone(), p2.clone());
    let p4 = mul_polyx(p4.clone(), p3.clone());
    let p5 = mul_polyx(p2.clone(), p3.clone());
    let p5 = mul_polyx(p5.clone(), p1.clone());
    assert!(check_equal_polyx(p5, p4))
}

#[cfg(test)]
#[quickcheck]
fn test_poly_mul_identity(p1: PolyxContainer) {
    let p1 = p1.0;
    let p2 = mul_polyx(p1.clone(), gen_one_polyx());
    let p3 = mul_polyx(gen_one_polyx(), p1.clone());
    assert!(check_equal_polyx(p1, p2.clone()));
    assert!(check_equal_polyx(p3, p2));
}

#[cfg(test)]
#[quickcheck]
fn test_poly_mul_cummutativity(p1: PolyxContainer, p2: PolyxContainer) {
    let p1 = p1.0;
    let p2 = p2.0;
    let p3 = mul_polyx(p1.clone(), p2.clone());
    let p4 = mul_polyx(p2.clone(), p1.clone());
    assert!(check_equal_polyx(p3, p4));
}

#[cfg(test)]
#[quickcheck]
fn test_poly_mul_left_distributive(p1: PolyxContainer, p2: PolyxContainer, p3: PolyxContainer) {
    let p1 = p1.0;
    let p2 = p2.0;
    let p3 = p3.0;
    // p4 = p1 * (p2 + p3)
    let p4 = add_polyx(p2.clone(), p3.clone());
    let p4 = mul_polyx(p4.clone(), p1.clone());
    // p5 = (p1 * p2) + (p1 * p3)
    let p5 = mul_polyx(p1.clone(), p2.clone());
    let p6 = mul_polyx(p1.clone(), p3.clone());
    let p5 = add_polyx(p5.clone(), p6.clone());
    assert!(check_equal_polyx(p4, p5));
}
///////////////////

#[cfg(test)]
#[quickcheck]
fn test_poly_div(p1: PolyxContainer, p2: PolyxContainer, x: u128) {
    let p1 = p1.0;
    let p2 = p2.0;
    if p2.len() > 0 {
        let x = FpVesta::from_literal(x);

        let (q, r) = divide_polyx(p1.clone(), p2.clone());
        let eval_q = eval_polyx(q, x);
        let eval_r = eval_polyx(r, x);
        let eval_r_div = eval_r / eval_polyx(p2.clone(), x);

        let expected = eval_polyx(p1, x) / eval_polyx(p2.clone(), x);
        let actual = eval_q + eval_r_div;

        assert_eq!(expected, actual);
    }
}

#[cfg(test)]
#[quickcheck]
fn test_poly_sub(p1: PolyxContainer, p2: PolyxContainer, x: u128) {
    let p1 = p1.0;
    let p2 = p2.0;
    let x = FpVesta::from_literal(x);
    let sum_poly = sub_polyx(p1.clone(), p2.clone());

    let expected = eval_polyx(p1, x) - eval_polyx(p2, x);
    let actual = eval_polyx(sum_poly, x);
    assert_eq!(expected, actual);
}

#[cfg(test)]
#[test]
fn test_poly_eval() {
    let v1 = vec![5, 10, 20]
        .iter()
        .map(|e| FpVesta::from_literal((*e) as u128))
        .collect();
    let p1 = Seq::from_vec(v1);

    assert_eq!(eval_polyx(p1, FpVesta::TWO()), FpVesta::from_literal(105));
}

#[cfg(test)]
#[test]
fn test_trim_poly() {
    let p = Seq::from_vec(vec![
        FpVesta::ZERO(),
        FpVesta::from_literal(6),
        FpVesta::from_literal(4),
        FpVesta::ZERO(),
        FpVesta::ZERO(),
        FpVesta::from_literal(2),
        FpVesta::ZERO(),
        FpVesta::ZERO(),
        FpVesta::ZERO(),
    ]);

    let trimmed_p = trim_polyx(p.clone());
    assert_eq!(trimmed_p.len(), p.len() - 3);
}

#[cfg(test)]
#[quickcheck]
fn test_lagrange(a: Points) {
    let points_seq = a.0;

    let legrange_poly = lagrange_polyx(points_seq.clone());

    for j in 0..points_seq.len() {
        let eval_x = points_seq[j].0;
        let point_y = points_seq[j].1;
        let res = eval_polyx(legrange_poly.clone(), eval_x);
        assert_eq!(res, point_y)
    }
}

#[cfg(test)]
#[quickcheck]
fn test_lagrange_basis(a: Points) {
    let points_seq = a.0;
    // let points_seq = Seq::<(Fp, Fp)>::from_vec(vec![
    //     (Fp::from_literal(1), Fp::from_literal(2)),
    //     (Fp::from_literal(2), Fp::from_literal(3)),
    //     (Fp::from_literal(5), Fp::from_literal(0)),
    // ]);

    for i in 0..points_seq.len() {
        let x = points_seq[i].0;
        let basis = lagrange_basis(points_seq.clone(), x);
        for j in 0..points_seq.len() {
            let eval_x = points_seq[j].0;
            let res = eval_polyx(basis.clone(), eval_x);
            if x == eval_x {
                assert_eq!(res, FpVesta::ONE())
            } else {
                assert_eq!(res, FpVesta::ZERO())
            }
        }
    }
}
