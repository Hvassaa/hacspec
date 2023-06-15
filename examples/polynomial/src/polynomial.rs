#![allow(non_snake_case)]
#![allow(dead_code)]
#![allow(warnings, unused)]

use hacspec_lib::*;

/// A polynomial represented by its coefficient form, such that index i is the i'th term
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
    res[usize::zero()] = res[usize::zero()] + s;

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
    res[usize::zero()] = res[usize::zero()] - s;

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
pub fn degree_polyx(p: Polyx) -> usize {
    let len = trim_polyx(p).len();
    if len == 0 {
        0
    } else {
        (len - 1)
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
    multi_poly_with_x_pow(p, 1)
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

/// Finds the Lagrange basis for a set of `points` and a single evaluation point `x`
/// This will produce a polynomial that evaluates to 1 at `x`and to 0 at all other x-values in the set `points`
/// No other guarentees are given about the resulting polynomial
///
/// # Arguments
/// * `points`is a sequence of points `(Fp,Fp)` whose x-values the polynomial wil evaluate to 0 at
/// * `x`is the x-value where the polynomial will evaluate to 1. If `x`is also in `points` the polynomial will still evaluate to 1 at `x``
/// # Assertions
/// * No two points may have the same x-value
pub fn lagrange_basis(points: Seq<(FpVesta, FpVesta)>, x: FpVesta) -> Polyx {
    let mut basis = Seq::<FpVesta>::create(points.len());
    basis[usize::zero()] = FpVesta::ONE();
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
    division_poly[usize::zero()] = devisor;

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
    poly[usize::zero()] = FpVesta::ONE();
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
#[quickcheck]
fn test_poly_add_logic(p1: PolyxContainer, p2: PolyxContainer, x: usize) {
    let p1 = p1.0;
    let p2 = p2.0;
    let x = FpVesta::from_literal(x as u128);
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

#[cfg(test)]
#[quickcheck]
fn test_poly_mul_logic(p1: PolyxContainer, p2: PolyxContainer, x: usize) {
    let p1 = p1.0;
    let p2 = p2.0;
    let x = FpVesta::from_literal(x as u128);
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
fn test_poly_div(p1: PolyxContainer, p2: PolyxContainer, x: usize) {
    let p1 = p1.0;
    let p2 = p2.0;
    if p2.len() > 0 {
        let x = FpVesta::from_literal(x as u128);

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
fn test_poly_sub(p1: PolyxContainer, p2: PolyxContainer, x: usize) {
    let p1 = p1.0;
    let p2 = p2.0;
    let x = FpVesta::from_literal(x as u128);
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
        .map(|e| FpVesta::from_literal((*e)))
        .collect();
    let p1 = Seq::from_vec(v1);

    assert_eq!(
        eval_polyx(p1, FpVesta::TWO()),
        FpVesta::from_literal(105 as u128)
    );
}

#[cfg(test)]
#[test]
fn test_trim_poly() {
    let p = Seq::from_vec(vec![
        FpVesta::ZERO(),
        FpVesta::from_literal(6 as u128),
        FpVesta::from_literal(4 as u128),
        FpVesta::ZERO(),
        FpVesta::ZERO(),
        FpVesta::from_literal(2 as u128),
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
