#![doc = include_str!("../table.md")]
#![allow(non_snake_case)]
#![allow(dead_code)]
#![allow(warnings, unused)]

use hacspec_lib::*;
use hacspec_pasta::*;

/// A struct for the public parameters, pp
//
/// Since the group and field is currently fixed, only G, U, W is represented
struct PublicParams(
    /// **G** in G^n
    Seq<G1>,
    /// U in G
    G1,
    /// W in G
    G1,
);

/// Common Reference Struct
///
/// This struct is a global variable for the proving system and holds values used in the commitment schemes
///
/// # Tuple entries
/// * `0`: Seq<G1> ∈ Gᵈ (vector of random elems.)
/// * `1`: G1 in G (random group element)
type CRS = (Seq<G1>, G1);

/// A term in a multivariate polynomial
///
/// # Tuple entries
/// * `0`: - The first entry represents the coefficient for the term.
/// * `1`: - The second entry, a sequence of `u32`s, represent the powers
///        for each variable, s.t. the i'th variabe is raised to the power
///        of the i'th entry in the sequence.
type Term = (Fp, Seq<u32>);

/// A representation of input variable in multivariate polynomial
///
/// # Tuple entries
/// * `0`: - The first entry determines whether this variable should be evaluated or not.
///        This is useful for only evaluating some variables in a multivariate polynomial.
/// * `1`: - The second entry is the actual (inputted) value for the variable
type InputVar = (bool, Fp);

fn halo2() {
    // step 1
    // dummy values
    let a: Seq<Seq<Term>> = Seq::<Seq<Term>>::create(0);
    let crs: CRS = (Seq::<G1>::create(0), g1_default());
    let r = Fp::default();

    for j in 0..a.len() {
        let aj = a[j].clone();
        let aj_prime = multi_to_uni_poly(aj.clone(), Seq::<InputVar>::create(0)); // dummy inputs
        let cAj = commit_polyx(&crs, aj_prime, r);
        // generate challenge cj
    }

    // step 2
    // dummy values
    let g: Seq<Term> = Seq::<Term>::create(0);

    let g_prime = multi_to_uni_poly(g.clone(), Seq::<InputVar>::create(0)); // dummy inputs

    // step 3
    //g_prime is not randomly sampled
    let cR = commit_polyx(&crs, g_prime, r); // TODO update r?
}

/// Add two polynomials, return resulting polynomial
///
/// # Arguments
///
/// * `p1` - the LHS polynomial
/// * `p2` - the RHS polynomial
fn add_polyx(p1: Seq<Fp>, p2: Seq<Fp>) -> Seq<Fp> {
    let mut res = Seq::<Fp>::create(0);
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

    trim_poly(res)
}

/// Subtract two polynomials, return resulting polynomial
///
/// # Arguments
///
/// * `p1` - the LHS polynomial
/// * `p2` - the RHS polynomial
fn sub_polyx(p1: Seq<Fp>, p2: Seq<Fp>) -> Seq<Fp> {
    let mut largest = p1.len();
    if p2.len() > p1.len() {
        largest = p2.len();
    }

    let mut res = Seq::<Fp>::create(largest);
    for i in 0..p1.len() {
        res[i] = p1[i];
    }

    for i in 0..p2.len() {
        res[i] = res[i] - p2[i];
    }

    trim_poly(res)
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
fn mul_polyx(a: Seq<Fp>, b: Seq<Fp>) -> Seq<Fp> {
    let mut result = Seq::<Fp>::create(a.len() + b.len());
    for i in 0..a.len() {
        if !a[i].equal(Fp::default()) {
            for j in 0..b.len() {
                if !b[j].equal(Fp::default()) {
                    result[i + j] = (result[i + j].add(a[i] * b[j]));
                }
            }
        }
    }
    result
}

/// Multiply a polynomial by a scalar, return resulting polynomial
///
/// # Arguments
///
/// * `p` - the polynomial
/// * `s` - the scalar
fn mul_scalar_polyx(p: Seq<Fp>, s: Fp) -> Seq<Fp> {
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
fn add_scalar_polyx(p: Seq<Fp>, s: Fp) -> Seq<Fp> {
    let mut res = p.clone();
    if res.len() == 0 {
        // if poly empty, initialize res to zero constant term
        res = Seq::<Fp>::create(1);
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
fn sub_scalar_polyx(p: Seq<Fp>, s: Fp) -> Seq<Fp> {
    let mut res = p.clone();
    if res.len() == 0 {
        // if poly empty, initialize res to zero constant term
        res = Seq::<Fp>::create(1);
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
fn eval_polyx(p: Seq<Fp>, x: Fp) -> Fp {
    let mut res = Fp::ZERO();

    for i in 0..p.len() {
        res = res + p[i] * x.exp(i as u32);
    }

    res
}

fn rotate_polyx(p: Seq<Fp>, rotation: Fp, n: u128) -> Seq<Fp> {
    let mut res = p;
    for i in 0..res.len() {
        let coef = res[i];
        let rot = rotation.pow((i as u128).modulo(n));
        res[i] = coef * rot;
    }

    res
}

/// Get the degree of a polynomial
///
/// # Arguments
///
/// * `p` - the polynomial
fn poly_degree(p: Seq<Fp>) -> u128 {
    let len = trim_poly(p).len();
    if len == 0 {
        0
    } else {
        (len as u128) - (1 as u128)
    }
}

/// Checks if all entries in a polynomial is 0
/// # Arguments
/// * `p` the polynomial to be checked
/// # Returns
/// * `true` if polynomial is NOT all 0
/// * `false`if polynomial IS all 0
fn check_not_zero(p: Seq<Fp>) -> bool {
    let mut sum = Fp::ZERO();
    let mut all_zero = false;
    for i in 0..p.len() {
        if p[i] > Fp::ZERO() {
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
fn trim_poly(p: Seq<Fp>) -> Seq<Fp> {
    let mut last_val_idx = 0;
    for i in 0..p.len() {
        if p[i] != Fp::ZERO() {
            last_val_idx = i;
        }
    }
    let mut res = Seq::<Fp>::create(last_val_idx + 1);
    if p.len() != 0 {
        for i in 0..res.len() {
            res[i] = p[i];
        }
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
fn divide_leading_terms(n: Seq<Fp>, d: Seq<Fp>) -> Seq<Fp> {
    let n = trim_poly(n);
    let d = trim_poly(d);
    let x_pow = n.len() - d.len();
    let n_coeff = n[n.len() - 1];
    let d_coeff = d[d.len() - 1];
    // let coeff = n_coeff / d_coeff;
    let coeff = n_coeff / d_coeff;
    let mut res = Seq::<Fp>::create(x_pow + 1);
    res[x_pow] = coeff;

    res
}

/// Multiply a polynomial with a single term (e.g. 5x^3), with the single term represented as a
/// polynomial. Returns the product.
/// (helper function for divide_poly)
///
/// # Arguments
///
/// * `p` - the polynomial
/// * `single_term` - the single term polynomial
fn multiply_poly_by_single_term(p: Seq<Fp>, single_term: Seq<Fp>) -> Seq<Fp> {
    let single_term = trim_poly(single_term);
    let st_len = single_term.len() - 1;
    let coef = single_term[st_len];
    let mut res = Seq::<Fp>::create(p.len() + st_len);
    for i in st_len..res.len() {
        res[i] = p[i - st_len] * coef;
    }

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
fn divide_poly(n: Seq<Fp>, d: Seq<Fp>) -> (Seq<Fp>, Seq<Fp>) {
    let mut q = Seq::<Fp>::new(n.len());
    let mut r = n.clone();

    let mut loop_upper_bound = d.len();
    if q.len() > d.len() {
        loop_upper_bound = q.len();
    }
    for _ in 0..loop_upper_bound {
        if check_not_zero(r.clone()) && poly_degree(r.clone()) >= poly_degree(d.clone()) {
            let t = divide_leading_terms(r.clone(), d.clone());
            q = add_polyx(q, t.clone());
            let aux_prod = multiply_poly_by_single_term(d.clone(), t);
            r = sub_polyx(r, aux_prod);
        }
    }
    (trim_poly(q), trim_poly(r))
}

// TODO document
fn multi_poly_with_x(p: Seq<Fp>) -> Seq<Fp> {
    multi_poly_with_x_pow(p, 1 as usize)
}

// TODO document
fn multi_poly_with_x_pow(p: Seq<Fp>, power: usize) -> Seq<Fp> {
    let p = trim_poly(p);
    let mut res: Seq<Fp> = Seq::<Fp>::create(p.len() + power);

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
fn legrange_poly(points: Seq<(Fp, Fp)>) -> Seq<Fp> {
    let mut poly = Seq::<Fp>::create(points.len());

    for i in 0..points.len() {
        let x: Fp = points[i].0;
        let y: Fp = points[i].1;
        let basis = legrange_basis(points.clone(), x);
        let scaled_basis = mul_scalar_polyx(basis, y);
        poly = add_polyx(poly.clone(), scaled_basis.clone());
    }
    poly = trim_poly(poly);
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
fn legrange_basis(points: Seq<(Fp, Fp)>, x: Fp) -> Seq<Fp> {
    let mut basis = Seq::<Fp>::create(points.len());
    basis[0] = Fp::ONE();
    let mut devisor = Fp::ONE();
    for i in 0..points.len() {
        let point = points[i];
        let p_x = point.0;
        if p_x != x {
            devisor = devisor.mul(x.sub(p_x));
            let poly_mul_x = multi_poly_with_x(basis.clone());
            let poly_mul_scalar: Seq<Fp> = mul_scalar_polyx(basis.clone(), p_x.neg());
            basis = add_polyx(poly_mul_x, poly_mul_scalar);
        }
    }
    let test = eval_polyx(basis.clone(), Fp::ONE());
    let mut division_poly = Seq::<Fp>::create(points.len());
    division_poly[0] = devisor;

    let output = divide_poly(basis, division_poly);
    let (final_basis, _) = output;
    final_basis
}

// fn legrange_basis(points: Seq<(Fp, Fp)>, x: Fp) -> Seq<Fp> {
//         let mut basis = Seq::<Fp>::create(points.len());
//         basis[0] = Fp::ONE();
//         let mut devisor = Fp::ONE();
//         for i in 0..points.len() {
//                     let point = points[i];
//                     let p_x = point.0;
//                     if p_x != x {
//                         let poly_mul_x = multi_poly_with_x(basis.clone());
//                         let poly_mul_scalar: Seq<Fp> = mul_scalar_polyx(basis.clone(), p_x.neg());
//                         basis = mul_scalar_polyx(basis.clone(), Fp::ONE());
//                     }
//                 }
//         basis
//     }

/// Evaluate a term with specified variable inputs
/// Helper function for reduce_multi_poly
///
/// # Arguments
///
/// * `term` - the term
/// TODO, document inputs and new_size (is new_size needed?)
fn reduce_multi_term(term: &Term, inputs: Seq<InputVar>, new_size: usize) -> Term {
    let (coef, powers) = term;

    let mut new_coef = coef.clone(); //First entry in a term sequence is the Coefficient
    let mut new_powers = Seq::<u32>::create(new_size);

    let mut idx = 0;
    for i in 0..powers.len() {
        let power = powers[i];
        let input = inputs[i];

        let (b, p) = input;
        if b {
            let val = p.exp(power);
            new_coef = new_coef * val;
        } else {
            new_powers[idx] = power;
            idx = idx + 1;
        }
    }

    (new_coef, new_powers)
}

/// Evaluate a polynomial in some specified variables and return the new multivariate polynomial
///
/// The output is a new polynomial, with the evaluated variables removed. If all variables are
/// evaluated there will be a single term, with a coefficient (which is the final evaluation) and an
/// empty sequence of powers (i.e. no variables)
///
/// # Arguments
///
/// * `p` - the multivariate polynomial, expressed as a sequence of 2-tuples.
/// * `inputs` - values for the variables and bools indicating if the should be evaluated
///
/// Each tuple of `p` has the coefficient and a sequence of powers, where the i'th entry is the power of the i'th variable in this term
///
/// # Constraints
///
/// * The length of inputs and all sequences of powers in p1 should be equal
fn reduce_multi_poly(p: Seq<Term>, inputs: Seq<InputVar>) -> Seq<Term> {
    let mut constant = Fp::ZERO();
    let mut unevaluated_variables = 0;
    for i in 0..inputs.len() {
        let (b, _) = inputs[i];
        if !b {
            unevaluated_variables = unevaluated_variables + 1;
        }
    }
    let mut new_poly = Seq::<Term>::create(p.len());
    let mut terms_added = 0;
    if unevaluated_variables == 0 {
        //sum results
        for i in 0..p.len() {
            // let term = p[i].clone();
            let (coef, _) = reduce_multi_term(&p[i], inputs.clone(), unevaluated_variables);
            constant = constant + coef;
        }
    } else {
        //check if term can be evaluated, else insert term in new poly
        for i in 0..p.len() {
            // let term = p[i].clone();
            let (coef, powers) = reduce_multi_term(&p[i], inputs.clone(), unevaluated_variables);
            let mut all_powers_zero = true;
            for i in 0..powers.len() {
                if powers[i] != (0 as u32) {
                    all_powers_zero = false;
                }
            }
            if all_powers_zero {
                constant = constant + coef;
            } else {
                new_poly[terms_added] = (coef, powers);
                terms_added = terms_added + 1;
            }
        }
    }
    let constant_term = (constant, Seq::<u32>::new(unevaluated_variables));
    new_poly[terms_added] = constant_term;

    new_poly.slice(0, terms_added + 1)
}

/// Evaluate a multivariate polynomials and return the evaluation
///
/// # Arguments
///
/// * `p` - the polynomial, expressed as a sequence of 2-tuples.
/// * `inputs` - a sequence of field elements, where the i'th entry is the value for the i'th variable
///
/// Each tuple of `p` has the coefficient and a sequence of powers, where the i'th entry is the power of
/// the i'th variable in this term
///
/// # Constraints
///
/// * The length of inputs and all sequences of powers in p1 should be equal
fn eval_multi_poly(p: Seq<Term>, inputs: Seq<Fp>) -> Fp {
    let mut inputvars = Seq::<InputVar>::create(inputs.len());
    for i in 0..inputs.len() {
        inputvars[i] = (true, inputs[i]);
    }
    let reduced = reduce_multi_poly(p, inputvars);
    let (res, _) = reduced[0];

    res
}

/// Pedersen vector commitment (1.3 in protocol)
///
/// # Arguments
///
/// * `crs` - the common reference string
/// * `a` - the "vector"
/// * `blinding` - blinding factor
fn commit_polyx(crs: &CRS, a: Seq<Fp>, blinding: Fp) -> G1 {
    let (G, W) = crs;
    // let (f1, f2, b) = h;

    let lhs: G1 = msm(a, G.clone());
    let rhs: G1 = g1mul(blinding, W.clone());
    let res: G1 = g1add(lhs, rhs);

    res
}

/// Evaluate a multivariate polynomial in variables such that it becomes a univariate polynomial (1.1 in protocol)
/// (univaraite polynomial represented as a sequence of field elements, where entry i, has
/// degree i in the variable and the coefficient is the entry)
///
/// # Arguments
///
/// * `p` - the multivariate polynomial, expressed as a sequence of 2-tuples.
/// * `inputs` - values for the variables and bools indicating if the should be evaluated
///
/// Each tuple of `p` has the coefficient and a sequence of powers, where the i'th entry is the power of the i'th variable in this term
///
/// # Constraints
///
/// * The length of inputs and all sequences of powers in p1 should be equal
/// * Exactly one variable should remain unevaluated_variables
fn multi_to_uni_poly(p: Seq<Term>, inputs: Seq<InputVar>) -> Seq<Fp> {
    // the univariate polynomial, in mutlivariate representation
    let reduced_poly = reduce_multi_poly(p.clone(), inputs);

    // get the highest degree, or 0 (default) if empty
    let mut max_deg = 0;
    for i in 0..reduced_poly.len() {
        let term = reduced_poly[i].clone();
        let powers = term.1;
        let cur_deg = powers[0] as usize;
        if cur_deg > max_deg {
            max_deg = cur_deg;
        }
    }

    let mut s = Seq::<Fp>::create(max_deg + 1);

    for i in 0..max_deg + 1 {
        // sum the coefficients of terms with same degree (in "x")
        let mut coeff_sum = Fp::ZERO();
        for j in 0..reduced_poly.len() {
            let mut coeff = Fp::ZERO();
            let poly_clone = reduced_poly.clone();
            let powers = poly_clone[j].1.clone();
            let f = poly_clone[j].0.clone();
            let power = powers[0];
            if power == (i as u32) {
                coeff = f.clone();
            }
            coeff_sum = coeff_sum + coeff;
        }

        // set the term with degree i to the corresponding coefficient
        s[i] = coeff_sum;
    }

    s
}

/// Inner product, between to equal length vectors of field elements
///
/// # Arguments
///
/// * `u` - LHS vector
/// * `v` - RHS vector
fn inner_product(u: Seq<Fp>, v: Seq<Fp>) -> Fp {
    let mut res = Fp::ZERO();
    for i in 0..u.len() {
        res = res + u[i] * v[i];
    }

    res
}

/// Multiscalar multiplicatoin, auxiliary function for Pedersen vector commitment
///
/// # Arguments
///
/// * `a` - sequence of scalars (LHS)
/// * `g` - sequence of group (curve) elements (RHS)
fn msm(a: Seq<Fp>, g: Seq<G1>) -> G1 {
    let mut res = g1mul(a[0], g[0]);
    for i in 1..a.len() {
        res = g1add(res, g1mul(a[i], g[i]));
    }

    res
}
/// Compute vanishing polynomial over n-order multiplicative subgroup H with root of unity omega
///
/// # Arguments
/// * `omega` - root of unity for the H
/// * `n` - the order of the group
fn compute_vanishing_polynomial(omega: Fp, n: u128) -> Seq<Fp> {
    println!("compute vanishing");
    println!("{:?}", n);

    let mut vanishing_poly = Seq::<Fp>::create((n - 1 as u128) as usize);
    vanishing_poly[0] = Fp::ONE();
    for i in 0..n as usize - 1 {
        let eval_point = omega.pow(i as u128);
        let poly_mul_x = multi_poly_with_x(vanishing_poly.clone());
        let poly_mul_scalar: Seq<Fp> = mul_scalar_polyx(vanishing_poly.clone(), eval_point.neg());
        vanishing_poly = add_polyx(poly_mul_x, poly_mul_scalar);
    }
    vanishing_poly
}

/// Compute the h(x) polynomial, used in step 4 and 13
///
/// # Arguments
///
/// * `g_prime` the univariate polynomial calculated in step 2 and 13
fn compute_h(g_prime: Seq<Fp>) -> Seq<Fp> {
    // TODO create the real vanishing polynomial
    let t = Seq::<Fp>::create(0);

    let (h, remainder) = divide_poly(g_prime, t);
    // TODO what to do with remainder?

    h
}

/// Implementation of the σ mapping from the protocol
///
/// # Arguments
/// * `i` - the i in σ(i)
/// * `sigma_list` - s.t. q[sigma_list[i]]=p_i (indexing/mapping into q, for p_i)
/// * `q` - q, from the protocol represented
fn sigma(i: u128, sigma_list: Seq<u128>, q: Seq<Seq<u128>>) -> Seq<u128> {
    let idx = sigma_list[i as usize];
    q[idx as usize].clone()
}

/// Auxilary function for computing L_j or R_j in step 24
///
/// # Arguments
/// * `p_part` - $p'_{hi}$ for L or  $p'_{lo}$ for R
/// * `b_part` - $b_{lo}$ for L or  $b_{hi}$ for R
/// * `g_part` - $g'_{lo}$ for L or  $g'_{hi}$ for R
/// * `z` - the challenge z from step 21
/// * `U` - group element U from pp
/// * `W` - group element W from pp
fn calculate_L_or_R(
    p_part: Seq<Fp>,
    b_part: Seq<Fp>,
    g_part: Seq<G1>,
    z: Fp,
    U: G1,
    W: G1,
    blinding: Fp,
) -> G1 {
    // <p'_part, G'_part>
    let p_g_msm: G1 = msm(p_part.clone(), g_part);

    let p_b_ip: Fp = inner_product(p_part, b_part);
    let z_ip: Fp = z * p_b_ip;
    // [z<p'_part, b_part>]U
    let z_ip_U: G1 = g1mul(z_ip, U);

    // [*]W
    let multed_W: G1 = g1mul(blinding, W);

    // calculate part j (L_j or R_j)
    let mut part_j: G1 = g1add(p_g_msm, z_ip_U);
    part_j = g1add(part_j, multed_W);

    part_j
}
fn step_1() {}
fn step_2() {}
fn step_3() {}
/// Step 4
/// Beginning of the vanishing argument
///
/// # Arguments
/// * `g_prime` - polynomial from step 2
/// * `omega` - a n=2ˆk root of unity (global variable)
/// * `n` - n=2ˆk (global variable)
fn step_4(g_prime: Seq<Fp>, omega: Fp, n: u128) -> Seq<Fp> {
    let vanishing = compute_vanishing_polynomial(omega, n);

    let (h, remainder) = divide_poly(g_prime, vanishing);

    h
}

/// Step 5
/// split polynomial of degree n_g(n-1)-n up into n_(g-2) polynomials of degree at most n-1
///
/// The polynomials(represented by vectors) are stored in a vectore.
/// This way the index in the outer vector can act as the i when reproducing the original poly:
/// h(X) = SUM from i=0 to n_(g-1) [xˆ(ni)h_i(x)]
/// Where n is a parameter of the prooving system, and h_i is the ith part of the original poly.
///
/// # Arguments
/// * `h` - Polynomial to be split
/// * `n` - defines length of new polynomials (global variable for prooving system)
fn step_5(h: Seq<Fp>, n: u128) -> Seq<Seq<Fp>> {
    let h = trim_poly(h);
    let no_of_parts = (h.len() + (n - (2 as u128)) as usize) / ((n - (1 as u128)) as usize);
    let n = n as usize;

    let mut original_index = 0;
    let mut poly_parts: Seq<Seq<Fp>> = Seq::<Seq<Fp>>::create(no_of_parts);
    for i in 0..poly_parts.len() {
        let mut current_poly_part: Seq<Fp> = Seq::<Fp>::create(n);
        for j in 0..n {
            if original_index < h.len() {
                current_poly_part[j] = h[original_index];
                original_index = original_index + 1;
            }
        }
        poly_parts[i] = current_poly_part;
    }
    poly_parts
}

/// Step 6
///
/// commit to each h_i polynomial keeping them in the seq to peserve the power (i)
///
/// # Arguments
/// * `poly_parts` - A sequence of polynomials to be commited to
/// * `crs` - Commen Refernce Struct (Global variable for prooving system)
/// * `r_seq` - Sequence of random elements used as blinding factors
///
/// # Constraints
/// * `r_seq` should be at least as long as the `poly_parts`
fn step_6(poly_parts: Seq<Seq<Fp>>, crs: &CRS, r_seq: Seq<Fp>) -> Seq<G1> {
    let mut commitment_seq: Seq<G1> = Seq::<G1>::create(poly_parts.len());
    for i in 0..poly_parts.len() {
        let commitment = commit_polyx(crs, poly_parts[i].clone(), r_seq[i]);
        commitment_seq[i] = commitment;
    }
    commitment_seq
}
/// Step 7
/// Computes the sum from step 7 in the protocol description
///
/// # Arguments
/// * `commitment_seq` - is a sequence of commitments
/// * `x`is - the challenge each commitment should be multiplied with
/// * `n` - Global parameter for the prooving system
fn step_7(commitment_seq: Seq<G1>, x: Fp, n: u128) -> G1 {
    let mut result: G1 = g1_default();
    for i in 0..commitment_seq.len() {
        let power: u128 = n * i as u128;
        let x_raised = x.pow(power);
        let intemidiate: G1 = g1mul(x_raised, commitment_seq[i]);
        result = g1add(result, intemidiate);
    }
    result
}

/// Step 8
/// This functions calculates h'(X) from the h_i parts created in step 5 and the challenge x
///
/// # Arguments
/// * `h_parts` - Sequence of the h_i parts from step 5
/// * `x` - the challenge from step 5
/// * `n` - n from the protocol
fn step_8(h_parts: Seq<Seq<Fp>>, x: Fp, n: u128) -> Seq<Fp> {
    let mut res = Seq::<Fp>::create((n - (1 as u128)) as usize);
    for i in 0..h_parts.len() {
        let ni_prod = n * (i as u128);
        let x_raised = x.pow(ni_prod as u128);
        let h_i = h_parts[i].clone();
        let aux_prod = mul_scalar_polyx(h_i, x_raised);
        res = add_polyx(res, aux_prod)
    }

    res
}

/// Step 9
/// This functions returns r(x) and creates a seq filled with a_i from the second part of step 9
///
/// # Arguments
/// * `r` - the polynomial from step 3
/// * `a_prime_seq` - A sequence of the a' polynomials from step 1
/// * `n_a` - Global parameter for the protocol
/// * `omega` - The generator for the evaluations points also a global parameter for the protocol
/// * `p` - a list of sets p_i which contains integers from the protocol
/// * `x` - The challenge from step 7
///
///
fn step_9(
    r: Seq<Fp>,
    a_prime_seq: Seq<Seq<Fp>>,
    n_a: usize,
    omega: Fp,
    p: Seq<Seq<u128>>,
    x: Fp,
) -> (Fp, Seq<Seq<Fp>>) {
    let mut a_seq: Seq<Seq<Fp>> = Seq::<Seq<Fp>>::create(n_a);
    let mut i_range: usize = n_a - 1;
    if i_range > p.len() {
        i_range = p.len();
    }
    for i in 0..i_range {
        let p_i: Seq<u128> = p[i].clone();
        let n_e = p_i.len();
        let a_prime_i: Seq<Fp> = a_prime_seq[i].clone();
        let mut a_i_seq: Seq<Fp> = Seq::<Fp>::create(n_e);
        let mut j_range: usize = n_e;
        // if j_range > p_i.len() {
        //     j_range = p_i.len();
        // }
        for j in 0..j_range {
            let p_i_j: u128 = p_i[j];
            let argument: Fp = omega.pow(p_i_j).mul(x);
            let a_i_j: Fp = eval_polyx(a_prime_i.clone(), argument);
            a_i_seq[j] = a_i_j;
        }
        a_seq[i] = a_i_seq;
    }
    let r_x = eval_polyx(r, x);
    (r_x, a_seq)
}
/// Step 10
/// This functions initializes the s sequence of length n_a and fills it with polynomials of degree n_e-1 made with legrange interpolation
///
/// # Arguments
/// * `omega` - omega from the protocol
/// * `x` - the challenge from step 7
/// * `a` - the sequence of sequences from step 9
/// * `n_a` - n_a from the protocol
///
fn step_10(omega: Fp, p: Seq<Seq<u128>>, x: Fp, a: Seq<Seq<Fp>>, n_a: u128) -> Seq<Seq<Fp>> {
    let mut s = Seq::<Seq<Fp>>::create(n_a as usize);
    let mut i_range: usize = n_a as usize - 1;
    if i_range > p.len() {
        i_range = p.len();
    }
    for i in 0..i_range as usize {
        let a_i = a[i as usize].clone();

        let p_i = p[i].clone();
        let n_e = p_i.len();

        let mut j_range: usize = n_e;
        // if j_range > p_i.len() {
        //     j_range = p_i.len();
        // }
        let mut points: Seq<(Fp, Fp)> = Seq::<(Fp, Fp)>::create((n_e));
        for j in 0..j_range {
            let p_i_j: u128 = p_i[j];
            let x_j = omega.pow(p_i_j) * x;
            let y_j = a_i[j as usize];
            points[j as usize] = (x_j, y_j);
        }
        let s_i: Seq<Fp> = legrange_poly(points);
        s[i as usize] = s_i
    }

    s
}

/// Step 11
/// Get the list of Q's (Q_0, ..., Q_{n_q - 1})
///
/// # Arguments
/// * `n_a` - n_a from the protocol
/// * `x1` - challenge 1
/// * `H_prime` - H', the computed sum from step 7
/// * `R` - R, commitment from step 3
/// * `a` - A, the list of hiding commitments for a_i's
/// * `q` - q, from the protocol
/// * `sigma_list` - s.t. q[sigma_list[i]]=p_i (indexing/mapping into q, for p_i)
fn step_11(
    n_a: u128,
    x1: Fp,
    H_prime: G1,
    R: G1,
    a: Seq<G1>,
    q: Seq<Seq<u128>>,
    sigma_list: Seq<u128>,
) -> Seq<G1> {
    let n_q = q.len();
    let mut qs = Seq::<G1>::create(n_q as usize);
    for i in 0..qs.len() {
        qs[i] = g1_default();
    }

    // bullet 1
    for i in 0..(n_a as usize) {
        let a_i = a[i as usize];
        // TODO is this what is meant by Q_sigma(i) ?
        let sigma_i = sigma(i as u128, sigma_list.clone(), q.clone());
        for k in 0..sigma_i.len() {
            let j = sigma_i[k];
            let q_sigma_i = qs[j as usize];
            let product = g1mul(x1, q_sigma_i);
            qs[j as usize] = g1add(product, a_i);
        }
    }

    // bullet 2
    let x1_squared = x1 * x1;
    let q0 = qs[0];
    let product1 = g1mul(x1_squared, q0);
    let product2 = g1mul(x1, H_prime);
    let sum1 = g1add(product1, product2);
    let final_sum = g1add(sum1, R);
    qs[0] = final_sum;

    qs
}

/// Step 12
/// Get the list of q's (q_0, ..., q_{n_q - 1})
///
/// # Arguments
/// * `n_a` - n_a from the protocol
/// * `x1` - challenge 1
/// * `h_prime` - h', the computed polynomial from [step_8]
/// * `r` - the "random" polynomial from [step_3]
/// * `a_prime` - a', the list of univariate polys from [step_1]
/// * `q` - q, from the protocol
/// * `sigma_list` - s.t. q[sigma_list[i]]=p_i (indexing/mapping into q, for p_i)
fn step_12(
    n_a: u128,
    x1: Fp,
    h_prime: Seq<Fp>,
    r: Seq<Fp>,
    a_prime: Seq<Seq<Fp>>,
    q: Seq<Seq<u128>>,
    sigma_list: Seq<u128>,
) -> Seq<Seq<Fp>> {
    let n_q = q.len();

    let mut qs = Seq::<Seq<Fp>>::create(n_q as usize);

    // initialize all polys to constant 0
    for i in 0..qs.len() {
        qs[i] = Seq::<Fp>::create(1);
    }

    // bullet 1
    for i in 0..(n_a as usize) {
        let a_i = a_prime[i as usize].clone();
        let sigma_i = sigma(i as u128, sigma_list.clone(), q.clone());
        // TODO is this what is meant by Q_sigma(i) ?
        for j in 0..sigma_i.len() {
            let j = sigma_i[j];
            let q_sigma_i = qs[j as usize].clone();
            let product = mul_scalar_polyx(q_sigma_i.clone(), x1);
            qs[j as usize] = add_polyx(product, a_i.clone());
        }
    }

    // bullet 2
    let x1_squared = x1 * x1;
    let q0 = qs[0 as usize].clone();
    let product1 = mul_scalar_polyx(q0, x1_squared);
    let product2 = mul_scalar_polyx(h_prime, x1);
    let sum1 = add_polyx(product1, product2);
    let final_sum = add_polyx(sum1, r);
    qs[0] = final_sum;

    qs
}

/// Step 13
/// Get the list of r's (r_0, ..., r_{n_q - 1})
///
/// # Arguments
/// * `n_a` - n_a from the protocol
/// * `n` - n from the protocol
/// * `omega` - omega from the protocol
/// * `x` - the challenge from step 7
/// * `x1` - the challenge from step 11
/// * `r` - r from step 9
/// * `s` - s, the computed polynomials from step 10
/// * `q` - q, from the protocol
/// * `sigma_list` - s.t. q[sigma_list[i]]=p_i (indexing/mapping into q, for p_i)
/// * `a` - a', the list of univariate polys from step 1
/// * `g_prime` - the polynomial from step 2
fn step_13(
    n_a: u128,
    n: u128,
    omega: Fp,
    x: Fp,
    x1: Fp,
    r: Fp,
    s: Seq<Seq<Fp>>,
    q: Seq<Seq<u128>>,
    sigma_list: Seq<u128>,
    a: Seq<Seq<Fp>>,
    g_prime: Seq<Fp>,
) -> Seq<Seq<Fp>> {
    let n_q = q.len();
    let mut rs = Seq::<Seq<Fp>>::create(n_q as usize);

    // initialize all polys to constant 0
    for i in 0..rs.len() {
        rs[i] = Seq::<Fp>::create(1);
    }

    // bullet 1
    for i in 0..(n_a as usize) {
        let s_i = s[i as usize].clone();
        let sigma_i = sigma(i as u128, sigma_list.clone(), q.clone());
        for j in 0..sigma_i.len() {
            let j = sigma_i[j];
            let r_sigma_i = rs[j as usize].clone();
            let product = mul_scalar_polyx(r_sigma_i.clone(), x1);
            rs[j as usize] = add_polyx(product, s_i.clone());
        }
    }

    // bullet 2
    let g_prime_x: Fp = eval_polyx(g_prime, x);
    let vanishing_poly: Seq<Fp> = compute_vanishing_polynomial(omega, n);
    let vanishing_poly_x: Fp = eval_polyx(vanishing_poly, x);
    let h = g_prime_x / vanishing_poly_x;
    let x1_squared: Fp = x1 * x1;
    let r0: Seq<Fp> = rs[0 as usize].clone();
    let product1 = mul_scalar_polyx(r0, x1_squared);
    let product2 = h * x1;
    let sum1 = add_scalar_polyx(product1, product2);
    let final_sum = add_scalar_polyx(sum1, r);
    rs[0] = final_sum;

    rs
}

/// Step 14
/// Get the commitment Q'
///
/// # Arguments
/// * `crs` - the common reference string
/// * `x2` - the challenge from step 11
/// * `q_polys` - the q polynomials from step 12
/// * `r_polys` - the r polynomials from step 13
/// * `q` - q, from the protocol
/// * `sigma_list` - s.t. q[sigma_list[i]]=p_i (indexing/mapping into q, for p_i)
/// * `r` - randomness for commiting
fn step_14(
    crs: &CRS,
    x2: Fp,
    q_polys: Seq<Seq<Fp>>,
    r_polys: Seq<Seq<Fp>>,
    q: Seq<Seq<u128>>,
    sigma_list: Seq<u128>,
    blinding: Fp,
    omega: Fp,
    x: Fp,
) -> G1 {
    let mut q_prime = Seq::<Fp>::create(1); // initialize q' to the constant zero poly
    let n_q = q.len();
    for i in 0..(n_q as usize) {
        let x2_powered = x2.pow(i as u128);
        let q_i = q_polys[i].clone();
        let r_i = r_polys[i].clone();
        let q_i_sub_r_i = sub_polyx(q_i, r_i);
        let q_i: Seq<u128> = sigma(i as u128, sigma_list.clone(), q.clone());
        let mut divisor: Seq<Fp> = Seq::<Fp>::create(q_i.len() + 1 as usize);
        divisor[0] = Fp::ONE();

        for j in 0..(q_i.len()) {
            let q_i_j = q_i[j];
            let scalar = omega.pow(q_i_j).mul(x);
            let divisor_mul_x = multi_poly_with_x(divisor.clone());
            let divisor_mul_scalar = mul_scalar_polyx(divisor.clone(), scalar.neg());
            divisor = add_polyx(divisor_mul_x, divisor_mul_scalar);
        }

        let (divided_poly, remainder) = divide_poly(q_i_sub_r_i.clone(), divisor); // TODO what to do with remainder?

        let multed_poly = mul_scalar_polyx(divided_poly, x2_powered);

        q_prime = add_polyx(q_prime, multed_poly);
    }
    let commitment = commit_polyx(crs, q_prime, blinding);

    commitment
}
/// This function emulates sending a challenge.
/// It takes a challenge and returns it again.
///
/// # Arguments
///  * `x_3` - the challenge to be send
///
fn step_15(x_3: Fp) -> Fp {
    x_3
}

/// Step 16
/// Get the u ∈ F^{n_q} vector
///
/// # Arguments
/// * `n_q` - n_q from the protocol
/// * `x3` - the challenge from step 15
/// * `q_polys` - the q polynomials from step 12
fn step_16(n_q: u128, x3: Fp, q_polys: Seq<Seq<Fp>>) -> Seq<Fp> {
    let mut u = Seq::<Fp>::create(n_q as usize);
    for i in 0..(n_q as usize) {
        let q_i = q_polys[i].clone();
        let u_i = eval_polyx(q_i, x3);
        u[i] = u_i;
    }

    u
}

/// This function emulates sending a challenge.
/// It takes a challenge and returns it again.
///
/// # Arguments
///  * `x_4` - the challenge to be send
///
fn step_17(x_4: Fp) -> Fp {
    x_4
}
///
///
/// # Arguments
/// * `x` - challenge from step 7
/// * `x1` - challenge from step 11
/// * `x2` - challenge from step 11
/// * `x3` - challenge from step 15
/// * `x4` - challenge from step 17
/// * `n_q` -  n_q from the protocol
/// * `omega` - omega from the protocol
/// * `Q_prime` - commitment from step 14
/// * `Q` - list of group-elements from step 11
/// * `u` - list of scalars from step 16
/// * `r` - list of polynomials from step 13
/// * `q` - q, from the protocol
/// * `sigma_list` - s.t. q[sigma_list[i]]=p_i (indexing/mapping into q, for p_i)
fn step_18(
    x: Fp,
    x1: Fp,
    x2: Fp,
    x3: Fp,
    x4: Fp,
    omega: Fp,
    Q_prime: G1,
    Q: Seq<G1>,
    u: Seq<Fp>,
    r: Seq<Seq<Fp>>,
    q: Seq<Seq<u128>>,
    sigma_list: Seq<u128>,
) -> (G1, Fp) {
    let n_q = q.len();
    let v = Fp::ZERO();

    let mut P_sum = g1_default();
    for i in 0..n_q {
        let Q_i = Q[i];
        let term = g1mul(x4.pow(i as u128), Q_i);
        P_sum = g1add(P_sum, term)
    }
    P_sum = g1mul(x4, P_sum);
    let P = g1add(Q_prime, P_sum);

    let mut v_first_sum = Fp::ZERO();
    for i in 0..n_q as usize {
        let q_i: Seq<u128> = sigma(i as u128, sigma_list.clone(), q.clone());
        let n_e = q_i.len();
        let x2_i: Fp = x2.pow(i as u128);
        let u_i: Fp = u[i];
        let r_i: Seq<Fp> = r[i].clone();
        let r_i_x3: Fp = eval_polyx(r_i, x3);
        let numerator: Fp = u_i - r_i_x3;
        let mut product: Fp = Fp::ONE();
        for j in 0..n_e {
            let q_i_j: u128 = q_i[j];
            let rhs = omega.pow(q_i_j) * x;
            let term = x3 - rhs;
            product = product * term;
        }
        let sum_term: Fp = x2.pow(i as u128) * (numerator / product);

        v_first_sum = v_first_sum + sum_term;
    }

    let mut v_second_sum: Fp = Fp::ZERO();
    for i in 0..n_q {
        let u_i: Fp = u[i];
        let term: Fp = x4 * u_i;
        v_second_sum = v_second_sum + term;
    }
    let v = v_first_sum + x4 * v_second_sum;
    (P, v)
}

/// Step 19
/// Get the p(X) polynomial
///
/// # Arguments
/// * `x4` - the challenge from step 17
/// * `q_prime` - the q' polynomial computed by the prover in step 14
/// * `q_polys` - the q polynomials from step 12
fn step_19(x4: Fp, q_prime: Seq<Fp>, q_polys: Seq<Seq<Fp>>) -> Seq<Fp> {
    let mut p = Seq::<Fp>::create(1); // initialize p to the constant zero poly
    let n_q: usize = q_polys.len();

    //  Sum_i^nq-1 {x4^(n_q-1-i) q_i(X)}
    for i in 0..n_q {
        let power: u128 = (n_q - 1 - i) as u128;
        let x4_powered = x4.pow(power as u128);
        let q_i = q_polys[i].clone();
        let multed_poly = mul_scalar_polyx(q_i, x4_powered);

        p = add_polyx(p, multed_poly)
    }

    // q'(X) + [x4] Sum_i^nq-1 {x4^i q_i(X)}
    let x4n_q: Fp = x4.pow(n_q as u128);
    let first_term: Seq<Fp> = mul_scalar_polyx(q_prime, x4n_q);
    p = add_polyx(p, first_term);

    p
}

/// Step 20
///
/// Get the commitment S
///
/// # Arguments
/// * `s` - a randomly sampled poly (degree n-1) with a root at x3 from [step_15]
/// * `crs` - the common reference string
/// * `r` - randomness for commiting
fn step_20(s: Seq<Fp>, crs: CRS, r: Fp) -> G1 {
    let S = commit_polyx(&crs, s, r);
    S
}

/// Step 21
///
/// Get the xi and z challenges. They have to be fed into hacspec, since there is no randomness.
///
/// # Arguments
/// * `xi` - the ξ challenge
/// * `z` - the z challenge
fn step_21(xi: Fp, z: Fp) -> (Fp, Fp) {
    (xi, z)
}

/// Step 22
/// Get the P' curve-point/group-element
///
/// # Arguments
/// * `p` - the group element from step 18
/// * `g0` - the group element at index zero in **G** from pp
/// * `s` - the group element/commitment from step 20
/// * `v` - v as calculated in step 18
/// * `xi` - the ξ challenge from step 21
fn step_22(p: G1, g0: G1, s: G1, v: Fp, xi: Fp) -> G1 {
    let prod1 = g1mul(v, g0);
    let prod1_neg = g1neg(prod1);
    let prod2 = g1mul(xi, s);
    let lhs_sum = g1add(p, prod1_neg);
    let p_prime = g1add(lhs_sum, prod2);
    p_prime
}

/// Step 23
/// Get the p'(X) polynomial
///
/// # Arguments
/// * `p` - the polynomial p from step 19
/// * `s` - the polynomial s from step 20
/// * `x3` - the challenge from step 15
/// * `xi` - the ξ challenge from step 21
fn step_23(p: Seq<Fp>, s: Seq<Fp>, x3: Fp, xi: Fp) -> Seq<Fp> {
    // TODO what happens if v does not correspond with v?
    let p_eval_x3 = eval_polyx(p.clone(), x3);
    let xi_mul_s = mul_scalar_polyx(s, xi);
    let mut p_prime = p;
    p_prime = sub_scalar_polyx(p_prime, p_eval_x3);
    p_prime = add_polyx(p_prime, xi_mul_s);

    p_prime
}

/// Step 24
///
/// Get **G**' abd **p**'
///
/// # Arguments
/// * `p_prime_poly` - the polynomial p'(X) from [step_23]
/// * `G` - the vector of group elems from public-params
/// * `x3` - the challenge from [step_15]
/// * `z` - the challenge from [step_21]
/// * `U` - the group elem U from public-params
/// * `W` - the group elem U from public-params
/// * `n` - n from the protocol preamble
/// * `k` - k from the protocol preamble
/// * `u` - the list of u_j challenges from the verifier // TODO maybe should be interactive
///
/// # Returns
/// * `p_prime` - `Seq<Fp>`
/// * `G_prime` - `Seq<G1>`
/// * `L` - `Seq<G1>` the sequence of all `L_j`
/// * `R` - `Seq<G1>` the sequence of all `R_j`
fn step_24(
    p_prime_poly: Seq<Fp>,
    G: Seq<G1>,
    x3: Fp,
    z: Fp,
    U: G1,
    W: G1,
    n: u128,
    k: usize,
    u: Seq<Fp>,
    L_blinding: Seq<Fp>,
    R_blinding: Seq<Fp>,
) -> (Seq<Fp>, Seq<G1>, Seq<G1>, Seq<G1>) {
    let mut p_prime: Seq<Fp> = p_prime_poly;
    let mut g_prime: Seq<G1> = G;
    let mut b: Seq<Fp> = Seq::<Fp>::create(n as usize);
    let mut L: Seq<G1> = Seq::<G1>::create(k);
    let mut R: Seq<G1> = Seq::<G1>::create(k);

    for i in 0..b.len() {
        let x3_powered: Fp = x3.pow(i as u128);
        b[i] = x3_powered;
    }

    for j in 0..k {
        let p_prime_half: usize = p_prime.len() / 2;
        let g_prime_half: usize = g_prime.len() / 2;
        let b_half: usize = b.len() / 2;

        // BULLET 1
        // PROVER WORKS HERE
        let p_prime_lo: Seq<Fp> = p_prime.slice(0, p_prime_half);
        let p_prime_hi: Seq<Fp> = p_prime.slice(p_prime_half, p_prime_half);

        let g_prime_lo: Seq<G1> = g_prime.slice(0, g_prime_half);
        let g_prime_hi: Seq<G1> = g_prime.slice(g_prime_half, g_prime_half);

        let b_lo: Seq<Fp> = b.slice(0, b_half);
        let b_hi: Seq<Fp> = b.slice(b_half, b_half);

        // calcuate L_j and R_j, using the right parts of p', G' and b
        let L_j: G1 = calculate_L_or_R(
            p_prime_hi.clone(),
            b_lo.clone(),
            g_prime_lo.clone(),
            z,
            U,
            W,
            L_blinding[j],
        );
        L[j] = L_j;

        let R_j: G1 = calculate_L_or_R(
            p_prime_lo.clone(),
            b_hi.clone(),
            g_prime_hi.clone(),
            z,
            U,
            W,
            R_blinding[j],
        );
        R[j] = R_j;

        // BULLET 2
        // VERIFIER WORKS HERE
        let u_j: Fp = u[j];

        // BULLET 3
        // VERIFIER & PROVER WORKS HERE
        let mut new_g_prime: Seq<G1> = Seq::<G1>::create(g_prime_half);
        for i in 0..new_g_prime.len() {
            // TODO, this is entry-wise multiplication and pairwise addition!!!
            let g_prime_hi_indexed: G1 = g_prime_hi[i];
            let g_prime_lo_indexed: G1 = g_prime_lo[i];
            let rhs_product: G1 = g1mul(u_j, g_prime_hi_indexed);
            let sum: G1 = g1add(g_prime_lo_indexed, rhs_product);
            new_g_prime[i] = sum;
        }
        g_prime = new_g_prime;

        let rhs: Seq<Fp> = mul_scalar_polyx(b_hi.clone(), u_j);
        let new_b: Seq<Fp> = add_polyx(b_lo.clone(), rhs);
        b = new_b;
        // BULLET 4
        // PROVER WORKS HERE
        let u_j_inv: Fp = u_j.inv();
        let rhs: Seq<Fp> = mul_scalar_polyx(p_prime_hi.clone(), u_j_inv);
        let new_p_prime: Seq<Fp> = add_polyx(p_prime_lo.clone(), rhs);
        p_prime = new_p_prime;
    }

    (p_prime, g_prime, L, R)
}

/// Step 25
///
/// Get the zeroth entry in **p** and synthetic blinding factor f
///
/// # Arguments
/// * `p_prime` - **p**' from [step_24]
/// * `blinding_factors` - the list of all the elided blinding factors
fn step_25(
    p_prime: Seq<Fp>,
    L_blinding: Seq<Fp>,
    R_blinding: Seq<Fp>,
    s_blind: Fp,
    q_prime_blind: Fp,
    xi: Fp,
    u: Seq<Fp>,
) -> (Fp, Fp) {
    let p_prime_0 = p_prime[0];
    let mut f: Fp = q_prime_blind + (s_blind * xi);
    for j in 0..L_blinding.len() {
        let u_j: Fp = u[j];
        let u_j_inv: Fp = u_j.inv();
        let L_j_blinding: Fp = L_blinding[j];
        let R_j_blinding: Fp = R_blinding[j];
        f = f + L_j_blinding * u_j_inv;
        f = f + R_j_blinding * u_j;
    }

    (p_prime_0, f)
}

///Varifiers final check of the protocol
/// # Arguments
/// * `u` - Sequence of `u_j` from step 24
/// * `L` - Sequence of `L_j` from step 24
/// * `P_prime` -  from step 22
/// * `R` - Sequence of `R_j` from step 24
/// * `c` - from step 25
/// * `G_prime_0` - the first entry in the `G_prime` sequence from step 24
/// * `b_0` - the first entry in the `b` sequence from step 24
/// * `z` - the challenge from step 21
/// * `U` - from public parameters
/// * `f` - blinding factor from step 25
/// * `W` - from public parameters
///
fn step_26(
    u: Seq<Fp>,
    L: Seq<G1>,
    P_prime: G1,
    R: Seq<G1>,
    c: Fp,
    G_prime_0: G1,
    b_0: Fp,
    z: Fp,
    U: G1,
    f: Fp,
    W: G1,
) -> bool {
    let mut first_sum: G1 = (FpCurve::ZERO(), FpCurve::ZERO(), true);
    for j in 0..u.len() {
        let u_j_inv: Fp = u[j].inv();
        let L_j: G1 = L[j];
        let prod_j: G1 = g1mul(u_j_inv, L_j);
        first_sum = g1add(first_sum, prod_j);
    }

    let mut second_sum: G1 = (FpCurve::ZERO(), FpCurve::ZERO(), true);
    for j in 0..u.len() {
        let u_j: Fp = u[j];
        let R_j: G1 = R[j];
        let prod_j: G1 = g1mul(u_j, R_j);
        second_sum = g1add(second_sum, prod_j);
    }
    let lhs: G1 = g1add(first_sum, g1add(P_prime, second_sum));

    let rhs_term_1: G1 = g1mul(c, G_prime_0);

    let cb_0z: Fp = c * b_0 * z;

    let rhs_term_2: G1 = g1mul(cb_0z, U);

    let rhs_term_3: G1 = g1mul(f, W);

    let rhs: G1 = g1add(rhs_term_1, g1add(rhs_term_2, rhs_term_3));

    let check: bool = lhs == rhs;

    check
}

#[cfg(test)]
extern crate quickcheck;
#[cfg(test)]
#[macro_use(quickcheck)]
extern crate quickcheck_macros;
#[cfg(test)]
use quickcheck::*;

#[cfg(test)]
use rand::seq::SliceRandom;
#[cfg(test)]
use rand::thread_rng;

#[cfg(test)]
#[derive(Clone, Debug, Default)]
struct UniPolynomial(Seq<Fp>);

#[cfg(test)]
#[derive(Clone, Debug)]
struct SeqOfUniPoly(Seq<Seq<Fp>>);

#[cfg(test)]
#[derive(Clone, Debug)]
struct PorQ(Seq<Seq<u128>>);

#[cfg(test)]
impl Arbitrary for UniPolynomial {
    fn arbitrary(g: &mut quickcheck::Gen) -> UniPolynomial {
        let size = u8::arbitrary(g) % 20 + 1;
        let mut v: Vec<Fp> = vec![];
        for _ in 0..size {
            let new_val: Fp = Fp::from_literal(u8::arbitrary(g) as u128);
            v.push(new_val);
        }
        UniPolynomial(Seq::<Fp>::from_vec(v))
    }
}

#[cfg(test)]
impl Arbitrary for SeqOfUniPoly {
    fn arbitrary(g: &mut quickcheck::Gen) -> SeqOfUniPoly {
        let size = (u8::arbitrary(g) % 100 + 1); // min 1, max 100
        let mut seq_of_uni_poly = Seq::<Seq<Fp>>::create(size as usize);
        for i in 0..size {
            let uni_poly = (UniPolynomial::arbitrary(g));
            seq_of_uni_poly[i] = uni_poly.0
        }
        SeqOfUniPoly(seq_of_uni_poly)
    }
}

#[cfg(test)]
impl Arbitrary for PorQ {
    fn arbitrary(g: &mut quickcheck::Gen) -> PorQ {
        let size = u8::arbitrary(g) % 20;
        let mut p_or_q: Seq<Seq<u128>> = Seq::<Seq<u128>>::create(size as usize);
        for j in 0..size {
            let inner_size: u8 = u8::arbitrary(g) % 20 + 3;
            // let mut inner_seq = Seq::<u128>::create(inner_size as usize);
            let mut v: Vec<u128> = vec![];
            for i in 0..inner_size {
                let new_val: u128 = u128::arbitrary(g);
                if !v.contains(&new_val) {
                    v.push(new_val);
                }
                // inner_seq[i] = u128::arbitrary(g) % 10;
            }
            // let inner_seq: Seq<u128> =
            p_or_q[j] = Seq::<u128>::from_vec(v);
        }
        PorQ(p_or_q)
    }
}
#[cfg(test)]
#[derive(Clone, Debug)]
struct Points(Seq<(Fp, Fp)>);

#[cfg(test)]
impl Arbitrary for Points {
    fn arbitrary(g: &mut quickcheck::Gen) -> Points {
        let size = u8::arbitrary(g) % 20;
        let mut x_cords = vec![];
        let mut points = vec![];
        for _ in 0..size {
            let x: Fp = Fp::from_literal(u128::arbitrary(g) % 7);
            let y: Fp = Fp::from_literal(u128::arbitrary(g) % 7);
            if !x_cords.contains(&x) {
                points.push((x, y));
                x_cords.push(x)
            }
        }
        Points(Seq::<(Fp, Fp)>::from_vec(points))
    }
}

#[cfg(test)]
#[derive(Clone, Debug)]
pub struct G1Container(G1);

#[cfg(test)]
impl Arbitrary for G1Container {
    fn arbitrary(g: &mut Gen) -> G1Container {
        let a = Fp::from_literal(u128::arbitrary(g));
        let generator = g1_generator();
        G1Container(g1mul(a, generator))
    }
}

#[cfg(test)]
#[test]
fn test_step_4() {
    fn a(omega_value: u8, n: u8, r: u8) -> bool {
        let g_prime_degree = n as u128 + 5;

        let vanishing_poly_degree = n as u128 % g_prime_degree + 5;
        let mut r = r as u128;

        // r cannot be 0 as it would lead to g_prime being all 0
        if r == 0 {
            r = r + 2;
        }
        println!("{:?}", vanishing_poly_degree);
        println!("{:?}", g_prime_degree);
        println!("{:?}", r);

        let omega: Fp = Fp::from_literal((omega_value as u128) + 1);
        let g_prime = compute_vanishing_polynomial(omega, g_prime_degree as u128);
        let g_prime = mul_scalar_polyx(g_prime, Fp::from_literal(r));
        let h = step_4(g_prime, omega, vanishing_poly_degree);
        let h_degree = poly_degree(h);
        let expected_h_degree = g_prime_degree - vanishing_poly_degree;
        assert_eq!(h_degree, expected_h_degree);
        true
    }
    // limit the number of tests, since it is SLOW
    QuickCheck::new()
        .tests(5)
        .quickcheck(a as fn(omega_value: u8, n: u8, r: u8) -> bool);
}

#[cfg(test)]
#[quickcheck]
fn test_step_5(h: UniPolynomial, n: u8) -> TestResult {
    if n < 2 {
        // discard if n is too small (step_5 requires a n>2 to make sense)
        return TestResult::discard();
    }
    let n = n as u128;
    let h = h.0;
    let h = trim_poly(h); // extract polynomial
    let h_parts = step_5(h.clone(), n); // split the h poly
    let n = n as usize;

    let mut h_summed = Seq::<Fp>::create(1); // initialize a sum to the constant zero poly

    // h(x) = sum from 0 to n_g-2 (X^ni h_i(X))
    for i in 0..h_parts.len() {
        let hi = h_parts[i].clone();
        let n_times_i = n * i;
        let Xni_times_hi = multi_poly_with_x_pow(hi, n_times_i as usize);
        h_summed = add_polyx(h_summed, Xni_times_hi);
    }

    let h_summed = trim_poly(h_summed);

    // assert the original and the summed polys have same length
    let h_len = h.len();
    let h_summed_len = h_summed.len();
    assert_eq!(
        h_len, h_summed_len,
        "lengths of h and h_summed mismatch: {} and {}\n h: {:?}\nh_summed: {:?}",
        h_len, h_summed_len, h, h_summed
    );

    // assert pairwise equality
    for i in 0..h.len() {
        assert_eq!(h[i], h_summed[i]);
    }

    TestResult::passed()
}

// Generators taken from:
// https://o1-labs.github.io/proof-systems/specs/pasta.html#pallas
// (mina generator: (1,12418654782883325593414442427049395787963493412651469444558597405572177144507))
#[cfg(test)]
fn g1_generator() -> G1 {
    (
        FpCurve::from_hex("1"),
        FpCurve::from_hex("1B74B5A30A12937C53DFA9F06378EE548F655BD4333D477119CF7A23CAED2ABB"),
        false,
    )
}

// this hardcoded test for creating a real quickcheck test of step 5,6,7,8
#[cfg(test)]
#[quickcheck]
fn test_step_5_6_7_8_manual(x: u8, w: u8) -> bool {
    // h: UniPolynomial,
    // W_power: u8,
    // random_G_power: u8,
    // n: u8,
    // x: u8,
    // blinding: u8,

    // the original h poly
    let h: Seq<Fp> = Seq::<Fp>::from_vec(vec![
        Fp::from_literal(3),
        Fp::from_literal(7),
        Fp::from_literal(4),
        Fp::from_literal(10),
        Fp::from_literal(15),
        Fp::from_literal(35),
    ]);
    let n = 4;
    let x = Fp::from_literal(x as u128);
    let blinding = Fp::from_literal(345);
    let W = g1mul(Fp::from_literal(w as u128), g1_generator());
    // there should be as many G elements as there are elements in the h_i polys
    let G = Seq::<G1>::from_vec(vec![
        g1mul(Fp::ONE(), g1_generator()),
        g1mul(Fp::TWO(), g1_generator()),
        g1mul(Fp::from_literal(3), g1_generator()),
        g1mul(Fp::from_literal(4), g1_generator()),
    ]);
    // there should be as many random elements as there are h_i polys
    let randomness = Seq::<Fp>::from_vec(vec![Fp::ONE(), Fp::TWO()]);
    // let crs: CRS = (G, W);

    let h_s = step_5(h, n);
    let H_s = step_6(h_s.clone(), &(G.clone(), W), randomness.clone());
    let H_prime = step_7(H_s, x, n);
    let h_prime = step_8(h_s, x, n);

    let mut randomness_sum = Fp::ZERO();
    for i in 0..randomness.len() {
        let x_pow_ni = x.pow(n * (i as u128));
        randomness_sum = randomness_sum + (randomness[i] * x_pow_ni);
    }
    let h_prime_com = commit_polyx(&(G, W), h_prime, randomness_sum);
    assert_eq!(H_prime, h_prime_com);
    H_prime == h_prime_com
}

#[cfg(test)]
#[test]
fn test_step_5_6_7_8() {
    fn a(h: UniPolynomial, n: u8, x: u8, w: u8, randomness_seed: u8, G_seed: u8) -> bool {
        let h = h.0;

        // n should no be too small (for step 5)
        let n = n as u128 + 5;

        // STEP 5
        let h_s = step_5(h, n);

        ////////////////////////////////////////////////////////////////////////////////////
        /// SETTING UP THE REQUIRED VALUES (W, G, x, commitment-randomness), NOT INTERESTING
        ////////////////////////////////////////////////////////////////////////////////////
        let x = Fp::from_literal(x as u128);
        let W = g1mul(Fp::from_literal(w as u128), g1_generator());

        // get the length of a h_i, which is the same as the length of G
        let h_i_len: &Seq<Fp> = &(h_s[0]);
        let h_i_len = h_i_len.len();
        // get the number of h_i polys, which is the same as the number
        // of random elements for comitting
        let h_s_len = h_s.len();

        // there should be as many G elements as there are elements in the h_i polys
        let mut G = Seq::<G1>::create(h_i_len);
        let G_seed = Fp::from_literal(G_seed as u128 + 1); // +1, so it non-zero

        // create some "randomness" for G
        G[0] = g1mul(G_seed, g1_generator());
        for i in 1..G.len() {
            G[i] = g1mul(G_seed, G[i - 1]);
        }

        // there should be as many random elements as there are h_i polys
        let mut randomness = Seq::<Fp>::create(h_s_len);
        // create some "randomness" for commitments
        randomness[0] = Fp::from_literal(randomness_seed as u128 + 1); // +1, so it non-zero
        for i in 1..randomness.len() {
            randomness[i] = (randomness[i - 1] + Fp::ONE()) * Fp::TWO();
        }
        //////////////////////////////////////////////////////////////////////////////////
        /// SETTING UP VALUES DONE
        //////////////////////////////////////////////////////////////////////////////////

        // STEP 6
        let H_s = step_6(h_s.clone(), &(G.clone(), W), randomness.clone());
        // STEP 7
        let H_prime = step_7(H_s, x, n);
        // STEP 8
        let h_prime = step_8(h_s, x, n);

        // sum the randomess corresponding (see the thesis for furhter explanation)
        let mut randomness_sum = Fp::ZERO();
        for i in 0..randomness.len() {
            let x_pow_ni = x.pow(n * (i as u128));
            randomness_sum = randomness_sum + (randomness[i] * x_pow_ni);
        }

        // commit to h_prime
        let h_prime_com = commit_polyx(&(G, W), h_prime, randomness_sum);
        assert_eq!(H_prime, h_prime_com);
        H_prime == h_prime_com
    }

    // limit the number of tests, since it is SLOW
    QuickCheck::new().tests(50).quickcheck(
        a as fn(h: UniPolynomial, n: u8, x: u8, w: u8, randomness_seed: u8, G_seed: u8) -> bool,
    );
}

// hardcoded test, results calculated on the "blackboard"
// #[cfg(test)]
// #[test]
// fn test_step_11_manual() {
//     let n_q = 3;
//     let n_a = 3;
//     let x1 = Fp::TWO();
//     let H_prime = g1mul(Fp::TWO(), g1_generator());
//     let R = g1_generator();
//     let a = Seq::<G1>::from_vec(vec![
//         g1mul(Fp::from_literal(2), g1_generator()),
//         g1mul(Fp::from_literal(3), g1_generator()),
//         g1mul(Fp::from_literal(4), g1_generator()),
//     ]);
//     let q = Seq::<Seq<u128>>::from_vec(vec![
//         (Seq::<u128>::from_vec(vec![0])),
//         (Seq::<u128>::from_vec(vec![1, 2, 0])),
//         (Seq::<u128>::from_vec(vec![2, 0, 2])),
//     ]);
//     let Q_s = step_11(n_a, x1, H_prime, R, a, q);

//     // testing BULLET 1
//     // Q_i = [x1]Q_i + A_j, for every time i is in some sigma(j)
//     assert_eq!(g1mul(Fp::from_literal(3), g1_generator()), Q_s[1]);
//     assert_eq!(g1mul(Fp::from_literal(24), g1_generator()), Q_s[2]);

//     // testing BULLET 2
//     assert_eq!(g1mul(Fp::from_literal(77), g1_generator()), Q_s[0]);
// }

#[cfg(test)]
#[test]
fn test_step_11() {
    fn a(n_a: u8, n_q: u8, x1: u8, R_power: u8, H_power: u8, a_seed: u8) -> bool {
        ////////////////////////////////////////////////////////////////////////////////////
        /// SETTING UP THE REQUIRED VALUES (n_a, n_q, x1, H', R, the q list, the A commitemtns), NOT INTERESTING
        ////////////////////////////////////////////////////////////////////////////////////
        let mut n_a: u8 = n_a; // make it non-zero
        if n_a == 0 {
            n_a = 1;
        }
        let mut n_q: u8 = n_q; // make it non-zero
        if n_q == 0 {
            n_q = 1;
        }
        if n_q > n_a {
            n_q = n_q % n_a
        }
        let x1 = Fp::from_literal(x1 as u128);
        let H_prime = g1mul(Fp::from_literal(H_power as u128), g1_generator());
        let R = g1mul(Fp::from_literal(R_power as u128), g1_generator());

        let mut a = Seq::<G1>::create(n_a as usize);
        a[0] = g1mul(Fp::from_literal(a_seed as u128), g1_generator());
        for i in 1..a.len() {
            a[i] = g1mul(Fp::from_literal(a_seed as u128), a[i - 1]);
        }

        let mut sigma_list: Vec<u128> = vec![];
        let mut q = Seq::<Seq<u128>>::create(n_a as usize);
        // create some random values for q, each entry with len n_q/2
        // and entries for sigma_list to be used in sigma
        // (note, here we actually do not guarantee that q's elements are distinct)
        // add one more entry for sigma_list, since the loop starts at 1
        let sigma_idx = rand::Rng::gen_range(&mut rand::thread_rng(), 0..q.len());
        sigma_list.push(sigma_idx as u128);
        q[0] = Seq::<u128>::from_vec(vec![0]); // q[0]={0} by definition
        for i in 1..q.len() {
            let mut v: Vec<u128> = vec![];
            for j in 0..n_q {
                v.push(j as u128);
            }
            v.shuffle(&mut thread_rng());
            let v = &v[0..((n_q / 2) as usize)];
            q[i] = Seq::from_vec(v.to_vec());

            let sigma_idx = rand::Rng::gen_range(&mut rand::thread_rng(), 0..q.len());
            sigma_list.push(sigma_idx as u128);
        }
        let n_q: usize = q.len();

        let sigma_seq = Seq::<u128>::from_vec(sigma_list);

        //////////////////////////////////////////////////////////////////////////////////
        /// SETTING UP VALUES DONE
        //////////////////////////////////////////////////////////////////////////////////
        let Q_s = step_11(
            n_a as u128,
            x1,
            H_prime,
            R,
            a.clone(),
            q.clone(),
            sigma_seq.clone(),
        );

        // calculate each Q_i and check that it corresponds with the output of step_11
        for i in 0..n_q {
            let mut Q = g1_default();
            // BULLET 1
            // Q_i := [x1]Q_i + A_j, for every time i is in some sigma(j)
            for j in 0..a.len() {
                let p_j = sigma(j as u128, sigma_seq.clone(), q.clone());
                for k in 0..p_j.len() {
                    if i == p_j[k] as usize {
                        Q = g1add(g1mul(x1, Q), a[j]);
                    }
                }
            }
            // BULLET 2
            // Q_0 := [x1^2]Q_0 + [x1]H' + R
            if i == 0 {
                Q = g1mul(x1.pow(2), Q);
                Q = g1add(Q, g1mul(x1, H_prime));
                Q = g1add(Q, R);
            }
            if Q != Q_s[i as usize] {
                return false;
            }
        }

        true
    }
    // limit the number of tests, since it is SLOW
    QuickCheck::new().tests(1).quickcheck(
        a as fn(n_a: u8, n_q: u8, x1: u8, R_power: u8, H_power: u8, a_seed: u8) -> bool,
    );
}

#[cfg(test)]
#[test]
fn test_step_12() {
    fn a(
        n_a: u8,
        n_q: u8,
        x1: u8,
        r: UniPolynomial,
        h: UniPolynomial,
        a_polys: SeqOfUniPoly,
    ) -> bool {
        ////////////////////////////////////////////////////////////////////////////////////
        /// SETTING UP THE REQUIRED VALUES (n_a, n_q, x1, H', R, the q list, the A commitemtns), NOT INTERESTING
        ////////////////////////////////////////////////////////////////////////////////////
        let mut n_a: u8 = n_a; // make it non-zero
        if n_a == 0 {
            n_a = 1;
        }
        let mut n_q: u8 = n_q; // make it non-zero
        if n_q == 0 {
            n_q = 1;
        }
        if n_q > n_a {
            n_q = n_q % n_a
        }
        let x1 = Fp::from_literal(x1 as u128);

        let mut sigma_list: Vec<u128> = vec![];
        let mut q = Seq::<Seq<u128>>::create(n_a as usize);
        // create some random values for q, each entry with len n_q/2
        // and entries for sigma_list to be used in sigma
        // (note, here we actually do not guarantee that q's elements are distinct)
        // add one more entry for sigma_list, since the loop starts at 1
        let sigma_idx = rand::Rng::gen_range(&mut rand::thread_rng(), 0..q.len());
        sigma_list.push(sigma_idx as u128);
        q[0] = Seq::<u128>::from_vec(vec![0]); // q[0]={0} by definition
        for i in 1..q.len() {
            let mut v: Vec<u128> = vec![];
            for j in 0..n_q {
                v.push(j as u128);
            }
            v.shuffle(&mut thread_rng());
            let v = &v[0..((n_q / 2) as usize)];
            q[i] = Seq::from_vec(v.to_vec());

            let sigma_idx = rand::Rng::gen_range(&mut rand::thread_rng(), 0..q.len());
            sigma_list.push(sigma_idx as u128);
        }

        let sigma_seq = Seq::<u128>::from_vec(sigma_list);

        // a_polys is a number of random polys, but there should be n_a of them
        // (SeqOfUniPoly generates a fixed length seq of polys)
        let mut a_polys = a_polys.0;
        if a_polys.len() > n_a as usize {
            a_polys = Seq::from_vec(a_polys.native_slice()[0..(n_a as usize)].to_vec());
        } else if a_polys.len() < n_a as usize {
            let diff = n_a as usize - a_polys.len();
            for _ in 0..diff {
                // if wrong size, just use 0
                a_polys = a_polys.push(&Seq::<Fp>::from_vec(vec![Fp::ZERO()]));
            }
        }
        //////////////////////////////////////////////////////////////////////////////////
        /// SETTING UP VALUES DONE
        //////////////////////////////////////////////////////////////////////////////////
        let h = h.0;
        let r = r.0;
        let q_s = step_12(
            n_a as u128,
            x1,
            h.clone(),
            r.clone(),
            a_polys.clone(),
            q.clone(),
            sigma_seq.clone(),
        );
        // calculate each Q_i and check that it corresponds with the output of step_12
        for i in 0..n_q {
            let mut q_poly = Seq::<Fp>::create(1);
            // BULLET 1
            // q_i := x1 * q_i + a'_j(X), for every time i is in some sigma(j)
            for j in 0..n_a {
                let p_j = sigma(j as u128, sigma_seq.clone(), q.clone());
                for k in 0..p_j.len() {
                    if i == p_j[k] as u8 {
                        q_poly = add_polyx(mul_scalar_polyx(q_poly, x1), a_polys[j].clone())
                    }
                }
            }
            // BULLET 2
            // q_0 := x1^2 * q_0 + x1 * h'(X) + r(X)
            if i == 0 {
                q_poly = mul_scalar_polyx(q_poly, x1.pow(2));
                q_poly = add_polyx(q_poly, mul_scalar_polyx(h.clone(), x1));
                q_poly = add_polyx(q_poly, r.clone());
            }
            q_poly = trim_poly(q_poly);
            let expected = trim_poly(q_s[i as usize].clone());
            if q_poly.len() != expected.len() {
                return false;
            }
            for j in 0..q_poly.len() {
                if q_poly[j] != expected[j] {
                    return false;
                }
            }
        }

        true
    }
    // limit the number of tests, since it is SLOW
    QuickCheck::new().tests(10).quickcheck(
        a as fn(
            n_a: u8,
            n_q: u8,
            x1: u8,
            r: UniPolynomial,
            h: UniPolynomial,
            a_polys: SeqOfUniPoly,
        ) -> bool,
    );
}

// quickcheck is "limited" (not exactly) to eight arguments
// so we have to reuse some of the values in some way
#[cfg(test)]
#[test]
fn test_step_13() {
    fn a(
        n_a: u8,
        n_q: u8,
        omega: u8,
        x: u8,
        r: u8,
        s: SeqOfUniPoly,
        a: SeqOfUniPoly,
        g_prime: UniPolynomial,
    ) -> bool {
        ////////////////////////////////////////////////////////////////////////////////////
        /// SETTING UP THE REQUIRED VALUES (n_a, n_q, x1, H', R, the q list, the A commitemtns), NOT INTERESTING
        ////////////////////////////////////////////////////////////////////////////////////
        let mut n_a: u128 = n_a as u128; // make it non-zero
        if n_a == 0 {
            n_a = 1;
        }
        let mut n_q: u128 = n_q as u128; // make it non-zero
        if n_q == 0 {
            n_q = 1;
        }
        if n_q > n_a {
            n_q = n_q % n_a
        }
        let mut n = n_q * 3; // a bit of reuse, due the above restrictions
        if n == 0 {
            n = 1;
        }
        let omega = Fp::from_literal(omega as u128);
        let x = Fp::from_literal(x as u128);
        let x1 = x * Fp::TWO(); // a bit of reuse, due the above restrictions
        let r = Fp::from_literal(r as u128);
        let s = s.0;
        let mut q = Seq::<Seq<u128>>::create(n_a as usize);
        let a = a.0;
        let g_prime = g_prime.0;

        let mut sigma_list: Vec<u128> = vec![];
        let mut q = Seq::<Seq<u128>>::create(n_a as usize);
        // create some random values for q, each entry with len n_q/2
        // and entries for sigma_list to be used in sigma
        // (note, here we actually do not guarantee that q's elements are distinct)
        // add one more entry for sigma_list, since the loop starts at 1
        let sigma_idx = rand::Rng::gen_range(&mut rand::thread_rng(), 0..q.len());
        sigma_list.push(sigma_idx as u128);
        q[0] = Seq::<u128>::from_vec(vec![0]); // q[0]={0} by definition
        for i in 1..q.len() {
            let mut v: Vec<u128> = vec![];
            for j in 0..n_q {
                v.push(j as u128);
            }
            v.shuffle(&mut thread_rng());
            let v = &v[0..((n_q / 2) as usize)];
            q[i] = Seq::from_vec(v.to_vec());

            let sigma_idx = rand::Rng::gen_range(&mut rand::thread_rng(), 0..q.len());
            sigma_list.push(sigma_idx as u128);
        }

        let sigma_seq = Seq::<u128>::from_vec(sigma_list);

        // s is a number of random polys, but there should be n_a of them
        // (SeqOfUniPoly generates a fixed length seq of polys)
        let mut s_polys = s;
        if s_polys.len() > n_a as usize {
            s_polys = Seq::from_vec(s_polys.native_slice()[0..(n_a as usize)].to_vec());
        } else if s_polys.len() < n_a as usize {
            let diff = n_a as usize - s_polys.len();
            for _ in 0..diff {
                // if wrong size, just use 0
                s_polys = s_polys.push(&Seq::<Fp>::from_vec(vec![Fp::ZERO()]));
            }
        }

        //////////////////////////////////////////////////////////////////////////////////
        /// SETTING UP VALUES DONE
        //////////////////////////////////////////////////////////////////////////////////
        let r_s = step_13(
            n_a as u128,
            n as u128,
            omega,
            x,
            x1,
            r,
            s_polys.clone(),
            q.clone(),
            sigma_seq.clone(),
            a,
            g_prime.clone(),
        );

        // calculate each r_i and check that it corresponds with the output of step_13
        for i in 0..n_q {
            let mut r_poly = Seq::<Fp>::create(1);
            // BULLET 1
            // r_i := x1 * r_i + s_j(X), for every time i is in some sigma(j)
            for j in 0..n_a {
                let p_j = sigma(j as u128, sigma_seq.clone(), q.clone());
                for k in 0..p_j.len() {
                    if i == p_j[k] {
                        r_poly =
                            add_polyx(mul_scalar_polyx(r_poly, x1), s_polys[j as usize].clone())
                    }
                }
            }
            // BULLET 2
            // r_0 := x1^2 * r_0 + x1 * h + r
            if i == 0 {
                r_poly = mul_scalar_polyx(r_poly, x1.pow(2));

                // calculate h
                // TODO for this to make sense we should test
                // * eval_poly_x
                // * compute_vanishing_polynomial
                let g_prime_x: Fp = eval_polyx(g_prime.clone(), x);
                let vanishing_poly: Seq<Fp> = compute_vanishing_polynomial(omega, n);
                let vanishing_poly_x: Fp = eval_polyx(vanishing_poly, x);
                let h = g_prime_x / vanishing_poly_x;

                r_poly = add_scalar_polyx(r_poly, x1 * h);
                r_poly = add_scalar_polyx(r_poly, r.clone());
            }
            r_poly = trim_poly(r_poly);
            let expected = trim_poly(r_s[i as usize].clone());
            if r_poly.len() != expected.len() {
                return false;
            }
            for j in 0..r_poly.len() {
                if r_poly[j] != expected[j] {
                    return false;
                }
            }
        }

        true
    }
    // limit the number of tests, since it is SLOW
    QuickCheck::new().tests(5).quickcheck(
        a as fn(
            n_a: u8,
            n_q: u8,
            omega: u8,
            x: u8,
            r: u8,
            s: SeqOfUniPoly,
            a: SeqOfUniPoly,
            g_prime: UniPolynomial,
        ) -> bool,
    );
}

// #[cfg(test)]
// #[test]
// fn test_step_14_manuel() {
//     ////////////////////////////////////////////////////////////////////////////////////
//     /// SETTING UP THE REQUIRED VALUES (n_a, n_q, x1, H', R, the q list, the A commitemtns), NOT INTERESTING
//     ////////////////////////////////////////////////////////////////////////////////////
//     let w = 3;
//     // W and G from CRS
//     let W = g1mul(Fp::from_literal(w as u128), g1_generator());
//     // there should be as many G elements as there are elements in the h_i polys
//     let G = Seq::<G1>::from_vec(vec![
//         g1mul(Fp::ONE(), g1_generator()),
//         g1mul(Fp::TWO(), g1_generator()),
//         g1mul(Fp::from_literal(3), g1_generator()),
//         g1mul(Fp::from_literal(4), g1_generator()),
//     ]);
//     // let crs: CRS = (G, W);

//     // let x2 = Fp::from_literal(x as u128);
//     let x = Fp::TWO(); // Dummy

//     let x2 = x.mul(x);

//     let omega: Fp = Fp::TWO();

//     let n_q = 3; // Dummy

//     let q_polys: Seq<Seq<Fp>> = Seq::<Seq<Fp>>::from_vec(vec![
//         Seq::from_vec(vec![
//             Fp::from_literal(1),
//             Fp::from_literal(2),
//             Fp::from_literal(3),
//         ]),
//         Seq::from_vec(vec![
//             Fp::from_literal(4),
//             Fp::from_literal(5),
//             Fp::from_literal(6),
//         ]),
//         Seq::from_vec(vec![
//             Fp::from_literal(7),
//             Fp::from_literal(8),
//             Fp::from_literal(9),
//         ]),
//     ]);
//     let r_polys: Seq<Seq<Fp>> = Seq::<Seq<Fp>>::from_vec(vec![
//         Seq::from_vec(vec![
//             Fp::from_literal(9),
//             Fp::from_literal(8),
//             Fp::from_literal(7),
//         ]),
//         Seq::from_vec(vec![
//             Fp::from_literal(6),
//             Fp::from_literal(5),
//             Fp::from_literal(4),
//         ]),
//         Seq::from_vec(vec![
//             Fp::from_literal(3),
//             Fp::from_literal(2),
//             Fp::from_literal(1),
//         ]),
//     ]);
//     // let r = Fp::from_literal(r as u128);
//     let r = Fp::ONE(); // Dummy

//     // create some random values for q, each entry with len n_q/2
//     let q = Seq::<Seq<u128>>::from_vec(vec![
//         Seq::from_vec(vec![0]),
//         Seq::from_vec(vec![0, 1, 2]),
//         Seq::from_vec(vec![0, 1, 2]),
//     ]);

//     //////////////////////////////////////////////////////////////////////////////////
//     /// SETTING UP VALUES DONE
//     //////////////////////////////////////////////////////////////////////////////////
//     let q_prime: G1 = step_14(&(G.clone(), W), x2, q_polys, r_polys, q, r, omega, x);

//     //////////////////////////////////////////////////////////////////////////////////
//     /// MANUEL CALCULATION
//     //////////////////////////////////////////////////////////////////////////////////

//     /// i = 0 in outer sum
//     let mut i_0_dividend = sub_polyx(
//         Seq::from_vec(vec![
//             Fp::from_literal(1),
//             Fp::from_literal(2),
//             Fp::from_literal(3),
//         ]),
//         Seq::from_vec(vec![
//             Fp::from_literal(9),
//             Fp::from_literal(8),
//             Fp::from_literal(7),
//         ]),
//     );
//     let i_0_divisor = Seq::from_vec(vec![Fp::from_literal(2).neg(), Fp::from_literal(1)]);
//     let i_0_division = divide_poly(i_0_dividend, i_0_divisor).0;
//     let i_0 = mul_scalar_polyx(i_0_division, Fp::ONE());

//     // i = 1 in outer sum
//     let i_1_dividend: Seq<Fp> = sub_polyx(
//         Seq::from_vec(vec![
//             Fp::from_literal(4),
//             Fp::from_literal(5),
//             Fp::from_literal(6),
//         ]),
//         Seq::from_vec(vec![
//             Fp::from_literal(6),
//             Fp::from_literal(5),
//             Fp::from_literal(4),
//         ]),
//     );
//     let mut i_1_divisor = Seq::from_vec(vec![
//         Fp::from_literal(1),
//         Fp::from_literal(0),
//         Fp::from_literal(0),
//         Fp::from_literal(0),
//     ]);
//     let mul_x = multi_poly_with_x(i_1_divisor.clone());
//     let mul_scalar: Seq<Fp> = mul_scalar_polyx(i_1_divisor.clone(), Fp::from_literal(2).neg());
//     i_1_divisor = add_polyx(mul_x, mul_scalar);

//     let mul_x = multi_poly_with_x(i_1_divisor.clone());
//     let mul_scalar: Seq<Fp> = mul_scalar_polyx(i_1_divisor, Fp::from_literal(4).neg());
//     i_1_divisor = add_polyx(mul_x, mul_scalar);

//     let mul_x = multi_poly_with_x(i_1_divisor.clone());
//     let mul_scalar: Seq<Fp> = mul_scalar_polyx(i_1_divisor.clone(), Fp::from_literal(8).neg());
//     i_1_divisor = add_polyx(mul_x, mul_scalar);

//     let i_1_division = divide_poly(i_1_dividend, i_1_divisor.clone()).0;
//     let i_1 = mul_scalar_polyx(i_1_division, Fp::from_literal(4));

//     // i=2 in outer sum

//     let i_2_dividend: Seq<Fp> = sub_polyx(
//         Seq::from_vec(vec![
//             Fp::from_literal(7),
//             Fp::from_literal(8),
//             Fp::from_literal(9),
//         ]),
//         Seq::from_vec(vec![
//             Fp::from_literal(3),
//             Fp::from_literal(2),
//             Fp::from_literal(1),
//         ]),
//     );
//     let i_2_division = divide_poly(i_2_dividend, i_1_divisor).0;
//     let i_2 = mul_scalar_polyx(i_2_division, Fp::from_literal(16));
//     let result = add_polyx(i_0, add_polyx(i_1, i_2));
//     let commitment: (FpCurve, FpCurve, bool) = commit_polyx(&(G.clone(), W), result, r);
//     assert_eq!(commitment, q_prime);
// }

#[cfg(test)]
#[test]
fn test_step_14() {
    fn a(
        w: u8,
        x: u8,
        n_q: u128,
        q_polys: SeqOfUniPoly,
        r_polys: SeqOfUniPoly,
        r: u8,
        omega: u8,
        G_seed: u8,
    ) -> bool {
        ////////////////////////////////////////////////////////////////////////////////////
        /// SETTING UP THE REQUIRED VALUES (n_a, n_q, x1, H', R, the q list, the A commitemtns), NOT INTERESTING
        ////////////////////////////////////////////////////////////////////////////////////
        let W = g1mul(Fp::from_literal(w as u128), g1_generator());

        let x = Fp::from_literal(x as u128);

        let x2 = x.mul(x.add(Fp::TWO().pow(19)));

        let omega: Fp = Fp::TWO();

        let r_polys = r_polys.0;
        let q_polys = q_polys.0;

        let r = Fp::from_literal(r as u128);
        let mut n_q = q_polys.len() as u128;
        if n_q > r_polys.len() as u128 {
            n_q = r_polys.len() as u128
        }

        // create some random values for q, each entry with len n_q/2
        let mut sigma_list: Vec<u128> = vec![];
        let mut q = Seq::<Seq<u128>>::create(n_q as usize);
        let sigma_idx = rand::Rng::gen_range(&mut rand::thread_rng(), 0..q.len());
        sigma_list.push(sigma_idx as u128);
        q[0] = Seq::<u128>::from_vec(vec![0]); // q[0]={0} by definition
        for i in 1..q.len() {
            let mut v: Vec<u128> = vec![];
            for j in 0..n_q {
                v.push(j as u128);
            }
            v.shuffle(&mut thread_rng());
            let v = &v[0..((n_q / 2) as usize)];
            q[i] = Seq::from_vec(v.to_vec());

            let sigma_idx = rand::Rng::gen_range(&mut rand::thread_rng(), 0..q.len());
            sigma_list.push(sigma_idx as u128);
        }

        let sigma_seq = Seq::<u128>::from_vec(sigma_list);

        //////////////////////////////////////////////////////////////////////////////////
        /// SETTING UP VALUES DONE
        //////////////////////////////////////////////////////////////////////////////////

        //////////////////////////////////////////////////////////////////////////////////
        /// MANUEL CALCULATION
        //////////////////////////////////////////////////////////////////////////////////
        let mut sum_result = Seq::from_vec(vec![Fp::from_literal(0)]);

        for i in 0..(n_q as usize) as usize {
            let dividend_lhs: Seq<Fp> = mul_scalar_polyx(q_polys[i].clone(), x2.pow(i as u128));
            let dividend_rhs: Seq<Fp> = mul_scalar_polyx(r_polys[i].clone(), x2.pow(i as u128));
            let dividend: Seq<Fp> = sub_polyx(dividend_lhs, dividend_rhs);

            let q_i = sigma(i as u128, sigma_seq.clone(), q.clone());
            let n_e = q_i.len();
            // let mut divisor: Seq<Fp> = Seq::from_vec(vec![Fp::from_literal(1)]);
            let mut divisor: Seq<Fp> = Seq::<Fp>::create(q_i.len() + 1 as usize);
            divisor[0] = Fp::ONE();

            for j in 0..n_e as usize {
                let divisor_lhs: Seq<Fp> = multi_poly_with_x(divisor.clone());
                let q_i_j: u128 = q_i[j];
                let rhs_scalar: Fp = omega.pow(q_i_j).mul(x).neg();
                let divisor_rhs_mult: Seq<Fp> = mul_scalar_polyx(divisor, rhs_scalar);
                divisor = add_polyx(divisor_lhs, divisor_rhs_mult);
            }
            let division: Seq<Fp> = divide_poly(dividend.clone(), divisor).0;

            sum_result = add_polyx(sum_result, division);
        }

        //////////////////////////////
        /// CREATE G WITH CORRECT LENGTH - NEEDS TO BE SAME LENGTH AS POLY YOU WANT TO COMMIT TO
        //////////////////////////////
        let mut G = Seq::<G1>::create(sum_result.clone().len());
        let G_seed = Fp::from_literal(G_seed as u128 + 1); // +1, so it non-zero

        // create some "randomness" for G
        G[0] = g1mul(G_seed, g1_generator());
        for i in 1..G.len() {
            G[i] = g1mul(G_seed, G[i - 1]);
        }
        /////////////////////////////
        /// FINISHED CREATHING G
        /////////////////////////////
        let q_prime_test = commit_polyx(&(G.clone(), W), sum_result, r);
        let q_prime: G1 = step_14(
            &(G.clone(), W),
            x2,
            q_polys.clone(),
            r_polys.clone(),
            q.clone(),
            sigma_seq,
            r,
            omega,
            x,
        );

        assert_eq!(q_prime, q_prime_test);
        true
    }
    // limit the number of tests, since it is SLOW
    QuickCheck::new().tests(5).quickcheck(
        a as fn(
            w: u8,
            x: u8,
            n_q: u128,
            q_polys: SeqOfUniPoly,
            r_polys: SeqOfUniPoly,
            r: u8,
            omega: u8,
            G_seed: u8,
        ) -> bool,
    );
}

#[cfg(test)]
#[test]
fn test_step_16() {
    fn a(x3: u8, q_polys: SeqOfUniPoly) -> bool {
        let q_polys: Seq<Seq<Fp>> = q_polys.0;
        let n_q: u128 = q_polys.len() as u128;
        let x3: Fp = Fp::from_literal(x3 as u128);
        let u: Seq<Fp> = step_16(n_q, x3, q_polys.clone());
        for i in 0..u.len() as usize {
            let u_i: Fp = u[i];
            let q_i: Seq<Fp> = q_polys[i].clone();
            let q_i_eval: Fp = eval_polyx(q_i, x3);
            assert_eq!(u_i, q_i_eval);
        }
        true
    }
    // limit the number of tests, since it is SLOW
    QuickCheck::new()
        .tests(50)
        .quickcheck(a as fn(x3: u8, q_polys: SeqOfUniPoly) -> bool);
}

// #[cfg(test)]
// #[test]
// fn test_step_18_manuel() {
//     let x: Fp = Fp::from_literal(83729);
//     let x1: Fp = Fp::from_literal(1209837);
//     let x2: Fp = Fp::from_literal(5423890);
//     let x3: Fp = Fp::from_literal(2);
//     let x4: Fp = Fp::from_literal(2340938);
//     let omega: Fp = Fp::from_literal(929392);
//     let Q_prime: G1 = g1mul(Fp::from_literal(123231), g1_generator());
//     let Q: Seq<G1> = Seq::<G1>::from_vec(vec![
//         g1mul(Fp::from_literal(2), g1_generator()),
//         g1mul(Fp::from_literal(3), g1_generator()),
//         g1mul(Fp::from_literal(4), g1_generator()),
//     ]);
//     let q: Seq<Seq<u128>> = Seq::<Seq<u128>>::from_vec(vec![
//         (Seq::<u128>::from_vec(vec![0])),
//         (Seq::<u128>::from_vec(vec![1, 2, 0])),
//         (Seq::<u128>::from_vec(vec![2, 0, 2])),
//     ]);
//     let u: Seq<Fp> = Seq::<Fp>::from_vec(vec![
//         Fp::from_literal(2123),
//         Fp::from_literal(0),
//         Fp::from_literal(2),
//     ]);
//     let r: Seq<Seq<Fp>> = Seq::<Seq<Fp>>::from_vec(vec![
//         (Seq::<Fp>::from_vec(vec![
//             Fp::from_literal(123),
//             Fp::from_literal(4322),
//             Fp::from_literal(99283),
//         ])),
//         (Seq::<Fp>::from_vec(vec![
//             Fp::from_literal(2839),
//             Fp::from_literal(2123),
//             Fp::from_literal(0),
//         ])),
//         (Seq::<Fp>::from_vec(vec![
//             Fp::from_literal(1919919191),
//             Fp::from_literal(0),
//             Fp::from_literal(11183),
//         ])),
//     ]);

//     let P_sum_0: (FpCurve, FpCurve, bool) = Q[0];
//     let P_sum_1: (FpCurve, FpCurve, bool) = g1mul(x4, Q[1]);
//     let P_sum_2: (FpCurve, FpCurve, bool) = g1mul(x4.pow(2), Q[2]);
//     let P_sum: (FpCurve, FpCurve, bool) = g1add(g1add(P_sum_0, P_sum_1), P_sum_2);
//     let P_test: (FpCurve, FpCurve, bool) = g1add(g1mul(x4, P_sum), Q_prime);
//     let (P, v) = step_18(
//         x,
//         x1,
//         x2,
//         x3,
//         x4,
//         omega,
//         Q_prime,
//         Q,
//         u.clone(),
//         r.clone(),
//         q,
//     );
//     assert_eq!(P_test, P);
//     //Calculate v
//     let r_clone: Seq<Seq<Fp>> = r.clone();
//     let first_sum_0_dividend = u[0]
//         - eval_polyx(
//             Seq::<Fp>::from_vec(vec![
//                 Fp::from_literal(123),
//                 Fp::from_literal(4322),
//                 Fp::from_literal(99283),
//             ]),
//             x3,
//         );
//     let mut first_sum_0_divisor: Fp = x3 - x;
//     let first_sum_0: Fp = first_sum_0_dividend / first_sum_0_divisor;

//     let first_sum_1_dividend = u[1]
//         - eval_polyx(
//             Seq::<Fp>::from_vec(vec![
//                 Fp::from_literal(2839),
//                 Fp::from_literal(2123),
//                 Fp::from_literal(0),
//             ]),
//             x3,
//         );

//     let mut first_sum_1_divisor: Fp = x3 - (omega * x);
//     first_sum_1_divisor = first_sum_1_divisor * (x3 - (omega.pow(2) * x));
//     first_sum_1_divisor = first_sum_1_divisor * (x3 - x);
//     let first_sum_1: Fp = x2 * (first_sum_1_dividend / first_sum_1_divisor);

//     let first_sum_2_dividend = u[2]
//         - eval_polyx(
//             Seq::<Fp>::from_vec(vec![
//                 Fp::from_literal(1919919191),
//                 Fp::from_literal(0),
//                 Fp::from_literal(11183),
//             ]),
//             x3,
//         );

//     let mut first_sum_2_divisor: Fp = (x3 - (omega.pow(2) * x));
//     first_sum_2_divisor = first_sum_2_divisor * (x3 - x);
//     first_sum_2_divisor = first_sum_2_divisor * (x3 - (omega.pow(2) * x));
//     let first_sum_2: Fp = x2.pow(2) * (first_sum_2_dividend / first_sum_2_divisor);

//     let first_sum: Fp = first_sum_0 + first_sum_1 + first_sum_2;

//     let second_sum_0: Fp = x4 * u[0];
//     let second_sum_1: Fp = x4 * u[1];
//     let second_sum_2: Fp = x4 * u[2];

//     let second_sum: Fp = x4 * (second_sum_0 + second_sum_1 + second_sum_2);

//     let test_v: Fp = first_sum + second_sum;

//     assert_eq!(test_v, v)
// }

#[cfg(test)]
#[test]
fn test_step_18() {
    fn a(rnd1: u8, rnd2: u8, omega: u8, r: SeqOfUniPoly) -> bool {
        let r: Seq<Seq<Fp>> = r.0;
        let n_q: usize = r.len();
        let mut x1: Fp = Fp::from_literal(rnd1 as u128).pow(123);
        if x1 == Fp::ZERO() {
            x1 = Fp::ONE()
        }
        let mut x2: Fp = x1.pow(rnd1 as u128);
        if x2 == Fp::ZERO() {
            x2 = Fp::ONE()
        }
        let mut x3: Fp = x2 + x1 + Fp::from_literal(rnd2 as u128 + 7).pow(42);
        if x3 == Fp::ZERO() {
            x3 = Fp::ONE()
        }
        let mut x4: Fp = x1 * x2 + Fp::from_literal(929299292);
        if x4 == Fp::ZERO() {
            x4 = Fp::ONE()
        }
        let mut x: Fp = Fp::from_literal(rnd1 as u128);
        if x == Fp::ZERO() {
            x = Fp::ONE()
        }
        let mut omega: Fp = Fp::from_literal(omega as u128);
        if omega == Fp::ZERO() {
            omega = Fp::from_literal(123)
        }
        let Q_prime: G1 = g1mul(Fp::from_literal(rnd2 as u128), g1_generator());
        let mut Q: Seq<(FpCurve, FpCurve, bool)> = Seq::<G1>::create(n_q);
        for i in 0..n_q {
            let g1_seed: Fp = Fp::from_literal(rnd1 as u128 % (i + 1) as u128).pow(rnd2 as u128);
            Q[i] = g1mul(g1_seed, g1_generator());
        }
        let mut u: Seq<Fp> = Seq::<Fp>::create(n_q);
        for i in 0..n_q {
            let random_Fp: Fp = Fp::from_literal(rnd2 as u128 % (i + 1) as u128).pow(rnd1 as u128);
            u[i] = random_Fp;
        }

        let mut sigma_list: Vec<u128> = vec![];
        let mut q: Seq<Seq<u128>> = Seq::<Seq<u128>>::create(n_q as usize);
        let sigma_idx = rand::Rng::gen_range(&mut rand::thread_rng(), 0..q.len());
        sigma_list.push(sigma_idx as u128);
        q[0] = Seq::<u128>::from_vec(vec![0]); // q[0]={0} by definition
        for i in 1..q.len() {
            let mut v: Vec<u128> = vec![];
            for j in 0..n_q {
                v.push(j as u128);
            }
            v.shuffle(&mut thread_rng());
            let v = &v[0..((n_q / 2) as usize)];
            q[i] = Seq::from_vec(v.to_vec());

            let sigma_idx = rand::Rng::gen_range(&mut rand::thread_rng(), 0..q.len());
            sigma_list.push(sigma_idx as u128);
        }

        let sigma_seq = Seq::<u128>::from_vec(sigma_list);

        let (P, v) = step_18(
            x,
            x1,
            x2,
            x3,
            x4,
            omega,
            Q_prime,
            Q.clone(),
            u.clone(),
            r.clone(),
            q.clone(),
            sigma_seq.clone(),
        );

        ///////////TEST IMPLEMENTATION FOR P////////////////////
        let mut test_P: G1 = Q_prime;
        for i in 0..n_q {
            test_P = g1add(test_P, g1mul(x4.pow(i as u128 + 1), Q[i]));
        }
        let mut test_v = Fp::ZERO();
        assert_eq!(P, test_P);
        ////////////TEST IMPLEMENTATION FOR v//////////////////
        // let mut second_sum: Fp = Fp::ZERO();
        let mut first_sum: Fp = Fp::ZERO();
        let mut second_sum: Fp = Fp::ZERO();
        for i in 0..n_q {
            let first_sum_dividend: Fp = x2.pow(i as u128) * (u[i] - eval_polyx(r[i].clone(), x3));
            let q_i = sigma(i as u128, sigma_seq.clone(), q.clone());
            let mut first_sum_divisor = Fp::ONE();
            for j in 0..q_i.len() {
                first_sum_divisor = first_sum_divisor * (x3 - omega.pow(q_i[j]) * x);
            }
            second_sum = second_sum + x4 * x4 * u[i];
            first_sum = first_sum + (first_sum_dividend / first_sum_divisor);
        }
        let test_v: Fp = first_sum + second_sum;

        assert_eq!(v, test_v);

        true
    }
    // limit the number of tests, since it is SLOW
    QuickCheck::new()
        .tests(5)
        .quickcheck(a as fn(rnd1: u8, rnd2: u8, omega: u8, r: SeqOfUniPoly) -> bool);
}

#[cfg(test)]
#[test]
fn test_step_19() {
    fn a(x4: u8, q_prime: UniPolynomial, q_polys: SeqOfUniPoly) -> bool {
        let q_polys: Seq<Seq<Fp>> = q_polys.0;
        let n_q: usize = q_polys.len();
        let x4: Fp = Fp::from_literal(x4 as u128);
        let x4nq: Fp = x4.pow(n_q as u128);
        let mut q_prime: Seq<Fp> = q_prime.0;
        let p: Seq<Fp> = step_19(x4, q_prime.clone(), q_polys.clone());
        q_prime = mul_scalar_polyx(q_prime, x4nq);

        for i in 0..q_polys.len() {
            let mut q_i: Seq<Fp> = q_polys[i].clone();
            q_i = mul_scalar_polyx(q_i, x4.pow((n_q - 1 - i) as u128));
            // q_i = mul_scalar_polyx(q_i, x4);
            q_prime = add_polyx(q_i, q_prime.clone());
        }
        assert_eq!(p.len(), q_prime.len());
        for j in 0..p.len() {
            assert_eq!(p[j], q_prime[j]);
        }
        true
    }
    QuickCheck::new()
        .tests(50)
        .quickcheck(a as fn(x4: u8, q_prime: UniPolynomial, q_polys: SeqOfUniPoly) -> bool);
}

#[cfg(test)]
#[test]
fn test_step_22() {
    fn a(p_val: u8, g0_val: u8, s_val: u8, v_val: u8, xi_val: u8) -> bool {
        let p: G1 = g1mul(Fp::from_literal(p_val as u128), g1_generator());
        let g0: G1 = g1mul(Fp::from_literal(g0_val as u128), g1_generator());
        let s: G1 = g1mul(Fp::from_literal(s_val as u128), g1_generator());
        let v: Fp = Fp::from_literal(v_val as u128);
        let xi: Fp = Fp::from_literal(xi_val as u128);

        let test_result: G1 = g1add(p, g1add(g1neg(g1mul(v, g0)), g1mul(xi, s)));

        let p_prime: G1 = step_22(p, g0, s, v, xi);

        assert_eq!(p_prime, test_result);

        true
    }

    QuickCheck::new()
        .tests(50)
        .quickcheck(a as fn(p_val: u8, g0_val: u8, s_val: u8, v_val: u8, xi_val: u8) -> bool);
}

#[cfg(test)]
#[test]
fn test_step_23() {
    fn a(p: UniPolynomial, s: UniPolynomial, x3: u8, xi: u8) -> bool {
        let p: Seq<Fp> = p.0;
        let s: Seq<Fp> = s.0;
        let x3: Fp = Fp::from_literal(x3 as u128);
        let xi: Fp = Fp::from_literal(xi as u128);
        let test_result = add_polyx(
            add_scalar_polyx(p.clone(), eval_polyx(p.clone(), x3).neg()),
            mul_scalar_polyx(s.clone(), xi),
        );
        let p_prime: Seq<Fp> = step_23(p, s, x3, xi);
        assert_eq!(p_prime.len(), test_result.len());
        for i in 0..p_prime.len() {
            assert_eq!(p_prime[i], test_result[i])
        }
        true
    }
    QuickCheck::new()
        .tests(50)
        .quickcheck(a as fn(p: UniPolynomial, s: UniPolynomial, x3: u8, xi: u8) -> bool);
}

#[cfg(test)]
#[test]
fn test_step_24() {
    use hacspec_lib::num::traits::Pow;
    let p_prime_poly: Seq<Fp> = Seq::<Fp>::from_vec(vec![
        Fp::from_literal(12398129),
        Fp::from_literal(2222),
        Fp::from_literal(3038300),
        Fp::from_literal(4),
    ]);
    let G: Seq<G1> = Seq::<G1>::from_vec(vec![
        g1mul(Fp::from_literal(2123), g1_generator()),
        g1mul(Fp::from_literal(30283), g1_generator()),
        g1mul(Fp::from_literal(4), g1_generator()),
        g1mul(Fp::from_literal(999999999999), g1_generator()),
    ]);
    let x3: Fp = Fp::from_literal(981298129832983298);
    let z: Fp = Fp::from_literal(9812398329834298123123);
    let U: G1 = g1mul(Fp::from_literal(99), g1_generator());
    let W: G1 = g1mul(Fp::from_literal(42), g1_generator());
    let k: usize = 2;
    let n: usize = 2.exp(2) as usize;
    let L_blinding: Seq<Fp> =
        Seq::<Fp>::from_vec(vec![Fp::from_literal(298398123), Fp::from_literal(3232323)]);
    let R_blinding: Seq<Fp> =
        Seq::<Fp>::from_vec(vec![Fp::from_literal(939), Fp::from_literal(10293)]);
    let mut L: Seq<G1> = Seq::<G1>::create(k);
    let mut R: Seq<G1> = Seq::<G1>::create(k);

    let u: Seq<Fp> = Seq::<Fp>::from_vec(vec![
        Fp::from_literal(1),
        Fp::from_literal(2),
        Fp::from_literal(3),
        Fp::from_literal(4),
    ]);
    let (real_p_prime, real_G_prime, real_L, real_R) = step_24(
        p_prime_poly.clone(),
        G.clone(),
        x3,
        z,
        U,
        W,
        n as u128,
        k,
        u.clone(),
        L_blinding.clone(),
        R_blinding.clone(),
    );

    ////////manuel calculation////////////////
    let mut G_prime: Seq<G1> = G.clone();

    //First round
    let p_prime_lo: Seq<Fp> = Seq::<Fp>::from_vec(vec![p_prime_poly[0], p_prime_poly[1]]);
    let p_prime_hi: Seq<Fp> = Seq::<Fp>::from_vec(vec![p_prime_poly[2], p_prime_poly[3]]);
    let G_prime_lo: Seq<G1> = Seq::<G1>::from_vec(vec![G[0], G[1]]);
    let G_prime_hi: Seq<G1> = Seq::<G1>::from_vec(vec![G[2], G[3]]);
    let b_lo: Seq<Fp> = Seq::<Fp>::from_vec(vec![x3.pow(0), x3.pow(1)]);
    let b_hi: Seq<Fp> = Seq::<Fp>::from_vec(vec![x3.pow(2), x3.pow(3)]);
    let L_0: G1 = g1add(
        g1add(
            msm(p_prime_hi.clone(), G_prime_lo.clone()),
            g1mul(z * inner_product(p_prime_hi.clone(), b_lo.clone()), U),
        ),
        g1mul(L_blinding[0], W),
    );
    L[0] = L_0;

    let R_0: G1 = g1add(
        g1add(
            msm(p_prime_lo.clone(), G_prime_hi.clone()),
            g1mul(z * inner_product(p_prime_lo.clone(), b_hi.clone()), U),
        ),
        g1mul(R_blinding[0], W),
    );
    R[0] = R_0;

    G_prime = Seq::<G1>::from_vec(vec![
        g1add(G_prime_lo[0], g1mul(u[0], G_prime_hi[0])),
        g1add(G_prime_lo[1], g1mul(u[0], G_prime_hi[1])),
    ]);
    let mut b: Seq<Fp> =
        Seq::<Fp>::from_vec(vec![b_lo[0] + u[0] * b_hi[0], b_lo[1] + u[0] * b_hi[1]]);
    let u_j: Fp = u[0];
    let mut p_prime: Seq<Fp> = Seq::<Fp>::from_vec(vec![
        p_prime_lo[0] + u_j.inv() * p_prime_hi[0],
        p_prime_lo[1] + u_j.inv() * p_prime_hi[1],
    ]);

    //second round
    let p_prime_lo: Seq<Fp> = Seq::<Fp>::from_vec(vec![p_prime[0]]);
    let p_prime_hi: Seq<Fp> = Seq::<Fp>::from_vec(vec![p_prime[1]]);
    let G_prime_lo: Seq<G1> = Seq::<G1>::from_vec(vec![G_prime[0]]);
    let G_prime_hi: Seq<G1> = Seq::<G1>::from_vec(vec![G_prime[1]]);
    let b_lo: Seq<Fp> = Seq::<Fp>::from_vec(vec![b[0]]);
    let b_hi: Seq<Fp> = Seq::<Fp>::from_vec(vec![b[1]]);
    let L_1: G1 = g1add(
        g1add(
            msm(p_prime_hi.clone(), G_prime_lo.clone()),
            g1mul(z * inner_product(p_prime_hi.clone(), b_lo.clone()), U),
        ),
        g1mul(L_blinding[1], W),
    );
    L[1] = L_1;

    let R_1: G1 = g1add(
        g1add(
            msm(p_prime_lo.clone(), G_prime_hi.clone()),
            g1mul(z * inner_product(p_prime_lo.clone(), b_hi.clone()), U),
        ),
        g1mul(R_blinding[1], W),
    );
    R[1] = R_1;

    G_prime = Seq::<G1>::from_vec(vec![g1add(G_prime_lo[0], g1mul(u[1], G_prime_hi[0]))]);
    b = Seq::<Fp>::from_vec(vec![b_lo[0] + u[0] * b_hi[0]]);
    let u_j: Fp = u[1];

    p_prime = Seq::<Fp>::from_vec(vec![p_prime_lo[0] + u_j.inv() * p_prime_hi[0]]);
    assert_eq!(G_prime[0], real_G_prime[0]);
    assert_eq!(p_prime[0], real_p_prime[0]);
    assert_eq!(L[0], real_L[0]);
    assert_eq!(L[1], real_L[1]);
    assert_eq!(R[0], real_R[0]);
    assert_eq!(R[1], real_R[1]);
}

// u: Seq<Fp>,
// L: Seq<G1>,
// P_prime: G1,
// R: Seq<G1>,
// c: Fp,
// G_prime_0: G1,
// b_0: Fp,
// z: Fp,
// U: G1,
// f: Fp,
// W: G1,

#[cfg(test)]
#[test]
fn test_step_26() {
    let u: Seq<Fp> = Seq::<Fp>::from_vec(vec![Fp::from_literal(743), Fp::from_literal(9)]);
    let L: Seq<G1> = Seq::<G1>::from_vec(vec![
        g1mul(Fp::from_literal(74), g1_generator()),
        g1mul(Fp::from_literal(749292992), g1_generator()),
    ]);
    let R: Seq<G1> = Seq::<G1>::from_vec(vec![
        g1mul(Fp::from_literal(7), g1_generator()),
        g1mul(Fp::from_literal(92929929292), g1_generator()),
    ]);

    let P_prime: G1 = g1mul(Fp::from_literal(1239734), g1_generator());
    let c: Fp = Fp::from_literal(1919191);
    let G_prime_0: G1 = g1mul(Fp::from_literal(9191203983123123123123), g1_generator());
    let b_0: Fp = Fp::from_literal(87410923091283);
    let z: Fp = Fp::from_literal(699388299374);
    let U: G1 = g1mul(Fp::from_literal(77777777), g1_generator());
    let f: Fp = Fp::ONE();
    let W: G1 = (
        FpCurve::from_hex("29A35E837F1BC8F4D83DD8E452DAC6691BDEDE5F0916BB02E7EB3BF0D8724746"),
        FpCurve::from_hex("2E7E5A3C4EFBE72E130E31E28F22E98BF0A3225FCB5E579B61B98F28083A8A05"),
        false,
    );

    let mut rhs: G1 = g1add(
        g1mul(Fp::from_literal(743).inv(), L[0]),
        g1mul(Fp::from_literal(9).inv(), L[1]),
    );
    rhs = g1add(rhs, P_prime);
    rhs = g1add(
        rhs,
        g1add(
            g1mul(Fp::from_literal(743), R[0]),
            g1mul(Fp::from_literal(9), R[1]),
        ),
    );
    let mut lhs: G1 = g1mul(c, G_prime_0);
    lhs = g1add(lhs, g1mul((c * b_0 * z), U));
    lhs = g1add(lhs, g1mul(f, W));
    let diff: G1 = g1add(rhs, g1neg(lhs));
    assert!(step_26(u, L, P_prime, R, c, G_prime_0, b_0, z, U, f, W))
}
#[cfg(test)]
#[test]
fn testmsm() {
    let fs1 = Seq::<Fp>::from_vec(vec![
        Fp::from_literal(144),
        Fp::from_literal(22),
        Fp::from_literal(3),
        Fp::from_literal(74),
        Fp::from_literal(79),
    ]);

    let fs2 = Seq::<Fp>::from_vec(vec![
        Fp::from_literal(112),
        Fp::from_literal(2231),
        Fp::from_literal(88),
        Fp::from_literal(9),
        Fp::from_literal(98),
    ]);
    let gs = Seq::<G1>::from_vec(vec![
        (FpCurve::from_literal(2), FpCurve::from_literal(2), false),
        (FpCurve::from_literal(2), FpCurve::from_literal(5), false),
        (FpCurve::from_literal(5), FpCurve::from_literal(3), false),
        (FpCurve::from_literal(6), FpCurve::from_literal(8), false),
        (FpCurve::from_literal(2), FpCurve::from_literal(5), false),
    ]);
    let msmed1 = msm(fs1.clone(), gs.clone());
    let msmed2 = msm(fs2.clone(), gs.clone());
    let msm_sum = g1add(msmed1, msmed2);
    let mut fs_sum = add_polyx(fs1, fs2);
    let sum_sum = msm(fs_sum, gs);
}

#[cfg(test)]
#[test]
fn test_step_9_10() {
    fn a(a_prime_seq: SeqOfUniPoly, omega_value: u128, p: PorQ, x_value: u128) -> TestResult {
        let r = Seq::<Fp>::from_vec(vec![Fp::ZERO()]);
        if p.0.len() == 0 {
            return TestResult::discard();
        }
        let omega: Fp = Fp::from_literal(omega_value % 55);
        let x: Fp = Fp::from_literal(x_value % 55);

        let p: Seq<Seq<u128>> = p.0;
        let a: &Seq<u128> = &p[0];
        let n_e: usize = a.len();
        let n_a: usize = a_prime_seq.0.len();
        if n_e == 0 {
            return TestResult::discard();
        }
        if n_a == 0 {
            return TestResult::discard();
        }
        if x_value % 55 < 2 {
            return TestResult::discard();
        }
        if omega_value % 55 < 3 {
            return TestResult::discard();
        }
        let (_, a) = step_9(r, a_prime_seq.0, n_a, omega, p.clone(), x);
        let s = step_10(omega, p.clone(), x, a.clone(), n_a as u128);
        let mut i_range: usize = n_a - 1;
        if i_range > p.len() {
            i_range = p.len();
        }
        for i in 0..i_range {
            let p_i: Seq<u128> = p[i].clone();
            let s_i: Seq<Fp> = s[i].clone();
            let a_i: Seq<Fp> = a[i].clone();
            let mut j_range: usize = n_e - 1;
            if j_range > p_i.len() {
                j_range = p_i.len();
            }
            for j in 0..j_range {
                let p_i_j = p_i[j];
                let function_arg: Fp = omega.pow(p_i_j) * x;
                let s_eval: Fp = eval_polyx(s_i.clone(), function_arg);
                let a_i_j: Fp = a_i[j];
                assert_eq!(s_eval, a_i_j);
            }
        }

        TestResult::passed()
    }
    QuickCheck::new().tests(5).quickcheck(
        a as fn(a_prime_seq: SeqOfUniPoly, omega_value: u128, p: PorQ, x_value: u128) -> TestResult,
    );
}

#[cfg(test)]
#[quickcheck]
fn test_poly_mul_x(a: UniPolynomial) {
    let p1 = a.0;
    let new_p = &multi_poly_with_x(p1.clone());
    for i in 1..new_p.len() {
        assert_eq!(new_p[i], p1[i - 1]);
    }
    assert_eq!(new_p[0], Fp::from_literal(0));
}

#[cfg(test)]
#[quickcheck]
fn test_legrange(a: Points) {
    let points_seq = a.0;

    let legrange_poly = legrange_poly(points_seq.clone());

    for j in 0..points_seq.len() {
        let eval_x = points_seq[j].0;
        let point_y = points_seq[j].1;
        let res = eval_polyx(legrange_poly.clone(), eval_x);
        assert_eq!(res, point_y)
    }
}

#[cfg(test)]
#[quickcheck]
fn test_legrange_basis(a: Points) {
    let points_seq = a.0;
    // let points_seq  = Seq::<(Fp,Fp)>::from_vec(vec![(Fp::from_literal(1),Fp::from_literal(2)), (Fp::from_literal(2),Fp::from_literal(3)), (Fp::from_literal(5),Fp::from_literal(0))]);

    for i in 0..points_seq.len() {
        let x = points_seq[i].0;
        let basis = legrange_basis(points_seq.clone(), x);
        for j in 0..points_seq.len() {
            let eval_x = points_seq[j].0;
            let res = eval_polyx(basis.clone(), eval_x);
            if x == eval_x {
                assert_eq!(res, Fp::ONE())
            } else {
                assert_eq!(res, Fp::ZERO())
            }
        }
    }
}

#[cfg(test)]
#[test]
fn test_part_8() {
    let v1 = vec![5, 10, 20]
        .iter()
        .map(|e| Fp::from_literal((*e) as u128))
        .collect();
    let p1 = Seq::from_vec(v1);
    let n = 3;
    let poly_parts = step_5(p1, n);
    let x: Fp = Fp::default();
    let res: Seq<Fp> = step_8(poly_parts, x, n);
}

#[cfg(test)]
#[test]
fn test_part_7() {
    let commitment_seq: Seq<G1> =
        Seq::<G1>::from_vec(vec![g1_default(), g1_default(), g1_default()]);
    let x: Fp = Fp::default();
    let n: u128 = 128;
    let res: G1 = step_7(commitment_seq, x, n);
}

#[cfg(test)]
#[test]
fn test_commit_to_poly_parts() {
    let crs: CRS = (
        Seq::<G1>::from_vec(vec![g1_default(), g1_default(), g1_default()]),
        g1_default(),
    );

    let r_seq = Seq::<Fp>::from_vec(vec![Fp::default(), Fp::default(), Fp::default()]);
    let v1 = vec![5, 10, 20]
        .iter()
        .map(|e| Fp::from_literal((*e) as u128))
        .collect();
    let p1 = Seq::from_vec(v1);
    let n = 3;
    let poly_parts = step_5(p1, n);
    let commitments = step_6(poly_parts, &crs, r_seq);
}

#[cfg(test)]
#[test]
fn test_poly_add() {
    let v1 = vec![5, 10, 20]
        .iter()
        .map(|e| Fp::from_literal((*e) as u128))
        .collect();
    let v2 = vec![55]
        .iter()
        .map(|e| Fp::from_literal((*e) as u128))
        .collect();
    let p1 = Seq::from_vec(v1);
    let p2 = Seq::from_vec(v2);

    let p3 = add_polyx(p1, p2);

    assert_eq!(p3[0], Fp::from_literal(60));
    assert_eq!(p3[1], Fp::from_literal(10));
    assert_eq!(p3[2], Fp::from_literal(20));
}

#[cfg(test)]
#[test]
fn test_poly_mul() {
    let v1 = vec![5, 10, 20]
        .iter()
        .map(|e| Fp::from_literal((*e) as u128))
        .collect();
    let p1 = Seq::from_vec(v1);

    let p3 = mul_scalar_polyx(p1, Fp::TWO());

    assert_eq!(p3[0], Fp::from_literal(10));
    assert_eq!(p3[1], Fp::from_literal(20));
    assert_eq!(p3[2], Fp::from_literal(40));
}

#[cfg(test)]
#[test]
fn test_poly_eval() {
    let v1 = vec![5, 10, 20]
        .iter()
        .map(|e| Fp::from_literal((*e) as u128))
        .collect();
    let p1 = Seq::from_vec(v1);

    assert_eq!(eval_polyx(p1, Fp::TWO()), Fp::from_literal(105));
}

#[cfg(test)]
#[test]
fn test_reduce_multi_poly() {
    // 1 + 3xy + 5x*y^2 + 2x^2 + 2y
    let t1 = (Fp::from_literal(1), Seq::from_vec(vec![0, 0]));
    let t2 = (Fp::from_literal(3), Seq::from_vec(vec![1, 1]));
    let t3 = (Fp::from_literal(5), Seq::from_vec(vec![1, 2]));
    let t4 = (Fp::from_literal(2), Seq::from_vec(vec![2, 0]));
    let t5 = (Fp::from_literal(2), Seq::from_vec(vec![0, 1]));

    // the multivariate poly
    let p = Seq::from_vec(vec![t1, t2, t3, t4, t5]);
    // input value for y (2nd var), do not eval for x (1st var)
    let i1 = Seq::from_vec(vec![(false, Fp::ZERO()), (true, Fp::from_literal(5))]);
    // check that there are 5 terms, t1 through t5
    assert_eq!(p.len(), 5);

    // evaluate the polynomial with the y valye
    let evaluation1 = reduce_multi_poly(p, i1);

    // the last term (2y) becomes constant and should be joined with the other constant (1)
    // so there should be one less term
    assert_eq!(evaluation1.len(), 4);

    // input 2 for x (1st var)
    let i2 = Seq::from_vec(vec![(true, Fp::TWO())]);
    let evaluation2 = reduce_multi_poly(evaluation1, i2);

    // check that there is only 1 term left (a constant)
    assert_eq!(evaluation2.len(), 1);
    let (res, powers) = evaluation2.iter().next().unwrap();
    // this constant is the final evaluation of the poly
    assert_eq!(*res, Fp::from_literal(299));
    // no more vars, no more powers
    assert_eq!(powers.len(), 0);
}

#[cfg(test)]
#[test]
fn test_eval_multi_poly() {
    // 1 + 3xy + 5x*y^2 + 2x^2 + 2y
    let t1 = (Fp::from_literal(1), Seq::from_vec(vec![0, 0]));
    let t2 = (Fp::from_literal(3), Seq::from_vec(vec![1, 1]));
    let t3 = (Fp::from_literal(5), Seq::from_vec(vec![1, 2]));
    let t4 = (Fp::from_literal(2), Seq::from_vec(vec![2, 0]));
    let t5 = (Fp::from_literal(2), Seq::from_vec(vec![0, 1]));

    // the multivariate poly
    let p = Seq::from_vec(vec![t1, t2, t3, t4, t5]);
    // input values x=2 and y=5
    let i = Seq::from_vec(vec![Fp::TWO(), Fp::from_literal(5)]);
    // check that there are 5 terms, t1 through t5
    assert_eq!(p.len(), 5);
    // evaluate the poly
    let res = eval_multi_poly(p, i);
    // check the result
    assert_eq!(res, Fp::from_literal(299));
}

#[cfg(test)]
#[test]
fn test_multi_to_uni_poly() {
    // 1 + 3xy + 5x*y^2 + 2x^2 + 2y
    let t1 = (Fp::from_literal(1), Seq::from_vec(vec![0, 0]));
    let t2 = (Fp::from_literal(3), Seq::from_vec(vec![1, 1]));
    let t3 = (Fp::from_literal(5), Seq::from_vec(vec![1, 2]));
    let t4 = (Fp::from_literal(2), Seq::from_vec(vec![2, 0]));
    let t5 = (Fp::from_literal(2), Seq::from_vec(vec![0, 1]));

    // the multivariate poly
    let p = Seq::from_vec(vec![t1, t2, t3, t4, t5]);
    // input value for y (2nd var), do not eval for x (1st var)
    let i1 = Seq::from_vec(vec![(false, Fp::ZERO()), (true, Fp::from_literal(5))]);
    // 11 + 140x + 2x^2
    let u = multi_to_uni_poly(p, i1);
    assert_eq!(u[0], Fp::from_literal(11));
    assert_eq!(u[1], Fp::from_literal(140));
    assert_eq!(u[2], Fp::from_literal(2));
}

#[cfg(test)]
#[test]
fn test_trim_poly() {
    let p = Seq::from_vec(vec![
        Fp::ZERO(),
        Fp::from_literal(6),
        Fp::from_literal(4),
        Fp::ZERO(),
        Fp::ZERO(),
        Fp::from_literal(2),
        Fp::ZERO(),
        Fp::ZERO(),
        Fp::ZERO(),
    ]);

    let trimmed_p = trim_poly(p.clone());
    assert_eq!(trimmed_p.len(), p.len() - 3);
}

#[cfg(test)]
#[test]
fn test_mult_poly_st() {
    let p = Seq::from_vec(vec![
        Fp::from_literal(5),
        Fp::from_literal(1),
        Fp::from_literal(3),
    ]);
    let single_term = Seq::from_vec(vec![
        Fp::ZERO(),
        Fp::ZERO(),
        Fp::ZERO(),
        Fp::from_literal(3),
    ]);

    let res = multiply_poly_by_single_term(p, single_term);
    assert_eq!(res[0], Fp::ZERO());
    assert_eq!(res[1], Fp::ZERO());
    assert_eq!(res[2], Fp::ZERO());
    assert_eq!(res[3], Fp::from_literal(15));
    assert_eq!(res[4], Fp::from_literal(3));
    assert_eq!(res[5], Fp::from_literal(9));
}

#[cfg(test)]
#[test]
fn test_poly_div() {
    let n = Seq::from_vec(vec![Fp::ZERO(), Fp::ZERO(), Fp::ONE()]);
    let d = Seq::from_vec(vec![Fp::ZERO(), Fp::ONE()]);

    let (q, r) = divide_poly(n, d);
    assert_eq!(q.len(), 2);
    assert_eq!(q[0], Fp::ZERO());
    assert_eq!(q[1], Fp::ONE());
    assert!(!check_not_zero(r));

    let n = Seq::from_vec(vec![
        Fp::from_literal(4),
        Fp::from_literal(8),
        Fp::from_literal(3),
    ]);
    let d = Seq::from_vec(vec![Fp::TWO(), Fp::from_literal(3)]);

    let (q, r) = divide_poly(n, d);
    assert_eq!(q.len(), 2);
    assert_eq!(q[0], Fp::TWO());
    assert_eq!(q[1], Fp::ONE());
    assert!(!check_not_zero(r));
}

#[cfg(test)]
#[quickcheck]
// fn test_vanishing_poly(omega_value:u128, n: u128){
fn test_vanishing_poly(omega_value: u128, n: u128) {
    let omega: Fp = Fp::from_literal((omega_value % 50) + 1);
    let n = n % 20 + 2;
    let vanishing_poly = compute_vanishing_polynomial(omega, n);
    for i in 0..(n - 1) {
        let should_be_zero = eval_polyx(vanishing_poly.clone(), omega.pow(i));
        assert_eq!(should_be_zero, Fp::ZERO())
    }
}

#[cfg(test)]
#[test]
fn scratch() {
    /*
     * let n = 2^2 = 4
     * then ω = 2 is 4 prime root of unity over F_5
     *
     * (since:
     * 2^4 mod 5 = 16 mod 5 = 1 and
     * 2^1 mod 5 = 2 != 1 and
     * 2^2 mod 5 = 4 != 1 and
     * 2^3 mod 5 = 3 != 1)
     *
     * | i | ω^i | a_0 | a_1 | a_2 | q_add |
     * |---|-----|-----|-----|-----|-------|
     * | 0 | 1   | 2   | 3   | 5   | 1     |
     * | 1 | 2   | 10  |     |     | 0     |
     * | 2 | 4   | 5   | 8   | 13  | 1     |
     * | 3 | 8   | 26  |     |     | 0     |
     *
     * then, g(X) = q_add(X) * (a_0(X) + a_1(X) + a_2(X) - a_0(ωX))
     * and g(ω^i) = 0 for all i in [0,n) (should hold)
     *
     *
     * (n_g - 2 = 2 ??? )
     */
    let n = 4;
    let n_a = 3;
    let omega = Fp::from_literal(2);
    let crs: CRS = (
        Seq::<G1>::from_vec(vec![
            g1mul(Fp::from_literal(22), g1_generator()),
            g1mul(Fp::from_literal(7), g1_generator()),
            g1mul(Fp::from_literal(9), g1_generator()),
            g1mul(Fp::from_literal(43), g1_generator()),
        ]),
        g1mul(Fp::from_literal(123), g1_generator()),
    );

    let r_poly = Seq::<Fp>::from_vec(vec![
        Fp::from_literal(987),
        Fp::from_literal(2),
        Fp::from_literal(64),
        Fp::from_literal(355),
    ]);
    let R_blind = Fp::from_literal(78);
    let R = commit_polyx(&crs, r_poly.clone(), R_blind);

    let p = Seq::<Seq<u128>>::from_vec(vec![
        Seq::<u128>::from_vec(vec![0, 1]),
        Seq::<u128>::from_vec(vec![0]),
        Seq::<u128>::from_vec(vec![0]),
    ]);

    let a0_points = Seq::<(Fp, Fp)>::from_vec(vec![
        (Fp::from_literal(1), Fp::from_literal(2)),
        (Fp::from_literal(2), Fp::from_literal(10)),
        (Fp::from_literal(4), Fp::from_literal(5)),
        (Fp::from_literal(8), Fp::from_literal(26)),
    ]);

    let a1_points = Seq::<(Fp, Fp)>::from_vec(vec![
        (Fp::from_literal(1), Fp::from_literal(3)),
        (Fp::from_literal(4), Fp::from_literal(8)),
    ]);

    let a2_points = Seq::<(Fp, Fp)>::from_vec(vec![
        (Fp::from_literal(1), Fp::from_literal(5)),
        (Fp::from_literal(4), Fp::from_literal(13)),
    ]);

    let q_add_points = Seq::<(Fp, Fp)>::from_vec(vec![
        (Fp::from_literal(1), Fp::from_literal(1)),
        (Fp::from_literal(2), Fp::from_literal(0)),
        (Fp::from_literal(4), Fp::from_literal(1)),
        (Fp::from_literal(8), Fp::from_literal(0)),
    ]);

    let a_0 = legrange_poly(a0_points);
    let a_1 = legrange_poly(a1_points);
    let a_2 = legrange_poly(a2_points);
    let q_add = legrange_poly(q_add_points);

    // construct A_i's (commitments)
    let A_0_blinding = Fp::from_literal(99);
    let A_0 = commit_polyx(&crs, a_0.clone(), A_0_blinding);
    let A_1_blinding = Fp::from_literal(123);
    let A_1 = commit_polyx(&crs, a_1.clone(), A_1_blinding);
    let A_2_blinding = Fp::from_literal(748);
    let A_2 = commit_polyx(&crs, a_2.clone(), A_2_blinding);
    let A_list = Seq::<G1>::from_vec(vec![A_0, A_1, A_2]);

    // construct g'(X) = q_add(X) * (a_0(X)+a_1(X)+a_2(X)-a_0(omega * X))
    let mut g_prime = add_polyx(a_0.clone(), a_1.clone());
    g_prime = add_polyx(g_prime, a_2.clone());
    let a_0_rotated = rotate_polyx(a_0.clone(), omega, n);
    g_prime = sub_polyx(g_prime, a_0_rotated);
    g_prime = mul_polyx(g_prime, q_add);
    for i in 0..4 {
        assert_eq!(eval_polyx(g_prime.clone(), omega.pow(i)), Fp::ZERO());
    }

    let h = step_4(g_prime, omega, n);
    let h_is = step_5(h, n);
    let r_seq = Seq::<Fp>::from_vec(vec![Fp::from_literal(5), Fp::from_literal(76)]);
    let H_is = step_6(h_is.clone(), &crs, r_seq);
    let x_challenge = Fp::from_literal(345);
    let H_prime = step_7(H_is, x_challenge, n);
    let h_prime = step_8(h_is, x_challenge, n);
    let a_primes = Seq::<Seq<Fp>>::from_vec(vec![a_0, a_1, a_2]);
    let (r, a_is) = step_9(r_poly, a_primes, n_a, omega, p, x_challenge);
    let x1_challenge = Fp::from_literal(475);
    // let Q_is = step_11(n_a, x1_challenge, H_prime, R, A_list);
}

// fn test_vanishing_poly(omega_value:u128, n: u128){
// #[cfg(test)]
// #[quickcheck]
// fn test_step_4(omega_value:u128, n: u128, r: u128){
//     let vanishing_poly_degree = n%50+5;
//     let g_prime_degree = n%100+55;
//     let mut r = r;

// fn test_add_poly_x() {
// let omega: Fp = Fp::from_literal((omega_value % 50) + 1);
// let n = n % 20 + 2;
// let vanishing_poly = compute_vanishing_polynomial(omega, n);
// for i in 0..(n - 1) {
//     let should_be_zero = eval_polyx(vanishing_poly.clone(), omega.pow(i));
//     assert_eq!(should_be_zero, Fp::ZERO())
// }

// fn test_add_poly_x() {
//     let omega: Fp = Fp::from_literal((omega_value % 50) + 1);
//     let n = n % 20 + 2;
//     let vanishing_poly = compute_vanishing_polynomial(omega, n);
//     for i in 0..(n - 1) {
//         let should_be_zero = eval_polyx(vanishing_poly.clone(), omega.pow(i));
//         assert_eq!(should_be_zero, Fp::ZERO())
//     }
// }

//TESTS MISSING:::::
// add_poly_x
// sub_poly_x
// all other poly functions only have 1 unit test...
