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

    // do the subtraction on constant term
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
/// * No two points may have the same x-value
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
/// * `r` - the "randomness"
fn commit_polyx(crs: &CRS, a: Seq<Fp>, r: Fp) -> G1 {
    let (g, h) = crs;
    let (f1, f2, b) = h;

    let lhs = msm(a, g.clone());
    let rhs = g1mul(r, (f1.clone(), f2.clone(), b.clone()));
    let res = g1add(lhs, rhs);

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
/// * `q` - q, from the protocol represented as seqs of (i, set), s.t. q_i = set
fn sigma(i: u128, q: Seq<(u128, Seq<u128>)>) -> Seq<u128> {
    /// TODO this is dummy
    let mut res = Seq::<u128>::create(0);
    for j in 0..q.len() {
        let maybe_i = q[j].0;
        let maybe_res = q[j].1.clone();
        if i == maybe_i {
            res = maybe_res;
        }
    }

    res
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
fn calculate_L_or_R(p_part: Seq<Fp>, b_part: Seq<Fp>, g_part: Seq<G1>, z: Fp, U: G1, W: G1) -> G1 {
    // <p'_part, G'_part>
    let p_g_msm = msm(p_part.clone(), g_part);

    let p_b_ip = inner_product(p_part, b_part);
    let z_ip = z * p_b_ip;
    // [z<p'_part, b_part>]U
    let z_ip_U = g1mul(z_ip, U);

    let r = Fp::ZERO(); // TODO use real randomness

    // [*]W
    let multed_W = g1mul(r, W);

    // calculate part j (L_j or R_j)
    let mut part_j = g1add(p_g_msm, z_ip_U);
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

    let mut poly_parts: Seq<Seq<Fp>> = Seq::<Seq<Fp>>::create(no_of_parts);

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
        poly_parts[i] = trim_poly(current_poly_part);
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
/// * `n_e` - Global parameter for the protocol
/// * `n_a` - Global parameter for the protocol
/// * `omega` - The generator for the evaluations points also a global parameter for the protocol
/// * `p` - a list of sets p_i which contains integers from the protocol
/// * `x` - The challenge from step 7
///
///
fn step_9(
    r: Seq<Fp>,
    a_prime_seq: Seq<Seq<Fp>>,
    n_e: usize,
    n_a: usize,
    omega: Fp,
    p: Seq<Seq<u128>>,
    x: Fp,
) -> (Fp, Seq<Seq<Fp>>) {
    let mut a_seq: Seq<Seq<Fp>> = Seq::<Seq<Fp>>::create(n_a);
    for i in 0..n_a {
        let a_prime_i: Seq<Fp> = a_prime_seq[i].clone();
        let mut a_i_seq: Seq<Fp> = Seq::<Fp>::create(n_e);
        let p_i = p[i].clone();
        for j in 0..a_prime_i.len() {
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
/// * `n_e` - n_e from the protocol
///
fn step_10(
    omega: Fp,
    p: Seq<Seq<u128>>,
    x: Fp,
    a: Seq<Seq<Fp>>,
    n_a: u128,
    n_e: u128,
) -> Seq<Seq<Fp>> {
    let mut s = Seq::<Seq<Fp>>::create(n_a as usize);
    for i in 0..n_a as usize {
        let mut points: Seq<(Fp, Fp)> = Seq::<(Fp, Fp)>::create((n_e as usize - 1));
        for j in 0..n_e as usize - 1 {
            let p_i = p[i as usize].clone();
            let p_i_j: u128 = p_i[j as usize];
            let x_j = omega.pow(p_i_j) * x;
            let a_i = a[i as usize].clone();
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
/// * `n_q` - n_q from the protocol
/// * `n_a` - n_a from the protocol
/// * `x1` - challenge 1
/// * `H_prime` - H', the computed sum from step 7
/// * `R` - R, commitment from step 3
/// * `a` - A, the list of hiding commitments for a_i's
/// * `q` - q, from the protocol represented as seqs of (i, set), s.t. q_i = set
fn step_11(
    n_q: u128,
    n_a: u128,
    x1: Fp,
    H_prime: G1,
    R: G1,
    a: Seq<G1>,
    q: Seq<(u128, Seq<u128>)>,
) -> Seq<G1> {
    let nq_minus1 = n_q - (1 as u128); // TODO should not be decremented here, or in the following steps.
    let mut qs = Seq::<G1>::create(nq_minus1 as usize);
    let na_minus1 = n_a - (1 as u128);

    // bullet 1
    for i in 0..(na_minus1 as usize) {
        let a_i = a[i as usize];
        let sigma_i = sigma(i as u128, q.clone());
        // TODO is this what is meant by Q_sigma(i) ?
        for j in 0..sigma_i.len() {
            let j = sigma_i[j];
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
/// * `n_q` - n_q from the protocol
/// * `n_a` - n_a from the protocol
/// * `x1` - challenge 1
/// * `h_prime` - h', the computed polynomial from [step_8]
/// * `r` - the "random" polynomial from [step_3]
/// * `a_prime` - a', the list of univariate polys from [step_1]
/// * `q` - q, from the protocol represented as seqs of (i, set), s.t. q_i = set
fn step_12(
    n_q: u128,
    n_a: u128,
    x1: Fp,
    h_prime: Seq<Fp>,
    r: Seq<Fp>,
    a_prime: Seq<Seq<Fp>>,
    q: Seq<(u128, Seq<u128>)>,
) -> Seq<Seq<Fp>> {
    let nq_minus1 = n_q - (1 as u128);
    let mut qs = Seq::<Seq<Fp>>::create(nq_minus1 as usize);

    // initialize all polys to constant 0
    for i in 0..qs.len() {
        qs[i] = Seq::<Fp>::create(1);
    }

    let na_minus1 = n_a - (1 as u128);

    // bullet 1
    for i in 0..(na_minus1 as usize) {
        let a_i = a_prime[i as usize].clone();
        let sigma_i = sigma(i as u128, q.clone());
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
/// * `n_q` - n_q from the protocol
/// * `n_a` - n_a from the protocol
/// * `n` - n from the protocol
/// * `omega` - omega from the protocol
/// * `x` - the challenge from step 7
/// * `x1` - the challenge from step 11
/// * `r` - r from step 9
/// * `s` - s, the computed polynomials from step 10
/// * `q` - q, from the protocol represented as seqs of (i, set), s.t. q_i = set
/// * `a` - a', the list of univariate polys from step 1
/// * `g_prime` - the polynomial from step 2
fn step_13(
    n_q: u128,
    n_a: u128,
    n: u128,
    omega: Fp,
    x: Fp,
    x1: Fp,
    r: Fp,
    s: Seq<Seq<Fp>>,
    q: Seq<(u128, Seq<u128>)>,
    a: Seq<Seq<Fp>>,
    g_prime: Seq<Fp>,
) -> Seq<Seq<Fp>> {
    let nq_minus1 = n_q - (1 as u128);
    let mut rs = Seq::<Seq<Fp>>::create(nq_minus1 as usize);

    // initialize all polys to constant 0
    for i in 0..rs.len() {
        rs[i] = Seq::<Fp>::create(1);
    }

    let na_minus1 = n_a - (1 as u128);

    // bullet 1
    for i in 0..(na_minus1 as usize) {
        let s_i = s[i as usize].clone();
        let sigma_i = sigma(i as u128, q.clone());
        // TODO is this what is meant by Q_sigma(i) ?
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
/// * `n_q` - n_q from the protocol
/// * `n_e` - n_e from the protocol
/// * `q_polys` - the q polynomials from step 12
/// * `r_polys` - the r polynomials from step 13
/// * `q` - the list of distinct sets of integers containing p_i
/// * `r` - randomness for commiting
fn step_14(
    crs: &CRS,
    x2: Fp,
    n_q: u128,
    n_e: u128,
    q_polys: Seq<Seq<Fp>>,
    r_polys: Seq<Seq<Fp>>,
    q: Seq<Seq<u128>>,
    r: Fp,
) -> G1 {
    let mut q_prime = Seq::<Fp>::create(1); // initialize q' to the constant zero poly

    for i in 0..(n_q as usize) {
        let x2_powered = x2.pow(i as u128);
        let q_i = q_polys[i].clone();
        let r_i = r_polys[i].clone();
        let q_i_sub_r_i = sub_polyx(q_i, r_i);
        let product = Seq::<Fp>::create(0); // TODO make the real divisor poly

        let (divided_poly, remainder) = divide_poly(q_i_sub_r_i, product); // TODO what to do with remainder?
        let multed_poly = mul_scalar_polyx(divided_poly, x2_powered);

        q_prime = add_polyx(q_prime, multed_poly);
    }

    let commitment = commit_polyx(crs, q_prime, r);

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
/// * `n_e` - n_e from the protocol
/// * `omega` - omega from the protocol
/// * `Q_prime` - commitment from step 14
/// * `Q` - list of group-elements from step 11
/// * `u` - list of scalars from step 16
/// * `r` - list of polynomials from step 13
/// * `q` - the list of distinct sets of integers containing p_i

fn step_18(
    x: Fp,
    x1: Fp,
    x2: Fp,
    x3: Fp,
    x4: Fp,
    n_q: u128,
    n_e: u128,
    omega: Fp,
    Q_prime: G1,
    Q: Seq<G1>,
    u: Seq<Fp>,
    r: Seq<Seq<Fp>>,
    q: Seq<Seq<u128>>,
) -> (G1, Fp) {
    let v = Fp::ZERO();

    let mut P_sum = g1_default();
    for i in 0..n_q as usize - 1 {
        let Q_i = Q[i];
        let term = g1mul(x4.pow(i as u128), Q_i);
        P_sum = g1add(P_sum, term)
    }
    P_sum = g1mul(x4, P_sum);
    let P = g1add(Q_prime, P_sum);

    let mut v_first_sum = Fp::ZERO();
    for i in 0..n_q as usize - 1 {
        let x2_i: Fp = x2.pow(i as u128);
        let u_i: Fp = u[i];
        let r_i: Seq<Fp> = r[i].clone();
        let r_i_x3: Fp = eval_polyx(r_i, x3);
        let numerator: Fp = u_i - r_i_x3;
        let mut product: Fp = Fp::ONE();
        for j in 0..n_e as usize - 1 {
            let q_i: Seq<u128> = q[i].clone();
            let q_i_j: u128 = q_i[j];
            let rhs = omega.pow(q_i_j) * x;
            let term = x3 - rhs;
            product = product * term;
        }
        let sum_term: Fp = x2 * (numerator / product);
        v_first_sum = v_first_sum + sum_term;
    }

    let mut v_second_sum: Fp = Fp::ZERO();
    for i in 0..n_q as usize - 1 {
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

    //  Sum_i^nq-1 {x4^i q_i(X)}
    for i in 0..q_polys.len() {
        let x4_powered = x4.pow(i as u128);
        let q_i = q_polys[i].clone();
        let multed_poly = mul_scalar_polyx(q_i, x4_powered);

        p = add_polyx(p, multed_poly)
    }

    // [x4] Sum_i^nq-1 {x4^i q_i(X)}
    p = mul_scalar_polyx(p, x4);

    // q'(X) + [x4] Sum_i^nq-1 {x4^i q_i(X)}
    p = add_polyx(p, q_prime);

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
) -> (Seq<Fp>, Seq<G1>) {
    let mut p_prime = p_prime_poly;
    let mut g_prime = G;
    let mut b = Seq::<Fp>::create(n as usize);
    for i in 0..b.len() {
        let x3_powered = x3.pow(i as u128);
        b[i] = x3_powered;
    }

    for j in 0..k {
        let p_prime_half = p_prime.len() / 2;
        let g_prime_half = g_prime.len() / 2;
        let b_half = b.len() / 2;

        // BULLET 1
        // PROVER WORKS HERE
        let p_prime_hi = p_prime.slice(0, p_prime_half);
        let p_prime_lo = p_prime.slice(p_prime_half, p_prime_half);

        let g_prime_hi = g_prime.slice(0, g_prime_half);
        let g_prime_lo = g_prime.slice(g_prime_half, g_prime_half);

        let b_lo = b.slice(0, b_half);
        let b_hi = b.slice(b_half, b_half);

        // calcuate L_j and R_j, using the right parts of p', G' and b
        let L_j = calculate_L_or_R(p_prime_hi.clone(), b_lo, g_prime_lo.clone(), z, U, W);
        let R_j = calculate_L_or_R(p_prime_lo.clone(), b_hi, g_prime_hi.clone(), z, U, W);

        // BULLET 2
        // VERIFIER WORKS HERE
        let u_j = u[j];

        // BULLET 3
        // VERIFIER & PROVER WORKS HERE
        let mut new_g_prime = Seq::<G1>::create(g_prime_half);
        for i in 0..new_g_prime.len() {
            // TODO, this is entry-wise multiplication and pairwise addition!!!
            let g_prime_hi_indexed = g_prime_hi[i];
            let g_prime_lo_indexed = g_prime_lo[i];
            let rhs_product = g1mul(u_j, g_prime_hi_indexed);
            let sum = g1add(g_prime_lo_indexed, rhs_product);
            new_g_prime[i] = sum;
        }
        g_prime = new_g_prime;

        // BULLET 4
        // PROVER WORKS HERE
        let u_j_inv = u_j.inv();
        let rhs = mul_scalar_polyx(p_prime_hi, u_j_inv);
        let new_p_prime = add_polyx(p_prime_lo, rhs);
        p_prime = new_p_prime;
    }

    (p_prime, g_prime)
}

/// Step 25
///
/// Get the zeroth entry in **p** and synthetic blinding factor f
///
/// # Arguments
/// * `p_prime` - **p**' from [step_24]
/// * `blinding_factors` - the list of all the elided blinding factors
fn step_25(p_prime: Seq<Fp>, blinding_factors: Seq<Fp>) -> (Fp, Fp) {
    let p_prime_0 = p_prime[0];
    // TODO how is f calculated?
    let f = Fp::ZERO();

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

    let rhs = g1add(rhs_term_1, g1add(rhs_term_2, rhs_term_3));

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
#[derive(Clone, Debug)]
struct UniPolynomial(Seq<Fp>);

#[cfg(test)]
impl Arbitrary for UniPolynomial {
    fn arbitrary(g: &mut quickcheck::Gen) -> UniPolynomial {
        let size = u8::arbitrary(g) % 20;
        let mut v = vec![];
        for _ in 0..size {
            v.push(Fp::from_literal(u128::arbitrary(g)));
        }
        UniPolynomial(Seq::<Fp>::from_vec(v))
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
#[quickcheck]
fn test_step_5(h: UniPolynomial, n: u8) -> TestResult {
    let n = n as u128;
    let h = h.0;
    let h = trim_poly(h); // extract polynomial
    if n < 2 {
        // discard if n is too small (step_5 requires a n>2 to make sense)
        TestResult::discard()
    } else {
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
}

#[cfg(test)]
// #[quickcheck]
#[test]
fn test_step_7() {
    // if n < 2 {
    // return TestResult::discard();
    // }
    let n = 5;
    let h = Seq::<Fp>::from_vec(vec![]);
    let n = n as u128;
    // let h = h.0;
    let h = trim_poly(h); // extract polynomial
    let h_parts: Seq<Seq<Fp>> = step_5(h, n);
    let parts_len: &Seq<Fp> = (&h_parts[0]);
    let parts_len = parts_len.len();

    let mut gd = Seq::<G1>::create(parts_len);
    let mut rs = Seq::<Fp>::create(parts_len);
    for i in 0..gd.len() {
        gd[i] = (FpCurve::ONE(), FpCurve::ONE(), false);
        rs[i] = Fp::ONE();
    }

    let crs: CRS = (gd, g1_default());

    let Hs = step_6(h_parts.clone(), &crs, rs);
    let x = Fp::TWO();

    let H_prime = step_7(Hs, x, n);
    let h_prime = step_8(h_parts.clone(), x, n);
    let h_prime_commitment = commit_polyx(&crs, h_prime, Fp::from_literal(h_parts.len() as u128));

    assert_eq!(H_prime, h_prime_commitment);

    // TestResult::passed()
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
fn test_step_9() {
    use std::clone;

    let v1 = vec![1, 1, 1]
        .iter()
        .map(|e| Fp::from_literal((*e) as u128))
        .collect();
    let v2: Vec<Fp> = vec![1, 1, 1]
        .iter()
        .map(|e| Fp::from_literal((*e) as u128))
        .collect();
    let v3: Vec<Fp> = vec![1, 1, 1]
        .iter()
        .map(|e| Fp::from_literal((*e) as u128))
        .collect();
    let p1 = Seq::from_vec(v1);
    let p2: Seq<Fp> = Seq::from_vec(v2);
    let p3: Seq<Fp> = Seq::from_vec(v3);
    let mut a_prime_seq: Seq<Seq<Fp>> = Seq::<Seq<Fp>>::create(3);
    a_prime_seq[0] = p1;
    a_prime_seq[1] = p2;
    a_prime_seq[2] = p3;
    let n_e = 3;
    let x: Fp = Fp::from_literal(1);
    let omega: Fp = Fp::from_literal(2);
    let a_seq: Seq<Seq<Fp>> = step_9(a_prime_seq, n_e, omega, x);
    let a_i_seq: &Seq<Fp> = &a_seq[1];
    assert_eq!(a_i_seq[1], Fp::from_literal(21));
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
#[test]
fn test_step11() {
    // TODO dont use dummy values
    let x1 = Fp::default();
    let a = Seq::<G1>::create(1);
    let n_a = u128::TWO();
    let n_q = u128::TWO();
    let h_prime = g1_default();
    let r = g1_default();
    let q = Seq::create(0);
    step_11(n_a, n_q, x1, h_prime, r, a, q);
}

#[cfg(test)]
#[test]
fn test_step12() {
    // TODO dont use dummy values
    let x1 = Fp::default();
    let a = Seq::create(0);
    let n_a = u128::TWO();
    let n_q = u128::ONE();
    let h_prime = Seq::create(0);
    let r = Seq::create(0);
    let q = Seq::create(0);
    step_12(n_a, n_q, x1, h_prime, r, a, q);
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

// #[cfg(test)]
// #[quickcheck]
// fn test_step_4(omega_value:u128, n: u128, r: u128){
//     let vanishing_poly_degree = n%50+5;
//     let g_prime_degree = n%100+55;
//     let mut r = r;

//     // r cannot be 0 as it would lead to g_prime being all 0
//     if r == 0{
//         r = r+2;
//     }

//     let  omega: Fp = Fp::from_literal((omega_value%50)+1);
//     let g_prime = compute_vanishing_polynomial(omega, g_prime_degree);
//     let g_prime = mul_scalar_polyx(g_prime, Fp::from_literal(r));
//     let h = step_4(g_prime, omega, vanishing_poly_degree);
//     let h_degree = poly_degree(h);
//     let expected_h_degree = g_prime_degree - vanishing_poly_degree;
//     assert_eq!(h_degree,expected_h_degree);
// }
