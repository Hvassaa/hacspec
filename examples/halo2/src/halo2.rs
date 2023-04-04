use hacspec_lib::*;
use hacspec_pasta::*;
use hacspec_sha256::*;

fn halo2() {
    // step 1
    // dummy values
    let a: Seq<Seq<Term>> = Seq::<Seq<Term>>::create(0);
    let crs = CRS(Seq::<G1>::create(0), G1::default());
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

    res
}

/// Subtract two polynomials, return resulting polynomial
///
/// # Arguments
///
/// * `p1` - the LHS polynomial
/// * `p2` - the RHS polynomial
fn sub_polyx(p1: Seq<Fp>, p2: Seq<Fp>) -> Seq<Fp> {
    let mut res = p1.clone();

    for i in 0..p2.len() {
        res[i] = p1[i] - p2[i];
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
fn poly_degree(p: Seq<Fp>) -> u32 {
    let len = p.len();
    if len == 0 {
        0
    } else {
        (len as u32) - 1
    }
}

/// Get the sum of all coefficietns of a polynomial
/// (useful for checking if a polynomial is 0)
///
/// # Arguments
///
/// * `p` - the polynomial
fn sum_coeffs(p: Seq<Fp>) -> Fp {
    let mut sum = Fp::ZERO();
    for i in 0..p.len() {
        sum = sum + p[i];
    }

    sum
}

// Trim a polynomial of trailing zeros (zero-terms) and return it
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

    for i in 0..res.len() {
        res[i] = p[i];
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
/// The algorithm is from <https://en.wikipedia.org/wiki/Polynomial_long_division> and is mainly
/// performed in `divide_poly_helper`.
///
/// The pseudo-code is shown here. The while-loop is replaces by a recursive call in a helper
/// function, since hacspec disallows while-loops.
///
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
///
/// # Arguments
///
/// * `n` - the dividend/enumerator polynomial
/// * `d` - the divisor/denominator polynomial
fn divide_poly(n: Seq<Fp>, d: Seq<Fp>) -> (Seq<Fp>, Seq<Fp>) {
    let q = Seq::<Fp>::create(n.len());
    let r = n.clone();
    divide_poly_helper(n, d, q, r)
}

/// Recursive helper function for `divide_poly`, with the actual algorithm.
/// It should NOT be used directly
///
/// # Arguments
///
/// * `n` - the dividend/enumerator polynomial
/// * `d` - the divisor/denominator polynomial
/// * `q` - the algorithm's current `q` value (in the recursion)
/// * `r` - the algorithm's current `r` value (in the recursion)
fn divide_poly_helper(n: Seq<Fp>, d: Seq<Fp>, q: Seq<Fp>, r: Seq<Fp>) -> (Seq<Fp>, Seq<Fp>) {
    if sum_coeffs(r.clone()) != Fp::ZERO() && poly_degree(r.clone()) >= poly_degree(d.clone()) {
        let t = divide_leading_terms(r.clone(), d.clone());
        let q = add_polyx(q, t.clone());
        let aux_prod = multiply_poly_by_single_term(d.clone(), t);
        let r = sub_polyx(r, aux_prod);
        divide_poly_helper(n, d, q, r)
    } else {
        (trim_poly(q), trim_poly(r))
    }
}

struct PublicParams(
    Seq<G1>, // G: G in G^d
    G1,      // U in G
    G1,      // W in G
);
/// Commen Reference Struct
/// This struct is a global variable for the prooving system and holds values used in the commitment schemes
/// 
/// # Elements
/// * `[0]`: Seq<G1> ∈ Gᵈ (vector of random elems.)
/// * `[1]`: G1 in G (random group element)
struct CRS(
    // G,  // G: group of prime-order p
    Seq<G1>, // g: g in G^d (vector of random elems.)
    G1,      // H: H in G (random group element)
             // Fp, // Fp: finite field order p
);

// primarily for multivariate polys
type Term = (Fp, Seq<u32>);
type InputVar = (bool, Fp);

/// Evaluate a term with specified variable inputs
/// Helper function for reduce_multi_poly
///
/// # Arguments
///
/// * `term` - the term
fn reduce_multi_term(term: Term, inputs: Seq<InputVar>, new_size: usize) -> Term {
    let (coef, powers) = term;

    let mut new_coef = coef; //First entry in a term sequence is the Coefficient
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
    // only checking the 1st term for brevity
    // assert_eq!(
    //     p.iter().next().unwrap().1.len(),
    //     inputs.len(),
    //     "no. of inputs should match length of variables"
    // );

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
            let term = p[i].clone();
            let (coef, _) = reduce_multi_term(term, inputs.clone(), unevaluated_variables);
            constant = constant + coef;
        }
    } else {
        //check if term can be evaluated, else insert term in new poly
        for i in 0..p.len() {
            let term = p[i].clone();
            let (coef, powers) = reduce_multi_term(term, inputs.clone(), unevaluated_variables);
            let mut all_powers_zero = true;
            for i in 0..powers.len() {
                if powers[i] != 0 {
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

/// Multiscalar multiplicatoin, auxiliry function for Pedersen vector commitment
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

/// Pedersen vector commitment (1.3 in protocol)
///
/// # Arguments
///
/// * `crs` - the common reference string
/// * `a` - the "vector"
/// * `r` - the "randomness"
fn commit_polyx(crs: &CRS, a: Seq<Fp>, r: Fp) -> G1 {
    let CRS(g, h) = crs;

    let lhs = msm(a, g.clone());
    let rhs = g1mul(r, h.clone());
    let res = g1add(lhs, rhs);

    res
}

/// Generates a random polynomial from given randomness using iterating hashing (3 in protocol)
///
/// # Arguments
///
/// * `randomness` - the "randomness"
/// * `size` - the size of the polynomials (the max power -1)
fn random_sample_poly(randomness: ByteSeq, size: usize) -> Seq<Fp> {
    let mut s = Seq::<Fp>::create(size);
    let mut r = randomness;

    for i in 0..size {
        let digest = hash(&r);
        let hex = digest.to_hex();
        r = ByteSeq::from_hex(&hex);

        s[i] = Fp::from_byte_seq_be(&r);
    }

    s
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
    // assert exactly one var. remains un-evaled
    // assert_eq!(
    //     inputs.iter().map(|f| f.0).filter(|f| *f).count(),
    //     inputs.len() - 1
    // );

    // the univariate polynomial, in mutlivariate representation
    let reduced_poly = reduce_multi_poly(p.clone(), inputs);

    // get the highest degree, or 0 (default) if empty
    let mut max_deg = 0;
    for i in 0..reduced_poly.len() {
        let term = reduced_poly[i].clone();
        let powers = term.1;
        let cur_deg = powers[0] as usize;
        if  cur_deg > max_deg {
            max_deg = cur_deg;
        }
    }

    let mut s = Seq::<Fp>::create(max_deg + 1);

    for i in 0..max_deg + 1 {
        // sum the coefficients of terms with same degree (in "x")
        let mut coeff_sum = Fp::ZERO();
        for j in 0..reduced_poly.len() {
            let mut coeff = Fp::ZERO();
            let term = reduced_poly[j].clone();
            let powers = term.1;
            let power = powers[0];
            if power == (i as u32) {
                coeff = term.0;
            }
            coeff_sum = coeff_sum + coeff;
        }

        // set the term with degree i to the corresponding coefficient
        s[i] = coeff_sum;
    }

    s
}

/// 5 (in protocol)
/// split polynomial of degree n_g(n-1)-n up into n_(g-2) polynomials of degree at most n-1
///
/// The prolynomials(represented by vectors) are stored in a vectore.
/// This way the index in the outer vector can act as the i when reproducing the original poly:
/// h(X) = SUM from i=0 to n_(g-1) [xˆ(ni)h_i(x)]
/// Where n is a parameter of the prooving system, and h_i is the ith part of the original poly.
///
/// # Arguments
/// * `p1` Polynomial to be split
/// * `n` defines length of new polynomials (global variable for prooving system)
///
fn split_poly(p1: Seq<Fp>, n: u32) -> Seq<Seq<Fp>> {
    let no_of_parts = (p1.len() + (n - 2) as usize) / ((n - 1) as usize);

    let mut original_index = 0;
    let mut poly_parts: Seq<Seq<Fp>> = Seq::<Seq<Fp>>::create(no_of_parts);
    for i in 0..poly_parts.len() {
        poly_parts[i] = Seq::<Fp>::create((n - 1) as usize);
        for j in 0..poly_parts.len() {
            let mut current_poly_part:Seq<Fp> = Seq::<Fp>::create(no_of_parts);

            if original_index < p1.len() {
                
                current_poly_part[j] = p1[original_index];
                original_index = original_index + 1;
            }
            poly_parts[j] = current_poly_part;
        }
    }
    poly_parts
}

///
///6 (in protocol)
///
/// commit to each h_i polynomial keeping them in the seq to peserve the power (i)
///
/// # Arguments
/// * `poly_parts` A sequence of polynomials to be commited to
/// * `crs` Commen Refernce Struct (Global variable for prooving system)
/// * `r_seq`Sequence of random elements used as blinding factors
/// 
/// # Constraints
/// * `r_seq` should be at least as long as the `poly_parts`
/// 
fn commit_to_poly_parts(poly_parts:Seq<Seq<Fp>>,crs: &CRS, r_seq:Seq<Fp>) -> Seq<G1>{
    let mut commitment_seq:Seq<G1> = Seq::<G1>::create(poly_parts.len());
    for i in 0..poly_parts.len(){
        let commitment = commit_polyx(crs,poly_parts[i].clone(),r_seq[i]);
        commitment_seq[i] = commitment;
    }
    commitment_seq
}

///Executes the summation from step 7 in protocol.
/// It sums the 
// fn step_7(commitment_seq:Seq<G1>,x:Fp){

// }

fn open() {}

// #[cfg(test)]
// extern crate quickcheck;
// #[cfg(test)]
// #[macro_use(quickcheck)]
// extern crate quickcheck_macros;
// #[cfg(test)]
// extern crate polynomial;
//
// #[cfg(test)]
// use quickcheck::*;
#[cfg(test)]
#[test]
fn test_commit_to_poly_parts() {
    let crs = CRS(
        Seq::<G1>::from_vec(vec![G1::default(), G1::default(), G1::default()]),
        G1::default(),
    );

    let r_seq = Seq::<Fp>::from_vec(vec![Fp::default(), Fp::default(), Fp::default()]);
    let v1 = vec![5, 10, 20]
        .iter()
        .map(|e| Fp::from_literal((*e) as u128))
        .collect();
    let p1 = Seq::from_vec(v1);
    let n = 3;
    let poly_parts = split_poly(p1, n);
    let commitments = commit_to_poly_parts(poly_parts, &crs, r_seq);
    println!("{:?}", commitments)
}

#[cfg(test)]
#[test]
fn test_split_poly() {
    let v1 = vec![5, 10, 20]
        .iter()
        .map(|e| Fp::from_literal((*e) as u128))
        .collect();
    let p1 = Seq::from_vec(v1);
    let n = 3;
    let poly_parts = split_poly(p1, n);
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
fn test_pr() {
    let random = ByteSeq::from_hex("1000");
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
    assert_eq!(sum_coeffs(r), Fp::ZERO());
}
