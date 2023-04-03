use hacspec_lib::*;
use hacspec_pasta::{g1add, g1mul, Fp, FpCurve, G1};
use hacspec_sha256::{hash, Sha256Digest};

fn halo2() {
    // step 1
    // dummy values
    let a: Seq<Seq<Term>> = Seq::new(0);
    let crs = CRS(Seq::new(0), G1::default());
    let r = Fp::default();

    for j in 0..a.len() {
        let aj = &a[j];
        let aj_prime = multi_to_uni_poly(aj, Seq::new(0)); // dummy inputs
        let cAj = commit_polyx(&crs, aj_prime, r);
        // generate challenge cj
    }

    // step 2
    // dummy values
    let g: &Seq<Term> = &Seq::new(0);

    let g_prime = multi_to_uni_poly(g, Seq::new(0)); // dummy inputs

    // step 3
    let cR = commit_polyx(&crs, g_prime, r); // TODO update r?
}

fn add_polyx(p1: Seq<Fp>, p2: Seq<Fp>) -> Seq<Fp> {
    let mut res;
    let short_len;

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

fn sub_polyx(p1: Seq<Fp>, p2: Seq<Fp>) -> Seq<Fp> {
    let mut res = p1.clone();

    for i in 0..p2.len() {
        res[i] = p1[i] - p2[i];
    }

    trim_poly(res)
}

fn mul_scalar_polyx(p1: Seq<Fp>, s: Fp) -> Seq<Fp> {
    let mut res = p1.clone();

    for i in 0..res.len() {
        res[i] = p1[i] * s;
    }

    res
}

fn eval_polyx(p1: Seq<Fp>, x: Fp) -> Fp {
    let mut res = Fp::ZERO();

    for i in 0..p1.len() {
        res = res + p1[i] * x.exp(i as u32);
    }

    res
}

fn uni_deg(p1: Seq<Fp>) -> u32 {
    let len = p1.len();
    if len == 0 {
        0
    } else {
        (len as u32) - 1
    }
}

fn sum_coeffs(p: Seq<Fp>) -> Fp {
    let mut sum = Fp::ZERO();
    for i in 0..p.len() {
        sum = sum + p[i];
    }

    sum
}

// trim a polynomial of trailing zeros (zero-terms)
fn trim_poly(p: Seq<Fp>) -> Seq<Fp> {
    let mut last_val_idx = 0;
    for i in 0..p.len() {
        if p[i] != Fp::ZERO() {
            last_val_idx = i;
        }
    }
    let mut res = Seq::create(last_val_idx + 1);

    for i in 0..res.len() {
        res[i] = p[i];
    }

    res
}

fn divide_leading_terms(n: Seq<Fp>, d: Seq<Fp>) -> Seq<Fp> {
    let n = trim_poly(n);
    let d = trim_poly(d);
    let x_pow = n.len() - d.len();
    let n_coeff = n[n.len() - 1];
    let d_coeff = d[d.len() - 1];
    let coeff = n_coeff / d_coeff;
    let mut res = Seq::create(x_pow + 1);
    res[x_pow] = coeff;

    res
}

fn multiply_poly_by_single_term(p: Seq<Fp>, single_term: Seq<Fp>) -> Seq<Fp> {
    let single_term = trim_poly(single_term);
    let st_len = single_term.len() - 1;
    let coef = single_term[st_len];
    let mut res = Seq::create(p.len() + st_len);
    for i in st_len..res.len() {
        res[i] = p[i - st_len] * coef;
    }

    res
}

/*
 * long division code taken from https://en.wikipedia.org/wiki/Polynomial_long_division
 *
 * pseudo code here:
 * function n / d is
 *  require d ≠ 0
 *  q ← 0
 *  r ← n             // At each step n = d × q + r

 *  while r ≠ 0 and degree(r) ≥ degree(d) do
 *      t ← lead(r) / lead(d)       // Divide the leading terms
 *      q ← q + t
 *      r ← r − t × d

 *  return (q, r)
 */
fn poly_divide(n: Seq<Fp>, d: Seq<Fp>) -> (Seq<Fp>, Seq<Fp>) {
    let mut q = Seq::new(n.len());
    let mut r = n.clone();

    while sum_coeffs(r.clone()) != Fp::ZERO() && uni_deg(r.clone()) >= uni_deg(d.clone()) {
        let t = divide_leading_terms(r.clone(), d.clone());
        q = add_polyx(q, t.clone());
        let aux_prod = multiply_poly_by_single_term(d.clone(), t);
        r = sub_polyx(r, aux_prod);
    }

    (trim_poly(q), trim_poly(r))
}

struct PublicParams(
    Seq<G1>, // G: G in G^d
    G1,      // U in G
    G1,      // W in G
);

struct CRS(
    // G,  // G: group of prime-order p
    Seq<G1>, // g: g in G^d (vector of random elems.)
    G1,      // H: H in G (random group element)
             // Fp, // Fp: finite field order p
);

// primarily for multivariate polys
type Term = (Fp, Seq<u32>);
type InputVar = (bool, Fp);

/*
 * Helper function for reduce_multi_poly
 *
 * evaluates a term with on and with the specified variable inputs
 */
fn reduce_multi_term(term: Term, inputs: &Seq<InputVar>, new_size: usize) -> Term {
    let (coef, powers) = term;

    let mut new_coef = coef; //First entry in a term sequence is the Coefficient
    let mut new_powers = Seq::new(new_size);

    let mut idx = 0;
    for i in 0..powers.len() {
        let power = powers[i];
        let input = inputs[i];

        match input {
            (true, p) => {
                let val = p.exp(power);
                new_coef = new_coef * val;
            }
            (false, _) => {
                new_powers[idx] = power;
                idx += 1;
            }
        }
    }

    return (new_coef, new_powers);
}

/*
 * p1 is the polynomial, expressed as a sequence of 2-tuples.
 *
 * Each tuple has the coefficient and a sequence of powers, where the i'th entry is the power of
 * the i'th variable in this term
 *
 * inputs is input values of for the variables. The boolean indicates whether the corresponding
 * variable should be evaluated or not
 *
 * the length of inputs and all sequences of powers in p1 should be equal
 *
 * The output is a new polynomial, with the evaluated variables removed. If all variables are
 * evaluated there will be a single term, with a coefficient (which is the final evaluation) and an
 * empty sequence of powers (i.e. no variables)
 */
fn reduce_multi_poly(p1: Seq<(Fp, Seq<u32>)>, inputs: Seq<InputVar>) -> Seq<Term> {
    // only checking the 1st term for brevity
    assert_eq!(
        p1.iter().next().unwrap().1.len(),
        inputs.len(),
        "no. of inputs should match length of variables"
    );

    let mut constant = Fp::ZERO();
    let mut unevaluated_variables = 0;
    for i in 0..inputs.len() {
        let input = inputs[i];
        match input {
            (false, _) => {
                unevaluated_variables += 1;
            }
            _ => (),
        }
    }
    let mut new_poly = Seq::new(p1.len());
    let mut terms_added = 0;
    if unevaluated_variables == 0 {
        //sum results
        for i in 0..p1.len() {
            let term = p1[i].clone();
            let (coef, _) = reduce_multi_term(term, &inputs, unevaluated_variables);
            constant = constant + coef;
        }
    } else {
        //check if term can be evaluated, else insert term in new poly
        for i in 0..p1.len() {
            let term = p1[i].clone();
            let (coef, powers) = reduce_multi_term(term, &inputs, unevaluated_variables);
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
                terms_added += 1;
            }
        }
    }
    let constant_term = (constant, Seq::<u32>::new(unevaluated_variables));
    new_poly[terms_added] = constant_term;

    new_poly.slice(0, terms_added + 1)
}

/*
 * evaluate a multivariate polynomial
 *
 * p1 is the polynomial, expressed as a sequence of 2-tuples.
 * Each tuple has the coefficient and a sequence of powers, where the i'th entry is the power of
 * the i'th variable in this term
 *
 * inputs are a sequence of field elements, where the i'th entry is the value for the i'th variable
 *
 * outputs a field element, which is the evaluation of the polynomial
 */
fn eval_multi_poly(p1: Seq<Term>, inputs: Seq<Fp>) -> Fp {
    let mut inputvars = Seq::new(inputs.len());
    for i in 0..inputs.len() {
        inputvars[i] = (true, inputs[i]);
    }
    let (res, _) = reduce_multi_poly(p1, inputvars)[0];

    res
}

/* Multiscalar multiplicatoin
 * Auxiliry function for Pedersen vector commitment
 */
fn msm(a: Seq<Fp>, g: &Seq<G1>) -> G1 {
    let mut res = g1mul(a[0], g[0]);
    for i in 1..a.len() {
        res = g1add(res, g1mul(a[i], g[i]));
    }

    res
}

/* 1.3 (in protocol)
 * Pedersen vector commitment
*/
fn commit_polyx(crs: &CRS, a: Seq<Fp>, r: Fp) -> G1 {
    let CRS(g, h) = crs;

    let lhs = msm(a, g);
    let rhs = g1mul(r, *h);
    let res = g1add(lhs, rhs);

    res
}

/* 3 (in protocol)
 * Generates a random polynomial from given randomness using iterating hashing
 */
fn random_sample_poly(randomness: ByteSeq, size: usize) -> Seq<Fp> {
    let mut s = Seq::new(size);
    let mut r = randomness;

    for i in 0..size {
        let digest = hash(&r);
        let hex = digest.to_hex();
        r = ByteSeq::from_hex(&hex);

        s[i] = Fp::from_byte_seq_be(&r);
    }

    s
}

/*
 * 1.1 (in protocol)
 * evaluate a multivariate polynomial in variables such that it becomes a univariate polynomial
 *
 * p1 is the polynomial, expressed as a sequence of 2-tuples.
 *
 * Each tuple has the coefficient and a sequence of powers, where the i'th entry is the power of
 * the i'th variable in this term
 *
 * inputs is input values of for the variables. The boolean indicates whether the corresponding
 * variable should be evaluated or not. Exactly one of of these bools should be false.
 *
 * returns a univariate polynomial, represented as a sequence of field elements, where entry i, has
 * degree i in the variable and the coefficient is the entry
 */
fn multi_to_uni_poly(p1: &Seq<Term>, inputs: Seq<InputVar>) -> Seq<Fp> {
    // assert exactly one var. remains un-evaled
    assert_eq!(
        inputs.iter().map(|f| f.0).filter(|f| *f).count(),
        inputs.len() - 1
    );

    // the univariate polynomial, in mutlivariate representation
    let reduced_poly = reduce_multi_poly(p1.clone(), inputs);

    // get the highest degree, or 0 (default) if empty
    let max = reduced_poly
        .iter()
        .map(|f| f.1[0] as usize)
        .reduce(|acc, curr| if curr > acc { curr } else { acc })
        .unwrap_or_default();

    let mut s = Seq::new(max + 1);

    for i in 0..max + 1 {
        // sum the coefficients of terms with same degree (in "x")
        let coeff_sum = reduced_poly
            .iter()
            .filter(|f| f.1[0] == (i as u32))
            .map(|f| f.0)
            .reduce(|acc, cur| acc + cur)
            .unwrap_or(Fp::from_literal(0));

        // set the term with degree i to the corresponding coefficient
        s[i] = coeff_sum;
    }

    s
}

/*
    5 (in protocol)
    split polynomial of degree n_g(n-1)-n up into n_(g-2) polynomials of degree at most n-1

    The prolynomials(represented by vectors) are stored in a vectore.
    This way the index in the outer vector can act as the i when reproducing the original poly:
    h(X) = SUM from i=0 to n_(g-1) [xˆ(ni)h_i(x)]
    Where n is a parameter of the prooving system, and h_i is the ith part of the original poly.
 */
fn split_poly(p1: Seq<Fp>, n: u32)->Seq<Seq<Fp>>{
    let no_of_parts = (p1.len()+ (n-2) as usize) / ((n-1) as usize);

    let mut original_index = 0;
    let mut poly_parts:Seq<Seq<Fp>> = Seq::create(no_of_parts);
    for i in 0..poly_parts.len(){
        poly_parts[i] = Seq::create((n-1)as usize);
        for j in 0..poly_parts.len(){
            if original_index < p1.len(){
                poly_parts[i][j] = p1[original_index];
                original_index += 1;
            }
        }
    }
    return poly_parts;
}

/*
    6 (in protocol)

    commit to each h_i polynomial keeping them in the seq to peserve the power (i)

    WE NEED TO THINK ABOUT THE RANDOMNESS:))))
 */
fn commit_to_poly_parts(poly_parts:Seq<Seq<Fp>>,crs: &CRS) -> Seq<G1>{
    let mut commitment_seq:Seq<G1> = Seq::create(poly_parts.len());
    // DUMMY VALUE FOR RANDOMNESS
    let r = Fp::default();
    for i in 0..poly_parts.len(){
        let commitment = commit_polyx(crs,poly_parts[i].clone(),r);
        commitment_seq[i] = commitment;
    }
    return commitment_seq;
}

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
fn test_commit_to_poly_parts(){

    let crs = CRS(Seq::new(0), G1::default());

    let v1 = vec![5, 10, 20]
        .iter()
        .map(|e| Fp::from_literal((*e) as u128))
        .collect();
    let p1 = Seq::from_vec(v1);
    let n = 3;
    let poly_parts = split_poly(p1,n);
    let commitments = commit_to_poly_parts(poly_parts,&crs);
}


#[cfg(test)]
#[test]
fn test_split_poly(){
    let v1 = vec![5, 10, 20]
        .iter()
        .map(|e| Fp::from_literal((*e) as u128))
        .collect();
    let p1 = Seq::from_vec(v1);
    let n = 3;
    let poly_parte = split_poly(p1,n);

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
    let u = multi_to_uni_poly(&p, i1);
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
    let n = Seq::from_vec(vec![
        Fp::ZERO(),
        Fp::ZERO(),
        Fp::ONE(),
    ]);
    let d = Seq::from_vec(vec![
        Fp::ZERO(),
        Fp::ONE(),
    ]);

    let (q, r) = poly_divide(n, d);
    assert_eq!(q.len(), 2);
    assert_eq!(q[0], Fp::ZERO());
    assert_eq!(q[1], Fp::ONE());
    assert_eq!(sum_coeffs(r), Fp::ZERO());
}
