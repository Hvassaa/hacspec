use hacspec_lib::*;
use hacspec_pasta::{g1add, g1mul, Fp, FpCurve, G1};
use hacspec_sha256::{hash, Sha256Digest};

// public_nat_mod!( //Custom Macro - defining a newtype with some functions - well defined macro's have library functions built in
//     type_name: Fp,
//     type_of_canvas: FpCanvas,
//     bit_size_of_field: 258, //381 with 3 extra bits
//     modulo_value: "40000000000000000000000000000000224698fc094cf91b992d30ed00000001" //0x40000000000000000000000000000000224698fc094cf91b992d30ed00000001
// );

fn halo2() {
    // dummy
    let a: Seq<Seq<Term>> = Seq::new(0);
    let crs = CRS(Seq::new(0), G1::default());
    let r = Fp::default();

    // step 1
    for j in 0..a.len() {
        let aj = &a[j];
        let aj_prime = multi_to_uni_poly(aj, Seq::new(0)); // dummy inputs
        let Aj = commit_polyx(&crs, aj_prime, r);
    }

}

fn add_polyx(p1: Seq<FpCurve>, p2: Seq<FpCurve>) -> Seq<FpCurve> {
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

fn mul_scalar_polyx(p1: Seq<FpCurve>, s: FpCurve) -> Seq<FpCurve> {
    let mut res = p1.clone();

    for i in 0..res.len() {
        res[i] = p1[i] * s;
    }

    res
}

fn eval_polyx(p1: Seq<FpCurve>, x: FpCurve) -> FpCurve {
    let mut res = FpCurve::ZERO();

    for i in 0..p1.len() {
        res = res + p1[i] * x.exp(i as u32);
    }

    res
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
fn test_poly_add() {
    let v1 = vec![5, 10, 20]
        .iter()
        .map(|e| FpCurve::from_literal((*e) as u128))
        .collect();
    let v2 = vec![55]
        .iter()
        .map(|e| FpCurve::from_literal((*e) as u128))
        .collect();
    let p1 = Seq::from_vec(v1);
    let p2 = Seq::from_vec(v2);

    let p3 = add_polyx(p1, p2);

    assert_eq!(p3[0], FpCurve::from_literal(60));
    assert_eq!(p3[1], FpCurve::from_literal(10));
    assert_eq!(p3[2], FpCurve::from_literal(20));
}

#[cfg(test)]
#[test]
fn test_poly_mul() {
    let v1 = vec![5, 10, 20]
        .iter()
        .map(|e| FpCurve::from_literal((*e) as u128))
        .collect();
    let p1 = Seq::from_vec(v1);

    let p3 = mul_scalar_polyx(p1, FpCurve::TWO());

    assert_eq!(p3[0], FpCurve::from_literal(10));
    assert_eq!(p3[1], FpCurve::from_literal(20));
    assert_eq!(p3[2], FpCurve::from_literal(40));
}

#[cfg(test)]
#[test]
fn test_poly_eval() {
    let v1 = vec![5, 10, 20]
        .iter()
        .map(|e| FpCurve::from_literal((*e) as u128))
        .collect();
    let p1 = Seq::from_vec(v1);

    assert_eq!(eval_polyx(p1, FpCurve::TWO()), FpCurve::from_literal(105));
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
