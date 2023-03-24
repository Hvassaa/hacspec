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
    // step 1
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

// Term for multivariate polynomials
#[derive(Default, Clone)]
struct Term(
    Fp,       // Coefficient
    Seq<u32>, // exponents, s.t. entry i is the i'th variable's exponent
);

fn eval_multi_term(term: (Fp,Seq<u32>), inputs: &Seq<Fp>) -> Fp {
    let (coef,powers) = term;
    let mut res = coef;//First entry in a term sequence is the Coefficient

    for i in 0..powers.len() {
        let power = powers[i];
        let input = inputs[i];
        let val = input.exp(power);
        res = res * val;
    }
    return res;
}

fn eval_multi_polyx(p1: Seq<(Fp, Seq<u32>)>, inputs: Seq<Fp>) -> Fp {
    let mut res = Fp::ZERO();
    for i in 0..p1.len() {
        let term = p1[i].clone();
        let term_val = eval_multi_term(term, &inputs);
        res = res + term_val;
        // res = res + p1[i] * x.exp(i as u32);
    }

    res
}

/* Multiscalar multiplicatoin
 * Auxiliry function for Pedersen vector commitment
 */
fn msm(a: Seq<Fp>, g: Seq<G1>) -> G1 {
    let mut res = g1mul(a[0], g[0]);
    for i in 1..a.len() {
        res = g1add(res, g1mul(a[i], g[i]));
    }

    res
}

/* 1,3
 * Pedersen vector commitment
*/
fn commit_polyx(crs: CRS, a: Seq<Fp>, r: Fp) -> G1 {
    let CRS(G, H) = crs;

    let lhs = msm(a, G);
    let rhs = g1mul(r, H);
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
    println!("{:?}", random_sample_poly(random, 10));
}
