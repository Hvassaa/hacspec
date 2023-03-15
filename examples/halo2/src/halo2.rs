use hacspec_lib::*;

// univariate polynomial represented as coefficients
// (left-most is lowest power, right-most is highest power)
#[derive(Clone, Debug)]
pub struct UniPolynomial(Seq<u64>);

// evaluate polynomial "p" at point "x"
pub fn eval_uni_poly(p: UniPolynomial, x: u64) -> u64 {
    let mut res: u64 = 0;
    let UniPolynomial(s) = p;
    s.iter().enumerate().for_each(|(i, c)| {
        res += x.pow(i as u32) * c;
    });

    res
}

// multiply polynomial "p" by scalar "x"
pub fn mult_uni_poly_scalar(p: UniPolynomial, x: u64) -> UniPolynomial {
    let UniPolynomial(s) = p;
    let mut res = s.clone();

    s.iter().enumerate().for_each(|(i, _)| {
        res[i] *= x;
    });

    UniPolynomial(res)
}

// add polynomial "p" and polynomial "q"
pub fn add_uni_polys(p: UniPolynomial, q: UniPolynomial) -> UniPolynomial {
    let UniPolynomial(s1) = p;
    let UniPolynomial(s2) = q;
    let mut res = s1.clone();

    s1.iter().enumerate().for_each(|(i, _)| {
        res[i] = s1[i] + s2[i];
    });

    UniPolynomial(res)
}

#[cfg(test)]
extern crate quickcheck;
#[cfg(test)]
#[macro_use(quickcheck)]
extern crate quickcheck_macros;
#[cfg(test)]
extern crate polynomial;

#[cfg(test)]
use quickcheck::*;

#[cfg(test)]
impl Arbitrary for UniPolynomial {
    fn arbitrary(g: &mut quickcheck::Gen) -> UniPolynomial {
        // since evaluating polynomials, we need to limit the size a bit
        // (or a couple of bits) :-)
        let size = 10; // here
        let mut v = vec![];
        for _ in 0..size {
            v.push(u8::arbitrary(g) as u64); // and here
        }

        UniPolynomial(Seq::<u64>::from_vec(v))
    }
}

#[cfg(test)]
#[quickcheck]
fn test_eval_polynomial(a: UniPolynomial) -> bool {
    let point = 7;
    let a2 = a.clone();
    let UniPolynomial(s) = a;
    let p = polynomial::Polynomial::new(s.native_slice().to_vec());
    let home = eval_uni_poly(a2, point);
    let away = p.eval(point);
    home == away
}
