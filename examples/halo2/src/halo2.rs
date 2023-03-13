use hacspec_lib::*;

// univariate polynomial represented as coefficients
// (left-most is lowest power, right-most is highest power)
#[derive(Clone, Debug)]
pub struct UniPolynomial(Seq<u32>);

pub fn eval_u_poly(p: UniPolynomial, x: u32) -> u32 {
    let mut res: u32 = 0;
    let UniPolynomial(s) = p;
    s.iter().enumerate().for_each(|(i, c)| {
        res += x.pow(i as u32) * c;
    });

    res
}

// TESTS

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
            v.push(u16::arbitrary(g) as u32); // and here
        }

        UniPolynomial(Seq::<u32>::from_vec(v))
    }
}

#[cfg(test)]
#[quickcheck]
fn test_p(a: UniPolynomial) -> bool {
    let a2 = a.clone();
    let UniPolynomial(s) = a;
    let p = polynomial::Polynomial::new(s.native_slice().to_vec());
    let home = eval_u_poly(a2, 2);
    let away = p.eval(2);
    home == away
}
