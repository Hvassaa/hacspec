#![allow(non_snake_case)]
#![allow(dead_code)]
#![allow(warnings, unused)]

use hacspec_lib::*;

public_nat_mod!(
    type_name: FpPallas,
    type_of_canvas: PallasCanvas,
    bit_size_of_field: 255,
    modulo_value: "40000000000000000000000000000000224698FC094CF91B992D30ED00000001"
);

struct Polynomial<T: Numeric + NumericCopy + Clone> {
    coefficients: Seq<T>
}

impl<T: Numeric + NumericCopy> Polynomial<T> {
    /// Evaluate a polynomial at point, return the evaluation
    ///
    /// # Arguments
    ///
    /// * `x` - the point
    fn evaluate(self, x: T) -> T {
        let coefficients = self.coefficients;
        let mut result = T::default();

        for i in 0..coefficients.len() {
            result = result + coefficients[i] * x.exp(i as u32);
        }

        result
    }
}

impl<T: Numeric + NumericCopy> Add for Polynomial<T> {
    type Output = Self;

    fn add(self, other: Self) -> Self {
        let lhs = self.coefficients;
        let rhs = other.coefficients;
        let (big, small) = {
            if lhs.len() > rhs.len() {
                (lhs, rhs)
            } else {
                (rhs, lhs)
            }
        };

        let mut result = big.clone();
        for i in 0..small.len() {
            result[i] = result[i].add(small[i]);
        }

        return Polynomial {coefficients: result};
    }
}

// TESTS

#[cfg(test)]
extern crate quickcheck;
#[cfg(test)]
#[macro_use(quickcheck)]
extern crate quickcheck_macros;
#[cfg(test)]
use quickcheck::*;

impl<T: Numeric + NumericCopy> Clone for Polynomial<T> {
    fn clone(&self) -> Self {
        Polynomial {coefficients: self.coefficients.clone()}
    }
}

// Only needed for test/Arbitrary
#[cfg(test)]
impl<T: Numeric + NumericCopy> Debug for Polynomial<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", self.coefficients)
    }
}

#[cfg(test)]
impl Arbitrary for Polynomial<FpPallas> {
    fn arbitrary(g: &mut quickcheck::Gen) -> Polynomial<FpPallas> {
        let size = usize::arbitrary(g) % 20 + 1;
        let mut v: Vec<FpPallas> = vec![];
        for _ in 0..size {
            let new_val = FpPallas::from_literal(u128::arbitrary(g));
            v.push(new_val);
        }
        Polynomial {coefficients: Seq::create(0)}
    }
}

#[cfg(test)]
#[quickcheck]
fn test_poly_add_logic(p1: Polynomial<FpPallas>, p2: Polynomial<FpPallas>, x: usize) {
    let x = FpPallas::from_literal(x as u128);
    let sum_poly = p1.clone() + p2.clone();

    let expected = p1.evaluate(x) + p2.evaluate(x);
    let actual = sum_poly.evaluate(x);
    assert_eq!(expected, actual);
}

#[cfg(test)]
#[quickcheck]
fn test_poly_add_closure(p1: Polynomial<FpPallas>, p2: Polynomial<FpPallas>) {
    let p3 = p1 + p2;
}
