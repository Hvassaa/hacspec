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

impl<T: Numeric + NumericCopy + PartialEq> Polynomial<T> {
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

    fn trim(self) -> Polynomial<T> {
        let len = self.coefficients.len();
        for i in (0..len).rev() {
            if self.coefficients[i] != T::default() {
                return Polynomial {coefficients: self.coefficients.slice(0, i + usize::one())}
            }
        }
        self

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

        Polynomial {coefficients: result}
    }
}

impl<T: Numeric + NumericCopy + PartialEq> Sub for Polynomial<T> {
    type Output = Self;

    fn sub(self, other: Self) -> Self {
        let rhs = other.coefficients;

        let mut neg_rhs = Seq::<T>::create(rhs.len());
        for i in 0..rhs.len() {
            neg_rhs[i] = T::default().sub(rhs[i]);
        }

        return (self.clone() + (Polynomial {coefficients: neg_rhs})).trim();
    }
}

impl<T: Numeric + NumericCopy + PartialEq> Mul for Polynomial<T> {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        let lhs = self.coefficients;
        let rhs = rhs.coefficients;
        let mut result = Seq::<T>::create(lhs.len() + rhs.len());
        for i in 0..lhs.len() {
            if !lhs[i].equal(T::default()) {
                for j in 0..rhs.len() {
                    if !rhs[j].equal(T::default()) {
                        result[i + j] = (result[i + j].add(lhs[i] * rhs[j]));
                    }
                }
            }
        }
        (Polynomial {coefficients: result}).trim()
    }

}

impl<T: Numeric + NumericCopy + PartialEq> PartialEq for Polynomial<T> {
    fn eq(&self, other: &Self) -> bool {

        let lhs = &self.clone().trim().coefficients;
        let rhs = &other.clone().trim().coefficients;

        if lhs.len() != rhs.len() {
            false
        } else {
            for i in 0..lhs.len() {
                if lhs[i] != rhs[i] {
                    return false;
                }
            }
            true
        }
    }
}

impl<T: Numeric + NumericCopy + PartialEq> Default for Polynomial<T> {
    /// Constant polynomial with value T::default
    fn default() -> Self {
        Polynomial {coefficients: Seq::<T>::create(1)}
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
        Polynomial {coefficients: Seq::from_vec(v)}
    }
}

#[cfg(test)]
fn constant_one_poly_pallas() -> Polynomial<FpPallas> {
    let mut c = Seq::<FpPallas>::create(1);
    c[usize::zero()] = FpPallas::ONE();
    Polynomial {coefficients: c}
}


// Addition

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

#[cfg(test)]
#[quickcheck]
fn test_poly_add_associativity(p1: Polynomial<FpPallas>, p2: Polynomial<FpPallas>, p3: Polynomial<FpPallas>) {
    let p4 = p1.clone() + p2.clone();
    let p4 = p4.clone() + p3.clone();
    let p5 = p2.clone() + p3.clone();
    let p5 = p5.clone() + p1.clone();
    assert_eq!(p4, p5);
}

// subtraction

#[cfg(test)]
#[quickcheck]
fn test_poly_sub(p1: Polynomial<FpPallas>, p2: Polynomial<FpPallas>, x: u128) {
    let x = FpPallas::from_literal(x);
    let sum_poly = p1.clone() - p2.clone();

    let expected = p1.evaluate(x) - p2.evaluate(x);
    let actual = sum_poly.evaluate(x);
    assert_eq!(expected, actual);
}

// Multiplication

#[cfg(test)]
#[quickcheck]
fn test_poly_mul_logic(p1: Polynomial<FpPallas>, p2: Polynomial<FpPallas>, x: u128) {
    let x = FpPallas::from_literal(x);
    let mul_poly = p1.clone() * p2.clone();

    let expected = p1.evaluate(x) * p2.evaluate(x);
    let actual = mul_poly.evaluate(x);
    assert_eq!(expected, actual);
}

#[cfg(test)]
#[quickcheck]
fn test_poly_mul_closure(p1: Polynomial<FpPallas>, p2: Polynomial<FpPallas>) {
    let p3 = p1 * p2;
}

#[cfg(test)]
#[quickcheck]
fn test_poly_mul_associativity(p1: Polynomial<FpPallas>, p2: Polynomial<FpPallas>, p3: Polynomial<FpPallas>) {
    let p4 = p1.clone() * p2.clone();
    let p4 = p4.clone() * p3.clone();
    let p5 = p2.clone() * p3.clone();
    let p5 = p5.clone() * p1.clone();
    assert_eq!(p4, p5);
}

#[cfg(test)]
#[quickcheck]
fn test_poly_mul_identity(p1: Polynomial<FpPallas>) {
    let mut const_one_poly = constant_one_poly_pallas();

    let p2 = p1.clone() * const_one_poly.clone();
    let p3 = const_one_poly.clone() * p1.clone();

    println!("const {:?}\np1 {:?}\np2 {:?}\np3 {:?}", const_one_poly, p1, p2, p3);
    assert_eq!(p1, p2);
    assert_eq!(p2, p3);
}

#[cfg(test)]
#[quickcheck]
fn test_poly_mul_cummutativity(p1: Polynomial<FpPallas>, p2: Polynomial<FpPallas>) {
    let p3 = p1.clone() * p2.clone();
    let p4 = p2 * p1.clone();
    assert_eq!(p3, p4);
}

#[cfg(test)]
#[quickcheck]
fn test_poly_mul_left_distributive(p1: Polynomial<FpPallas>, p2: Polynomial<FpPallas>, p3: Polynomial<FpPallas>) {
    let p4 = p1.clone() * (p2.clone() + p3.clone());
    let p5 = (p1.clone() * p2) + (p1 * p3);
    assert_eq!(p4, p5);
}
