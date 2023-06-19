#![allow(non_snake_case)]
#![allow(dead_code)]
#![allow(warnings, unused)]

use hacspec_lib::*;

#[derive(Copy)]
pub struct EllipticCurvePoint<
    T: Numeric + NumericCopy + PartialEq + Integer + hacspec_lib::Div<Output = T>,
> {
    x: T,
    y: T,
    a1: T,
    a2: T,
    a3: T,
    a4: T,
    a5: T,
    a6: T,
    isPointAtInfinity: bool,
    bit_size_of_field: usize,
}

impl<T: Numeric + NumericCopy + PartialEq + Integer + hacspec_lib::Div<Output = T>>
    EllipticCurvePoint<T>
{
    pub fn is_identity(self) -> bool {
        self.isPointAtInfinity
    }
    pub fn double(self) -> EllipticCurvePoint<T> {
        if self.isPointAtInfinity {
            self
        } else {
            let x12 = self.x.exp(2u32);
            let lambda = (T::from_literal(3u128) * x12 + T::TWO() * self.a2 * self.x
                - self.a1 * self.y
                + self.a4)
                / (T::TWO() * self.y + self.a1 * self.x + self.a3);
            let x3 = lambda.exp(2u32) + lambda * self.a1 - self.a2 - T::TWO() * self.x;
            let y3 = lambda * (self.x - x3) - self.y - self.a1 * self.x - self.a3;
            EllipticCurvePoint {
                x: x3,
                y: y3,
                a1: self.a1,
                a2: self.a2,
                a3: self.a3,
                a4: self.a4,
                a5: self.a5,
                a6: self.a6,
                isPointAtInfinity: false,
                bit_size_of_field: self.bit_size_of_field,
            }
        }
    }
    pub fn neg(self) -> EllipticCurvePoint<T> {
        EllipticCurvePoint {
            x: self.x,
            y: T::ZERO() - self.y,
            a1: self.a1,
            a2: self.a2,
            a3: self.a3,
            a4: self.a4,
            a5: self.a5,
            a6: self.a6,
            isPointAtInfinity: self.isPointAtInfinity,
            bit_size_of_field: self.bit_size_of_field,
        }
    }

    pub fn is_on_curve(self) -> bool {
        // point is on the curve IFF
        // the point satisfies the Weiestrass equation:
        // Yˆ2 + a_1XY + a_3Y = xˆ3 + a_2Xˆ2 + a_4X + a_6
        // or it is the point at infinity
        let x = self.x;
        let y = self.y;
        let on_curve = y * y + self.a1 * x * y + self.a3 * y
            == x * x * x + self.a2 * x * x + self.a4 * x + self.a6;

        (on_curve) || self.isPointAtInfinity
    }
}

impl<T: Numeric + NumericCopy + PartialEq + Integer + hacspec_lib::Div<Output = T>> Clone
    for EllipticCurvePoint<T>
{
    fn clone(&self) -> Self {
        EllipticCurvePoint {
            x: self.x,
            y: self.y,
            a1: self.a1,
            a2: self.a2,
            a3: self.a3,
            a4: self.a4,
            a5: self.a5,
            a6: self.a6,
            isPointAtInfinity: self.isPointAtInfinity,
            bit_size_of_field: self.bit_size_of_field,
        }
    }
}

impl<T: Numeric + NumericCopy + PartialEq + Integer + hacspec_lib::Div<Output = T>>
    Add<EllipticCurvePoint<T>> for EllipticCurvePoint<T>
{
    type Output = Self;

    fn add(self, other: EllipticCurvePoint<T>) -> Self {
        if self.isPointAtInfinity {
            return other;
        }
        if other.isPointAtInfinity {
            return self;
        }
        if self == other {
            return self.double();
        }
        if self == other.neg() {
            return EllipticCurvePoint {
                x: T::default(),
                y: T::default(),
                a1: self.a1,
                a2: self.a2,
                a3: self.a3,
                a4: self.a4,
                a5: self.a5,
                a6: self.a6,
                isPointAtInfinity: true,
                bit_size_of_field: self.bit_size_of_field,
            };
        }
        let x_diff = other.x - self.x;
        let y_diff = other.y - self.y;
        let lambda = y_diff / x_diff;

        let x3 = lambda.exp(2u32) + self.a1 * lambda - self.a2 - self.x - other.x;
        let y3 = lambda * self.x - self.a1 * x3 - self.a3 - lambda * x3 - self.y;

        return EllipticCurvePoint {
            x: x3,
            y: y3,
            a1: self.a1,
            a2: self.a2,
            a3: self.a3,
            a4: self.a4,
            a5: self.a5,
            a6: self.a6,
            isPointAtInfinity: false,
            bit_size_of_field: self.bit_size_of_field,
        };
    }
}

impl<
        U: Numeric + NumericCopy + PartialEq + Integer + hacspec_lib::Div<Output = U>,
        T: Numeric + NumericCopy + PartialEq + Integer + hacspec_lib::Div<Output = T>,
    > Mul<U> for EllipticCurvePoint<T>
{
    type Output = Self;

    fn mul(self, rhs: U) -> Self::Output {
        if self.isPointAtInfinity {
            return self;
        }
        let mut t = self;
        t.x = T::default();
        t.y = T::default();
        t.isPointAtInfinity = true;
        let bit_size_of_field = self.bit_size_of_field;
        for i in 0..self.bit_size_of_field {
            t = t.double();
            //starting from second most significant bit
            if rhs.get_bit(bit_size_of_field - 1 - i) == U::ONE() {
                t = t.add(self);
            }
        }
        t
    }
}

impl<T: Numeric + NumericCopy + PartialEq + Integer + hacspec_lib::Div<Output = T>> PartialEq
    for EllipticCurvePoint<T>
{
    fn eq(&self, other: &Self) -> bool {
        if self.x != other.x {
            return false;
        }
        if self.y != other.y {
            return false;
        }
        if self.isPointAtInfinity != other.isPointAtInfinity {
            return false;
        }
        // if self.a1 != other.a1 {
        //     return false;
        // }
        // if self.a2 != other.a2 {
        //     return false;
        // }
        // if self.a3 != other.a3 {
        //     return false;
        // }
        // if self.a4 != other.a4 {
        //     return false;
        // }
        // if self.a5 != other.a5 {
        //     return false;
        // }
        // if self.a6 != other.a6 {
        //     return false;
        // }
        return true;
    }
}

impl<T: Numeric + NumericCopy + PartialEq + Integer + hacspec_lib::Div<Output = T>> Default
    for EllipticCurvePoint<T>
{
    fn default() -> Self {
        EllipticCurvePoint {
            x: T::default(),
            y: T::default(),
            a1: T::default(),
            a2: T::default(),
            a3: T::default(),
            a4: T::default(),
            a5: T::default(),
            a6: T::default(),
            isPointAtInfinity: true,
            bit_size_of_field: 0,
        }
    }
}

#[cfg(test)]
extern crate quickcheck;
#[cfg(test)]
#[macro_use(quickcheck)]
extern crate quickcheck_macros;
#[cfg(test)]
use quickcheck::*;
#[cfg(test)]
public_nat_mod!(
    type_name: FpPallas,
    type_of_canvas: PallasCanvas,
    bit_size_of_field: 255,
    modulo_value: "40000000000000000000000000000000224698FC094CF91B992D30ED00000001"
);
#[cfg(test)]
public_nat_mod!(
    type_name: FpVesta,
    type_of_canvas: VestaCanvas,
    bit_size_of_field: 255,
    modulo_value: "40000000000000000000000000000000224698FC0994A8DD8C46EB2100000001"
);

// Only needed for test/Arbitrary (and mut refs are not supported)
#[cfg(test)]
impl<T: Numeric + NumericCopy + PartialEq + Integer + hacspec_lib::Div<Output = T>> Debug
    for EllipticCurvePoint<T>
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", (self.x, self.y, self.isPointAtInfinity))
    }
}

#[cfg(test)]
impl Arbitrary for EllipticCurvePoint<FpPallas> {
    fn arbitrary(g: &mut Gen) -> EllipticCurvePoint<FpPallas> {
        let a = FpPallas::from_literal(u128::arbitrary(g));
        let generator = g1_generator_pallas();
        let point = generator * a;
        point
    }
}

#[cfg(test)]
impl Arbitrary for FpVesta {
    fn arbitrary(g: &mut Gen) -> FpVesta {
        let mut a: [u64; 4] = [0; 4];
        for i in 0..4 {
            a[i] = u64::arbitrary(g);
        }
        let mut b: [u8; 32] = [0; 32];
        for i in 0..4 {
            let val: u64 = a[i];
            b[(i * 8)..((i + 1) * 8)].copy_from_slice(&(val.to_le_bytes()));
        }
        b[31] = b[31] & 127;
        FpVesta::from_byte_seq_le(Seq::<U8>::from_public_slice(&b))
    }
}

#[cfg(test)]
pub fn g1_generator_pallas() -> EllipticCurvePoint<FpPallas> {
    EllipticCurvePoint {
        x: FpPallas::from_hex("1"),
        y: FpPallas::from_hex("1B74B5A30A12937C53DFA9F06378EE548F655BD4333D477119CF7A23CAED2ABB"),
        a1: FpPallas::ZERO(),
        a2: FpPallas::ZERO(),
        a3: FpPallas::ZERO(),
        a4: FpPallas::ZERO(),
        a5: FpPallas::ZERO(),
        a6: FpPallas::from_literal(5),
        isPointAtInfinity: false,
        bit_size_of_field: 255,
    }
}

#[cfg(test)]
pub fn identity_pallas() -> EllipticCurvePoint<FpPallas> {
    EllipticCurvePoint {
        x: FpPallas::ZERO(),
        y: FpPallas::ZERO(),
        a1: FpPallas::ZERO(),
        a2: FpPallas::ZERO(),
        a3: FpPallas::ZERO(),
        a4: FpPallas::ZERO(),
        a5: FpPallas::ZERO(),
        a6: FpPallas::from_literal(5),
        isPointAtInfinity: true,
        bit_size_of_field: 255,
    }
}

#[cfg(test)]
#[test]
fn test_g1_arithmetic_vesta() {
    let g = g1_generator_pallas();
    let g2 = g.double();
    let g4 = g2.double();
    let g3 = g2 + g;
    let g4b = g3 + g;
    assert_eq!(g4b, g4);
}

#[cfg(test)]
#[quickcheck]
fn test_closure(a: EllipticCurvePoint<FpPallas>, b: EllipticCurvePoint<FpPallas>) {
    let sum = a + b;
    assert!(sum.is_on_curve());
}

#[cfg(test)]
#[quickcheck]
fn test_associativity(
    a: EllipticCurvePoint<FpPallas>,
    b: EllipticCurvePoint<FpPallas>,
    c: EllipticCurvePoint<FpPallas>,
) {
    let sum1 = (a + b) + c;
    let sum2 = (b + c) + a;
    assert_eq!(sum1, sum2);
}

#[cfg(test)]
#[quickcheck]
fn test_identity(a: EllipticCurvePoint<FpPallas>) {
    use std::convert::identity;

    let identity = EllipticCurvePoint::default();
    let sum = a + identity;
    println!("{:?}", sum);
    println!("{:?}", a);

    assert_eq!(sum, a);
}

#[cfg(test)]
#[quickcheck]
fn test_inverse(a: EllipticCurvePoint<FpPallas>) {
    let a_neg = a.neg();

    let sum = a + a_neg;

    assert!(sum.isPointAtInfinity);
}

#[cfg(test)]
#[test]
fn test_mul_standard() {
    let g = g1_generator_pallas();
    let m = FpVesta::ONE();
    assert_eq!(g, g * m);
    let m = FpVesta::from_literal(2u128);
    let g2 = g.double();
    assert_eq!(g2, g * m);
    let m = FpVesta::from_literal(3u128);
    let g3 = g + g2;
    assert_eq!(g3, g * m);
}

#[cfg(test)]
#[test]
fn test_mul_zero() {
    let g = g1_generator_pallas();
    let m = FpVesta::ZERO();
    let h = g * m;
    assert!(h.isPointAtInfinity);
}

#[cfg(test)]
#[test]
fn test_mul() {
    fn test_g1_mul_pallas(a: FpVesta) -> bool {
        let g = g1_generator_pallas() * a;
        let r = FpVesta::from_hex("0"); //r
        let h = g * r;
        h.isPointAtInfinity
    }
    //Only needing 5 successes, slow because affine
    QuickCheck::new()
        .tests(5)
        .quickcheck(test_g1_mul_pallas as fn(FpVesta) -> bool);
}

#[cfg(test)]
#[test]
fn test_g1_add_double_equiv_pallas() {
    fn test_g1_mul_pallas(a: FpVesta) -> bool {
        let g = g1_generator_pallas() * a;
        g + g == g.double()
    }
    //Only needing 5 successes, slow because affine
    QuickCheck::new()
        .tests(5)
        .quickcheck(test_g1_mul_pallas as fn(FpVesta) -> bool);
}

#[cfg(test)]
#[test]
fn test_add_double_special_case() {
    let g = EllipticCurvePoint {
        x: FpPallas::TWO(),
        y: FpPallas::ZERO(),
        a1: FpPallas::ZERO(),
        a2: FpPallas::ZERO(),
        a3: FpPallas::ZERO(),
        a4: FpPallas::ZERO(),
        a5: FpPallas::ZERO(),
        a6: FpPallas::from_literal(5),
        isPointAtInfinity: true,
        bit_size_of_field: 255,
    };
    assert_eq!(g + g, g.double());
}
