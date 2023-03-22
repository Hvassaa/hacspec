use hacspec_lib::*;


public_nat_mod!( //Custom Macro - defining a newtype with some functions - well defined macro's have library functions built in
    type_name: Fp,
    type_of_canvas: FpCanvas,
    bit_size_of_field: 258, //381 with 3 extra bits
    modulo_value: "40000000000000000000000000000000224698fc094cf91b992d30ed00000001" //0x40000000000000000000000000000000224698fc094cf91b992d30ed00000001
);

public_nat_mod!( //Custom Macro - defining a new type with some functions - well defined macro's have library functions built in
    type_name: Scalar,
    type_of_canvas: ScalarCanvas,
    bit_size_of_field: 256,
    modulo_value: "8000000000000000000000000000000000000000000000000000000000000000" //0x8000000000000000000000000000000000000000000000000000000000000000
);

// univariate polynomial represented as coefficients
// (left-most is lowest power, right-most is highest power)
#[derive(Clone, Debug)]
pub struct UniPolynomial(Seq<Fp>);

// evaluate polynomial "p" at point "x"
pub fn eval_uni_poly(p: UniPolynomial, x: Fp) -> Fp {
    let mut res: Fp = Fp::from_literal(0);
    let UniPolynomial(s) = p;
    s.iter().enumerate().for_each(|(i, c)| {
        let power = i as u32;
        res = res + (x.exp(power) * (*c));
    });

    res
}

// multiply polynomial "p" by scalar "x"
pub fn mult_uni_poly_scalar(p: UniPolynomial, x: Fp) -> UniPolynomial {
    let UniPolynomial(s) = p;
    let mut res = s.clone();

    s.iter().enumerate().for_each(|(i, _)| {
        res[i] = res[i] * x;
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
        let size = u8::arbitrary(g) % 20;
        let mut v = vec![];
        for _ in 0..size {
            v.push(Fp::from_literal(u128::arbitrary(g)));
        }
        UniPolynomial(Seq::<Fp>::from_vec(v))
    }
}

 
// polynomial for testing
#[cfg(test)]
fn get_test_poly() -> UniPolynomial {
    let v = vec![5, 200, 59, 33, 0, 19];
    let vfp: Vec<Fp> = v.iter().map(|e| Fp::from_literal(*e)).collect();
    let s = Seq::from_vec(vfp);

    UniPolynomial(s)
}
//
// #[cfg(test)]
// #[quickcheck]
// fn test_eval_polynomial() -> bool {
//     let p = get_test_poly();
//
//     eval_uni_poly(p, Fp::TWO()) == Fp::from_literal(1513) // trust me
// }

#[cfg(test)]
#[quickcheck]
fn test_eval_polylol() -> bool {
    let UniPolynomial(p1) = get_test_poly();
    let UniPolynomial(p2) = get_test_poly();
    add_poly(&p1, &p2);
    println!("{}", 100);
    true
}


// #[cfg(test)]
// #[quickcheck]
// fn test_eval_polynomial(a: UniPolynomial) -> bool {
//     let point = Fp::from_literal(7);
//     let a2 = a.clone();
//     let UniPolynomial(s) = a;
//     let p = polynomial::Polynomial::new(s.native_slice().to_vec());
//     let home = eval_uni_poly(a2, point);
//     let away = p.eval(point);
//     home == away
// }
