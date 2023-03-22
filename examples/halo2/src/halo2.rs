use hacspec_lib::*;

public_nat_mod!( //Custom Macro - defining a newtype with some functions - well defined macro's have library functions built in
    type_name: Fp,
    type_of_canvas: FpCanvas,
    bit_size_of_field: 258, //381 with 3 extra bits
    modulo_value: "40000000000000000000000000000000224698fc094cf91b992d30ed00000001" //0x40000000000000000000000000000000224698fc094cf91b992d30ed00000001
);

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

fn mul_scalar_polyx(p1: Seq<Fp>, s: Fp) -> Seq<Fp> {
    let mut res = p1.clone();

    for i in 0..res.len() {
        res[i] = p1[i] * s;
    }

    res
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
#[quickcheck]
fn test_poly_add() -> bool {
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

    p3[0] == Fp::from_literal(60) && p3[1] == Fp::from_literal(10) && p3[2] == Fp::from_literal(20)
}

#[cfg(test)]
#[quickcheck]
fn test_poly_mul() -> bool {
    let v1 = vec![5, 10, 20]
        .iter()
        .map(|e| Fp::from_literal((*e) as u128))
        .collect();
    let p1 = Seq::from_vec(v1);

    let p3 = mul_scalar_polyx(p1, Fp::TWO());

    p3[0] == Fp::from_literal(10) && p3[1] == Fp::from_literal(20) && p3[2] == Fp::from_literal(40)
}
