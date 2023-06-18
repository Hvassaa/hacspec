#![allow(non_snake_case)]
#![allow(dead_code)]
#![allow(warnings, unused)]

use hacspec_halo2::*;
use hacspec_lib::*;
use hacspec_pasta::*;
use hacspec_polynomial::*;

/*
 * let n = 2^2 = 4
 * then ω = big is 4 prime root of unity over Fp::Canvas
 *
 * | i | a_0 | a_1 | a_2 | q_add | q_sub |
 * |---|-----|-----|-----|-------|-------|
 * | 0 | 2   | 3   | 5   | 1     | 0     |
 * | 1 | 10  |     |     | 0     | 0     |
 * | 2 | 100 | 50  | 25  | 0     | 1     |
 * | 3 | 25  |     |     | 0     | 0     |
 *
 * then, g(X) = q_add(X) * (a_0(X) + a_1(X) + a_2(X) - a_0(ωX))
 * and g(ω^i) = 0 for all i in [0,n) (should hold)
 *
 *
 */

trait Chip {
    fn to_polynomial(&self, polys: Seq<Polynomial<FpVesta>>, omega: FpVesta) -> Polynomial<FpVesta>;
}

struct Configuration {
    matrix: Seq<Seq<FpVesta>>,
    polys: Seq<Polynomial<FpVesta>>,
    omega: FpVesta,
    g: Polynomial<FpVesta>,
}

impl Configuration {
    fn new(matrix: Seq<Seq<FpVesta>>, omega: FpVesta) -> Self {
        let mut polys = Seq::<Polynomial<FpVesta>>::create(matrix.len());

        for i in 0..matrix.len() {
            let col = &matrix[i];
            let mut points = Seq::<(FpVesta, FpVesta)>::create(col.len());
            for j in 0..col.len() {
                points[j] = (omega.pow(j as u128), col[j]);
            }
            let coeffs = lagrange_polyx(points);
            let poly = Polynomial::<FpVesta>::new(coeffs);
            polys[i] = poly;
        }
        Configuration { matrix, polys, omega, g: Polynomial::<FpVesta>::default() }
    }

    fn apply_chip(self, chip: &Chip) -> Self {
        let matrix = self.matrix;
        let polys = self.polys;
        let omega = self.omega;
        let g = self.g;
        let g = g + chip.to_polynomial(polys.clone(), omega);

        Configuration {matrix, polys, omega, g}
    }

    fn get_g(self) -> Polynomial<FpVesta> {
        self.g
    }
}

// a_0(X) + a_1(X) + a_2(X) = a_0(ωX)
struct AdditionChip {}
impl Chip for AdditionChip {
    fn to_polynomial(&self, polys: Seq<Polynomial<FpVesta>>, omega: FpVesta) -> Polynomial<FpVesta> {
        let a_0: &Polynomial<FpVesta> = &polys[0];
        let a_0_rotated = Polynomial::<FpVesta>::new(rotate_polyx(a_0.coeffs(), omega));
        let a_1: &Polynomial<FpVesta>= &polys[1];
        let a_2: &Polynomial<FpVesta>= &polys[2];
        let q_add: &Polynomial<FpVesta>= &polys[3];

        let combined = q_add.clone() * ((a_0.clone() + a_1.clone() + a_2.clone()) - a_0_rotated);

        combined
    }
}

// a_0(X) - a_1(X) - a_2(X) = a_0(ωX)
struct SubtractionChip {}
impl Chip for SubtractionChip {
    fn to_polynomial(&self, polys: Seq<Polynomial<FpVesta>>, omega: FpVesta) -> Polynomial<FpVesta> {
        let a_0: &Polynomial<FpVesta> = &polys[0];
        let a_0_rotated = Polynomial::<FpVesta>::new(rotate_polyx(a_0.coeffs(), omega));
        let a_1: &Polynomial<FpVesta>= &polys[1];
        let a_2: &Polynomial<FpVesta>= &polys[2];
        let q_sub: &Polynomial<FpVesta>= &polys[4];

        let combined = q_sub.clone() * ((a_0.clone() - a_1.clone() - a_2.clone()) - a_0_rotated);

        combined
    }
}

#[cfg(test)]
#[test]
fn test_test() {
    let n = 4;
    let a_0 = Seq::<FpVesta>::from_vec(vec![
        FpVesta::from_literal(2),
        FpVesta::from_literal(10),
        FpVesta::from_literal(100),
        FpVesta::from_literal(25),
    ]);
    let a_1 = Seq::<FpVesta>::from_vec(vec![
        FpVesta::from_literal(3),
        FpVesta::from_literal(0),
        FpVesta::from_literal(50),
        FpVesta::from_literal(0),
    ]);
    let a_2 = Seq::<FpVesta>::from_vec(vec![
        FpVesta::from_literal(5),
        FpVesta::from_literal(0),
        FpVesta::from_literal(25),
        FpVesta::from_literal(0),
    ]);
    let q_add = Seq::<FpVesta>::from_vec(vec![
        FpVesta::from_literal(1),
        FpVesta::from_literal(0),
        FpVesta::from_literal(0),
        FpVesta::from_literal(0),
    ]);
    let q_sub = Seq::<FpVesta>::from_vec(vec![
        FpVesta::from_literal(0),
        FpVesta::from_literal(0),
        FpVesta::from_literal(1),
        FpVesta::from_literal(0),
    ]);
    let matrix = Seq::from_vec(vec![a_0, a_1, a_2, q_add, q_sub]);
    let omega: FpVesta =
        FpVesta::from_hex("3691ce115adfa1187d65aa6313c354eb4a146505975fd3435d2f235b4abeb917");


    let mut config = Configuration::new(matrix, omega);
    let addition_chip = AdditionChip {};
    let subtraction_chip = SubtractionChip {};
    let g = config.apply_chip(&addition_chip).apply_chip(&subtraction_chip).get_g();


    for i in 0..n {
        assert_eq!(FpVesta::ZERO() ,g.clone().evaluate(omega.pow(i as u128)));
    }
}
