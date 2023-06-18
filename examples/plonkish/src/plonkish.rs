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
    fn to_polynomial(&self, polys: Seq<Polynomial<FpVesta>>, omega: FpVesta)
        -> Polynomial<FpVesta>;
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
        Configuration {
            matrix,
            polys,
            omega,
            g: Polynomial::<FpVesta>::default(),
        }
    }

    fn apply_chip(self, chip: Box<Chip>) -> Self {
        let matrix = self.matrix;
        let polys = self.polys;
        let omega = self.omega;
        let g = self.g;
        let g = g + chip.to_polynomial(polys.clone(), omega);

        Configuration {
            matrix,
            polys,
            omega,
            g,
        }
    }

    pub fn get_polys(&self) -> Seq<Polynomial<FpVesta>> {
        self.polys.clone()
    }

    pub fn get_g(self) -> Polynomial<FpVesta> {
        self.g
    }
}

// a_0(X) + a_1(X) + a_2(X) = a_0(ωX)
struct AdditionChip {}
impl Chip for AdditionChip {
    fn to_polynomial(
        &self,
        polys: Seq<Polynomial<FpVesta>>,
        omega: FpVesta,
    ) -> Polynomial<FpVesta> {
        let a_0: &Polynomial<FpVesta> = &polys[0];
        let a_0_rotated = Polynomial::<FpVesta>::new(rotate_polyx(a_0.coeffs(), omega));
        let a_1: &Polynomial<FpVesta> = &polys[1];
        let a_2: &Polynomial<FpVesta> = &polys[2];
        let q_add: &Polynomial<FpVesta> = &polys[3];

        let combined = q_add.clone() * ((a_0.clone() + a_1.clone() + a_2.clone()) - a_0_rotated);

        combined
    }
}

// a_0(X) - a_1(X) - a_2(X) = a_0(ωX)
struct SubtractionChip {}
impl Chip for SubtractionChip {
    fn to_polynomial(
        &self,
        polys: Seq<Polynomial<FpVesta>>,
        omega: FpVesta,
    ) -> Polynomial<FpVesta> {
        let a_0: &Polynomial<FpVesta> = &polys[0];
        let a_0_rotated = Polynomial::<FpVesta>::new(rotate_polyx(a_0.coeffs(), omega));
        let a_1: &Polynomial<FpVesta> = &polys[1];
        let a_2: &Polynomial<FpVesta> = &polys[2];
        let q_sub: &Polynomial<FpVesta> = &polys[4];

        let combined = q_sub.clone() * ((a_0.clone() - a_1.clone() - a_2.clone()) - a_0_rotated);

        combined
    }
}

#[cfg(test)]
#[test]
fn test_config() {
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
    let addition_chip = Box::new(AdditionChip {});
    let subtraction_chip = Box::new(SubtractionChip {});
    let g = config
        .apply_chip(addition_chip)
        .apply_chip(subtraction_chip)
        .get_g();

    for i in 0..n {
        assert_eq!(FpVesta::ZERO(), g.clone().evaluate(omega.pow(i as u128)));
    }
}

// Generators taken from:
// https://o1-labs.github.io/proof-systems/specs/pasta.html#pallas
// (mina generator: (1,12418654782883325593414442427049395787963493412651469444558597405572177144507))
#[cfg(test)]
fn g1_generator_pallas() -> G1_pallas {
    (
        FpPallas::from_hex("1"),
        FpPallas::from_hex("1B74B5A30A12937C53DFA9F06378EE548F655BD4333D477119CF7A23CAED2ABB"),
        false,
    )
}

#[cfg(test)]
#[test]
fn example_run() {
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
    let n: usize = 4;
    let n_a: usize = 3;
    let n_q: usize = 2;
    let n_g = 4;
    let omega: FpVesta =
        FpVesta::from_hex("3691ce115adfa1187d65aa6313c354eb4a146505975fd3435d2f235b4abeb917");
    let G: Seq<G1_pallas> = Seq::<G1_pallas>::from_vec(vec![
        g1mul_pallas(FpVesta::from_literal(22 as u128), g1_generator_pallas()),
        g1mul_pallas(FpVesta::from_literal(7 as u128), g1_generator_pallas()),
        g1mul_pallas(FpVesta::from_literal(9 as u128), g1_generator_pallas()),
        g1mul_pallas(FpVesta::from_literal(43 as u128), g1_generator_pallas()),
    ]);
    let W: G1_pallas = g1mul_pallas(FpVesta::from_literal(123 as u128), g1_generator_pallas());
    let crs: CRS = (G.clone(), W);
    let U: G1_pallas = g1mul_pallas(FpVesta::from_literal(72143 as u128), g1_generator_pallas());

    let r_poly = Seq::<FpVesta>::from_vec(vec![
        FpVesta::from_literal(13 as u128),
        FpVesta::from_literal(1123 as u128),
        FpVesta::from_literal(1444 as u128),
        FpVesta::from_literal(9991 as u128),
    ]);
    let R_blind: FpVesta = FpVesta::from_literal(123 as u128);
    let R: G1_pallas = commit_polyx(&crs, r_poly.clone(), R_blind);

    let p: Seq<Seq<usize>> = Seq::<Seq<usize>>::from_vec(vec![
        Seq::<usize>::from_vec(vec![0, 1]),
        Seq::<usize>::from_vec(vec![usize::zero()]),
        Seq::<usize>::from_vec(vec![usize::zero()]),
    ]);

    // MATRIX
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

    let config = Configuration::new(matrix, omega);
    let addition_chip = Box::new(AdditionChip {});
    let subtraction_chip = Box::new(SubtractionChip {});
    let config = config
        .apply_chip(addition_chip)
        .apply_chip(subtraction_chip);
    let polys = config.get_polys();
    let g = config.get_g();
    let g_prime = g.coeffs();
    ///////////////////

    let a_0: &Polynomial<FpVesta> = &polys[0];
    let a_0 = a_0.coeffs();
    let a_1: &Polynomial<FpVesta> = &polys[1];
    let a_1 = a_1.coeffs();
    let a_2: &Polynomial<FpVesta> = &polys[2];
    let a_2 = a_2.coeffs();

    let q_add: &Polynomial<FpVesta> = &polys[3];
    let q_add = q_add.clone();
    let q_sub: &Polynomial<FpVesta> = &polys[4];
    let q_sub = q_sub.clone();

    let a_primes: Seq<Polyx> = Seq::<Polyx>::from_vec(vec![a_0.clone(), a_1.clone(), a_2.clone()]);

    // construct A_i's (commitments)
    let A_0_blinding: FpVesta = FpVesta::from_literal(123 as u128);
    let A_0: G1_pallas = commit_polyx(&crs, a_0.clone(), A_0_blinding);
    let A_1_blinding: FpVesta = FpVesta::from_literal(234 as u128);
    let A_1: G1_pallas = commit_polyx(&crs, a_1.clone(), A_1_blinding);
    let A_2_blinding: FpVesta = FpVesta::from_literal(345 as u128);
    let A_2: G1_pallas = commit_polyx(&crs, a_2.clone(), A_2_blinding);
    let A_list: Seq<G1_pallas> = Seq::<G1_pallas>::from_vec(vec![A_0, A_1, A_2]);
    // save a_blinds
    let a_blinds = Seq::from_vec(vec![A_0_blinding, A_1_blinding, A_2_blinding]);

    let q: Seq<Seq<usize>> = Seq::<Seq<usize>>::from_vec(vec![
        Seq::from_vec(vec![usize::zero()]),
        Seq::from_vec(vec![0, 1]),
    ]);
    let sigma_list: Seq<usize> = Seq::<usize>::from_vec(vec![1, 0, 0]);

    let h: Polyx = step_4(g_prime.clone(), omega, n);

    let h_is: Seq<Polyx> = step_5(h.clone(), n, 4);

    let h_blindings: Polyx = Seq::<FpVesta>::from_vec(vec![
        FpVesta::from_literal(3 as u128),
        FpVesta::from_literal(4523 as u128),
        FpVesta::from_literal(838 as u128),
    ]);
    let H_is: Seq<G1_pallas> = step_6(h_is.clone(), &crs, h_blindings.clone());

    let x_challenge: FpVesta = FpVesta::from_literal(2 as u128);
    let H_prime: G1_pallas = step_7(H_is, x_challenge, n);

    let (h_prime, h_prime_blind) = step_8(h_is, x_challenge, n, h_blindings.clone());

    let (r, fat_a) = step_9(
        r_poly.clone(),
        a_primes.clone(),
        omega,
        p.clone(),
        x_challenge,
    );

    let s_is: Seq<Polyx> = step_10(omega, p.clone(), x_challenge, fat_a.clone());

    let x1_challenge = FpVesta::from_literal(2 as u128);
    let x2_challenge: FpVesta = FpVesta::from_literal(2 as u128);

    let (Q_is, _, _): (Seq<G1_pallas>, FpVesta, FpVesta) = step_11(
        n_a,
        x1_challenge,
        x2_challenge,
        H_prime,
        R,
        A_list,
        q.clone(),
        sigma_list.clone(),
    );

    let (q_is, q_blinds) = step_12(
        n_a,
        x1_challenge,
        h_prime,
        r_poly,
        a_primes.clone(),
        q.clone(),
        sigma_list.clone(),
        a_blinds,
        R_blind,
        h_prime_blind,
    );

    let fat_a_0: &Seq<FpVesta> = &fat_a[usize::zero()];
    let fat_a_1: &Seq<FpVesta> = &fat_a[1];
    let fat_a_2: &Seq<FpVesta> = &fat_a[2];
    // recreate g'(x) from **a**
    let g_prime_eval_combined_from_a = (q_add.evaluate(x_challenge)
        * (fat_a_0[0] + fat_a_1[0] + fat_a_2[0] - fat_a_0[1]))
        + (q_sub.evaluate(x_challenge) * (fat_a_0[0] - fat_a_1[0] - fat_a_2[0] - fat_a_0[1]));

    // let g_prime_eval_combined_from_a = eval_polyx(q_add, x_challenge)
    //     * (fat_a_0[usize::zero()] + fat_a_1[usize::zero()] + fat_a_2[usize::zero()] - fat_a_0[1]);

    let (r_is_prover, r_is_verifier): (Seq<Polyx>, Seq<Polyx>) = step_13(
        n,
        omega,
        x_challenge,
        x1_challenge,
        r,
        s_is,
        q.clone(),
        sigma_list.clone(),
        g_prime_eval_combined_from_a,
        g_prime,
    );

    let step14_blinding: FpVesta = FpVesta::from_literal(32 as u128);
    let (Q_prime, q_prime, Q_prime_blind) = step_14(
        &crs,
        x2_challenge,
        q_is.clone(),
        r_is_prover,
        q.clone(),
        step14_blinding,
        omega,
        x_challenge,
    );

    let x3_challenge: FpVesta = step_15(FpVesta::from_literal(3 as u128));

    let u: Polyx = step_16(n_q, x3_challenge, q_is.clone());

    let x4_challenge: FpVesta = step_17(FpVesta::from_literal(2 as u128));

    let (P, v) = step_18(
        x_challenge,
        x1_challenge,
        x2_challenge,
        x3_challenge,
        x4_challenge,
        omega,
        Q_prime,
        Q_is,
        u.clone(),
        r_is_verifier,
        q,
    );

    let (p_poly, p_blind) = step_19(x4_challenge, q_prime, q_is, q_blinds, Q_prime_blind);

    let step20_blinding: FpVesta = FpVesta::from_literal(532 as u128);
    let s_poly_points: Seq<(FpVesta, FpVesta)> = Seq::from_vec(vec![
        (
            FpVesta::from_literal(729 as u128),
            FpVesta::from_literal(23 as u128),
        ),
        (
            FpVesta::from_literal(73 as u128),
            FpVesta::from_literal(102 as u128),
        ),
        (
            FpVesta::from_literal(444 as u128),
            FpVesta::from_literal(484 as u128),
        ),
        (x3_challenge, FpVesta::ZERO()),
    ]);
    let s_poly: Polyx = lagrange_polyx(s_poly_points);
    assert_eq!(
        eval_polyx(s_poly.clone(), x3_challenge),
        FpVesta::ZERO(),
        "s(X) should have root at x3"
    );
    assert_eq!(
        degree_polyx(s_poly.clone()),
        n - 1,
        "s(X) should have degree n-1: {}",
        n - 1
    );
    let (S, s_blind) = step_20(s_poly.clone(), crs, step20_blinding);

    let (xi, z) = step_21(
        FpVesta::from_literal(2 as u128),
        FpVesta::from_literal(2 as u128),
    );

    let P_prime: G1_pallas = step_22(P, G[usize::zero()], S, v, xi);

    assert_eq!(
        eval_polyx(p_poly.clone(), x3_challenge),
        v,
        "p(x3) should correspond with v"
    );
    let (p_prime_poly, p_prime_blind) = step_23(p_poly, s_poly, x3_challenge, xi, p_blind, s_blind);

    let L_blinding: Polyx = Seq::<FpVesta>::from_vec(vec![
        FpVesta::from_literal(549 as u128),
        FpVesta::from_literal(634 as u128),
    ]);
    let R_blinding: Polyx = Seq::<FpVesta>::from_vec(vec![
        FpVesta::from_literal(827 as u128),
        FpVesta::from_literal(826 as u128),
    ]);
    let u_challenges: Polyx = Seq::from_vec(vec![
        FpVesta::from_literal(2 as u128),
        FpVesta::from_literal(2 as u128),
    ]);
    let (p_prime, G_prime, b, L, R, L_blinding, R_blinding) = step_24(
        p_prime_poly,
        G,
        x3_challenge,
        z,
        U,
        W,
        n,
        2,
        u_challenges.clone(),
        L_blinding,
        R_blinding,
    );
    let (c, f) = step_25(
        p_prime,
        L_blinding,
        R_blinding,
        p_prime_blind,
        u_challenges.clone(),
    );

    let V_accepts = step_26(
        u_challenges,
        L,
        P_prime,
        R,
        c,
        G_prime[usize::zero()],
        b[usize::zero()],
        z,
        U,
        f,
        W,
    );

    assert!(V_accepts);
}
