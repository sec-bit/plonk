use ark_ff::Zero;
use ark_poly::{univariate::DensePolynomial, Polynomial, UVPolynomial};
use ark_poly_commit::{LCTerm, LinearCombination};
use ark_std::{borrow::Borrow, cfg_iter_mut, format, ops::Mul, rand::RngCore, vec, vec::Vec};

mod prover_key;
pub(crate) use prover_key::*;

use crate::utils::interpolate_and_coset_fft;
use crate::{Composer, Domain, Error, Field, Map};

mod widget;
use widget::{ArithmeticWidget, LookupWidget, PermutationWidget, RangeWidget, Widget};

pub(crate) struct Prover<F: Field, D: Domain<F>> {
    domain_values: Map<String, Vec<F>>,
    coset_values: Map<String, Vec<F>>,
    polynomials: Map<String, DensePolynomial<F>>,

    challenges: Map<String, F>,
    evaluations: Map<String, F>,

    pub domain: D,
    pub coset: D,
    pub program_width: usize,
}

impl<'a, F: Field, D: Domain<F>> Prover<F, D> {
    pub fn domain_size(&self) -> usize {
        self.domain.size()
    }

    pub fn coset_size(&self) -> usize {
        self.coset.size()
    }

    pub fn insert(&mut self, label: &str, domain_values: Vec<F>) {
        let (domain_values, coset_values, polynomial) =
            interpolate_and_coset_fft(domain_values, self.domain, self.coset);

        self.domain_values.insert(label.to_string(), domain_values);
        self.coset_values.insert(label.to_string(), coset_values);
        self.polynomials.insert(label.to_string(), polynomial);
    }

    pub fn add_polynomial(&mut self, label: &str, polynomial: DensePolynomial<F>) {
        self.polynomials.insert(label.to_string(), polynomial);
    }

    pub fn add_challenge(&mut self, label: &str, value: F) {
        assert!(!self.challenges.contains_key(label));
        self.challenges.insert(label.to_string(), value);
    }

    pub fn get_challenge(&self, l: &str) -> Result<F, Error> {
        self.challenges
            .get(l)
            .cloned()
            .ok_or(Error::MissingElement(l.to_string()))
    }

    pub fn domain_values(&self) -> &Map<String, Vec<F>> {
        &self.domain_values
    }

    pub fn coset_values(&self) -> &Map<String, Vec<F>> {
        &self.coset_values
    }

    pub fn get_coset_values(&self, label: &str) -> Result<&[F], Error> {
        match self.coset_values.get(label) {
            None => Err(Error::MissingElement(format!(
                "missing coset values: {}",
                label
            ))),
            Some(v) => Ok(v),
        }
    }

    pub fn polynomials(&self) -> &Map<String, DensePolynomial<F>> {
        &self.polynomials
    }

    pub fn evaluate(&mut self, poly_label: &str, point_label: &str) -> Result<F, Error> {
        let label = format!("{}_{}", poly_label, point_label);
        match self.evaluations.get(&label) {
            Some(v) => Ok(*v),
            None => {
                let poly = self
                    .polynomials
                    .get(poly_label)
                    .ok_or(Error::MissingElement(poly_label.to_string()))?;
                let point = self
                    .challenges
                    .get(point_label)
                    .ok_or(Error::MissingElement(point_label.to_string()))?;
                let value = poly.evaluate(point);
                self.evaluations.insert(label, value);

                Ok(value)
            }
        }
    }

    pub fn evaluate_linear_combination(
        &mut self,
        lc: &LinearCombination<F>,
        point_label: &str,
    ) -> Result<F, Error> {
        let label = format!("{}_{}", lc.label, point_label);
        match self.evaluations.get(&label) {
            Some(value) => Ok(*value),
            None => {
                let point = self
                    .challenges
                    .get(point_label)
                    .ok_or(Error::MissingElement(point_label.to_string()))?;

                let value = evaluate_linear_combination(lc, &self.polynomials, point)?;
                self.evaluations.insert(label, value);
                Ok(value)
            }
        }
    }
}

impl<'a, F: Field, D: Domain<F>> Prover<F, D> {
    pub fn new(prover_key: &ProverKey<F, D>) -> Self {
        Self {
            domain_values: prover_key.domain_values().clone(),
            coset_values: prover_key.coset_values(),
            polynomials: prover_key.polynomials(),
            challenges: Map::new(),
            evaluations: Map::new(),
            domain: prover_key.domain,
            coset: prover_key.coset,
            program_width: prover_key.program_width,
        }
    }

    pub fn prove<R: RngCore>(&mut self, cs: &mut Composer<F>, rng: &mut R) -> Result<(), Error> {
        let widgets: Vec<Box<dyn Widget<F, D>>> = vec![
            Box::new(ArithmeticWidget::new(cs.program_width)),
            Box::new(PermutationWidget::new(cs.program_width)),
            Box::new(RangeWidget::new(cs.program_width)),
            Box::new(LookupWidget::new(cs.program_width)),
        ];

        print!("initializing...");
        let public_input = cs.compute_public_input();
        self.insert("pi", public_input.to_vec());
        let wires = cs.compute_wire_values()?;
        for (k, w) in wires.into_iter() {
            self.insert(&k, w);
        }
        println!("done");

        print!("first round...");
        self.add_challenge("eta", F::rand(rng));
        for w in widgets.iter() {
            w.compute_oracles(1, self)?;
        }
        println!("done");

        print!("second_round...");
        self.add_challenge("beta", F::rand(rng));
        self.add_challenge("gamma", F::rand(rng));
        for w in widgets.iter() {
            w.compute_oracles(2, self)?;
        }
        println!("done");

        print!("third round...");
        self.add_challenge("alpha", F::rand(rng));
        let t = {
            let mut combinator = F::one();

            let mut quotient = vec![F::zero(); self.coset_size()];
            for w in widgets.iter() {
                w.compute_quotient_contribution(self, &mut combinator, &mut quotient)?;
            }

            let vi = self.get_coset_values("vi")?;
            cfg_iter_mut!(quotient).zip(vi).for_each(|(q, v)| *q *= v);
            let t = DensePolynomial::from_coefficients_vec(self.coset.coset_ifft(&quotient));

            t
        };

        let mut t_chunks = split(t, self.domain_size());
        while t_chunks.len() < 4 {
            t_chunks.push(DensePolynomial::zero());
        }
        for (i, t) in t_chunks.into_iter().enumerate() {
            self.add_polynomial(&format!("t_{}", i), t);
        }
        println!("done");

        print!("forth round...");
        let zeta = F::rand(rng);
        self.add_challenge("zeta", zeta);
        self.add_challenge("zeta_omega", zeta * self.domain.generator());
        let (r, r_complement) = {
            let mut r = LinearCombination::<F>::empty("r");
            let mut r_complement = F::zero();
            let mut combinator = F::one();

            for w in widgets.iter() {
                let (w_r, w_complement) = &w.compute_linear_contribution(self, &mut combinator)?;

                r += w_r;
                r_complement += w_complement;
            }

            (r, r_complement)
        };
        let r_zeta = self.evaluate_linear_combination(&r, "zeta")?;
        let t = {
            let zeta = self.get_challenge("zeta")?;
            let zeta_n = zeta.pow(&[self.domain_size() as u64]);
            let zeta_2n = zeta_n.square();

            LinearCombination::<F>::new(
                "t",
                vec![
                    (F::one(), "t_0"),
                    (zeta_n, "t_1"),
                    (zeta_2n, "t_2"),
                    (zeta_n * zeta_2n, "t_3"),
                ],
            )
        };
        let t_zeta = self.evaluate_linear_combination(&t, "zeta")?;
        println!("done");

        print!("check equality...");
        let lhs = {
            let v_zeta = self
                .domain
                .evaluate_vanishing_polynomial(self.get_challenge("zeta")?);
            t_zeta * v_zeta
        };
        let rhs = {
            let q_arith_zeta = self.evaluate("q_arith", "zeta")?;
            let pi_zeta = self.evaluate("pi", "zeta")?;

            r_zeta - r_complement - q_arith_zeta * pi_zeta
        };

        assert_eq!(lhs, rhs, "prover equality check");
        println!("done");

        Ok(())
    }
}

fn split<F: Field>(poly: DensePolynomial<F>, chunk_size: usize) -> Vec<DensePolynomial<F>> {
    let mut chunks = Vec::new();

    let mut coeffs = poly.coeffs.into_iter().peekable();
    while coeffs.peek().is_some() {
        let chunk: Vec<_> = coeffs.by_ref().take(chunk_size).collect();
        chunks.push(DensePolynomial::from_coefficients_vec(chunk.to_vec()));
    }

    chunks
}

fn evaluate_linear_combination<F: Field>(
    lc: &LinearCombination<F>,
    polynomials: &Map<String, DensePolynomial<F>>,
    point: &F,
) -> Result<F, Error> {
    let mut acc = DensePolynomial::zero();
    for (coeff, term) in lc.iter() {
        acc = if let LCTerm::PolyLabel(term_label) = term {
            let polynomial = polynomials
                .get(term_label)
                .ok_or(Error::MissingElement(format!(
                    "polynomial {} for linear combination {}",
                    term_label, lc.label
                )))?
                .borrow();
            acc + polynomial.mul(&DensePolynomial::from_coefficients_vec(vec![*coeff]))
        } else {
            assert!(term.is_one());
            acc + DensePolynomial::from_coefficients_vec(vec![*coeff])
        }
    }

    Ok(acc.evaluate(point))
}

#[cfg(test)]
mod tests {
    use ark_bn254::Fr;
    use ark_std::{test_rng, UniformRand};

    use crate::composer::Composer;
    use crate::GeneralEvaluationDomain;

    use super::*;

    #[test]
    fn prover_linear_combination() -> Result<(), Error> {
        let rng = &mut test_rng();
        let degree = 10;
        let num = 10;

        let labels: Vec<_> = (0..num).into_iter().map(|i| format!("p_{}", i)).collect();
        let coeffs: Vec<_> = (0..num).into_iter().map(|_| Fr::rand(rng)).collect();
        let terms = (0..num)
            .into_iter()
            .zip(coeffs.clone())
            .map(|(i, c)| (c, labels[i].to_string()))
            .collect();
        let polynomials = labels
            .iter()
            .map(|l| (l.to_string(), DensePolynomial::<Fr>::rand(degree, rng)))
            .collect();

        let lc = LinearCombination::<Fr>::new("lc", terms);
        let point = Fr::rand(rng);
        let lc_value = evaluate_linear_combination(&lc, &polynomials, &point)?;

        let value: Fr = (0..num)
            .into_iter()
            .map(|i| polynomials[&labels[i]].evaluate(&point) * coeffs[i])
            .sum();
        assert_eq!(value, lc_value);

        Ok(())
    }

    #[test]
    fn prover_equality_check() -> Result<(), Error> {
        let mut cs = {
            // x^3 + x + pi = 35
            let mut cs = Composer::new(4);
            let pi = cs.alloc_input(Fr::from(5));
            let x = cs.alloc(Fr::from(3));
            let y = cs.mul(x, x);
            let z = cs.mul(x, y);
            let u = cs.add(x, z);
            let v = cs.add(pi, u);
            cs.enforce_constant(v, Fr::from(35));

            cs
        };

        let rng = &mut test_rng();

        let pk = cs.compute_prover_key::<GeneralEvaluationDomain<Fr>>()?;
        let mut prover = Prover::new(&pk);
        prover.prove(&mut cs, rng)?;

        Ok(())
    }
}
