use ark_ff::{batch_inversion, FftField, PrimeField};
use ark_poly::{univariate::DensePolynomial, EvaluationDomain, UVPolynomial};

pub trait Field: FftField + PrimeField {
    fn coset_generator(i: usize) -> Self;
}

use ark_poly::Evaluations;

pub(crate) trait Domain<F: Field>: 'static + EvaluationDomain<F> {
    fn generator(&self) -> F {
        self.element(1)
    }

    fn vanishing_polynomial(self) -> DensePolynomial<F> {
        let n = self.size();
        let mut coeffs = vec![F::zero(); n + 1];
        coeffs[0] = -F::one();
        coeffs[n] = F::one();
        DensePolynomial::from_coefficients_vec(coeffs)
    }

    /// index in range [1, domain_size]
    fn lagrange_polynomial(self, index: usize) -> DensePolynomial<F> {
        let n = self.size();
        assert!(index >= 1 && index <= n);
        let mut coeffs = vec![F::zero(); n];
        coeffs[index - 1] = F::one();
        Evaluations::from_vec_and_domain(coeffs, self).interpolate()
    }

    /// index in range [1, domain_size]
    fn evaluate_lagrange_polynomial(&self, index: usize, point: &F) -> F {
        let n = self.size();
        assert!(index >= 1 && index <= n);
        let numerator = point.pow(&[n as u64]) - F::one();
        let denominator = (F::from(n as u64) * (self.element(n - index + 1) * point - F::one()))
            .inverse()
            .unwrap();
        numerator * denominator
    }

    fn batch_evaluate_lagrange_polynomial(&self, indices: Vec<usize>, point: &F) -> Vec<F> {
        let n = self.size();

        indices
            .iter()
            .copied()
            .for_each(|i| assert!(i >= 1 && i <= n));

        let mut denominators: Vec<_> = indices
            .into_iter()
            .map(|i| F::from(n as u64) * (self.element(n - i + 1) * point - F::one()))
            .collect();
        batch_inversion(&mut denominators);

        let numerator = point.pow(&[n as u64]) - F::one();

        denominators
            .into_iter()
            .map(|denominator| denominator * numerator)
            .collect()
    }
}

pub type GeneralEvaluationDomain<F> = ark_poly::GeneralEvaluationDomain<F>;
impl<F: Field> Domain<F> for GeneralEvaluationDomain<F> {}

pub(crate) fn interpolate_and_coset_fft<F: Field>(
    mut domain_values: Vec<F>,
    domain: impl Domain<F>,
    coset: impl Domain<F>,
) -> (Vec<F>, Vec<F>, DensePolynomial<F>) {
    let zeros = vec![F::zero(); domain.size() - domain_values.len()];
    domain_values.extend(zeros);

    let polynomial = Evaluations::from_vec_and_domain(domain_values.clone(), domain).interpolate();
    let coset_values = coset.coset_fft(&polynomial);
    (domain_values, coset_values, polynomial)
}

#[cfg(test)]
mod tests {
    // use ark_bls12_381::{Bls12_381, Fr};
    use ark_bn254::Fr;
    use ark_ff::One;
    use ark_poly::Polynomial;
    use ark_std::{rand::Rng, test_rng, UniformRand};

    use super::*;

    impl Field for Fr {
        fn coset_generator(index: usize) -> Self {
            match index % 4 {
                1 => Fr::from(7_u64),
                2 => Fr::from(13_u64),
                3 => Fr::from(17_u64),
                _ => Self::one(),
            }
        }
    }

    #[test]
    fn utils_lagrange_evaluation() {
        let rng = &mut test_rng();
        let size: usize = rng.gen_range(1..(2 as usize).pow(10));
        let domain = GeneralEvaluationDomain::<Fr>::new(size).unwrap();
        let index = rng.gen_range(1..domain.size() + 1);
        let point = Fr::rand(rng);

        let l = domain.lagrange_polynomial(index);
        let l_point = domain.evaluate_lagrange_polynomial(index, &point);

        println!(
            "{}-th lagrange polynomial for domain of size {}:",
            index,
            domain.size()
        );
        assert_eq!(l.evaluate(&point), l_point);
    }

    #[test]
    fn utils_batch_lagrange_evaluation() {
        let rng = &mut test_rng();
        let size: usize = rng.gen_range(1..(2 as usize).pow(10));
        let domain = GeneralEvaluationDomain::<Fr>::new(size).unwrap();
        let batch_size = 32;
        let indices: Vec<_> = (0..batch_size)
            .into_iter()
            .map(|_| rng.gen_range(1..domain.size() + 1))
            .collect();
        let point = Fr::rand(rng);
        let evaluations = domain.batch_evaluate_lagrange_polynomial(indices.clone(), &point);

        indices.iter().enumerate().for_each(|(i, &j)| {
            assert_eq!(
                evaluations[i],
                domain.evaluate_lagrange_polynomial(j, &point)
            )
        });
    }
}
