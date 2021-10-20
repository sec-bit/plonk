use ark_ff::batch_inversion;
use ark_poly::univariate::DensePolynomial;
use ark_poly_commit::{BatchLCProof, PolynomialCommitment};
use ark_std::{string::String, vec::Vec};

use crate::utils::interpolate_and_coset_fft;
use crate::{Domain, Field, Map};

use super::Error;

#[derive(Debug)]
pub(crate) struct ProverKey<F: Field, D: Domain<F>> {
    pub circuit_size: usize,
    pub input_size: usize,
    pub program_width: usize,
    pub domain: D,
    pub coset: D,
    domain_values: Map<String, Vec<F>>,
    coset_values: Map<String, Vec<F>>,
    polynomials: Map<String, DensePolynomial<F>>,
}

impl<F: Field, D: Domain<F>> ProverKey<F, D> {
    pub fn new(
        circuit_size: usize,
        input_size: usize,
        program_width: usize,
    ) -> Result<Self, Error> {
        let domain = D::new(circuit_size).ok_or(Error::PolynomialDegreeTooLarge)?;

        let coset = D::new(domain.size() * program_width).ok_or(Error::PolynomialDegreeTooLarge)?;

        let coset_values = {
            let mut coset_values = Map::new();

            coset_values.insert(
                "lagrange_1".to_string(),
                coset.coset_fft(&domain.lagrange_polynomial(1)),
            );
            coset_values.insert(
                "lagrange_n".to_string(),
                coset.coset_fft(&domain.lagrange_polynomial(domain.size())),
            );
            coset_values.insert(
                "linear".to_string(),
                coset.coset_fft(&[F::zero(), F::one()]),
            );

            let mut vi = coset.coset_fft(&domain.vanishing_polynomial());
            batch_inversion(&mut vi);
            coset_values.insert("vi".to_string(), vi);

            coset_values
        };

        Ok(Self {
            circuit_size,
            input_size,
            program_width,
            domain,
            coset,
            domain_values: Map::new(),
            coset_values,
            polynomials: Map::new(),
        })
    }

    pub fn domain_generator(&self) -> F {
        self.domain.generator()
    }

    pub fn domain_size(&self) -> usize {
        self.domain.size()
    }

    pub fn coset_size(&self) -> usize {
        self.coset.size()
    }

    pub fn domain_values(&self) -> Map<String, Vec<F>> {
        self.domain_values.clone()
    }

    pub fn coset_values(&self) -> Map<String, Vec<F>> {
        self.coset_values.clone()
    }

    pub fn polynomials(&self) -> Map<String, DensePolynomial<F>> {
        self.polynomials.clone()
    }

    pub fn insert(&mut self, label: &str, domain_values: Vec<F>) {
        debug_assert!(
            domain_values.len() <= self.domain.size(),
            "when generating key {}, {} provided values are provided, which exceeds domain size of {}",
            label,
            domain_values.len(),
            self.domain.size()
        );

        let (domain_values, coset_values, polynomial) =
            interpolate_and_coset_fft(domain_values, self.domain, self.coset);

        self.domain_values.insert(label.to_string(), domain_values);
        self.coset_values.insert(label.to_string(), coset_values);
        self.polynomials.insert(label.to_string(), polynomial);
    }
}

pub struct Proof<F: Field, PC: PolynomialCommitment<F, DensePolynomial<F>>> {
    pub commitments: Vec<Vec<PC::Commitment>>,
    pub evaluations: Vec<F>,
    pub pc_proof: BatchLCProof<F, DensePolynomial<F>, PC>,
}
