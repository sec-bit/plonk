use ark_poly_commit::LinearCombination;
use ark_std::{cfg_into_iter, format, marker::PhantomData, vec, vec::Vec};

#[cfg(feature = "parallel")]
use rayon::prelude::*;

use crate::prover::{Error, Prover};
use crate::{Domain, Field};

use super::Widget;

pub(crate) struct PermutationWidget<F: Field, D: Domain<F>> {
    program_width: usize,
    wire_labels: Vec<String>,
    sigma_labels: Vec<String>,
    _field: PhantomData<F>,
    _domain: PhantomData<D>,
}

impl<'a, F: Field, D: Domain<F>> PermutationWidget<F, D> {
    const AUXILARY_LABELS: [&'static str; 3] = ["z", "linear", "lagrange_1"];

    pub fn new(program_width: usize) -> Self {
        Self {
            program_width,
            wire_labels: (0..program_width)
                .into_iter()
                .map(|i| format!("w_{}", i))
                .collect(),
            sigma_labels: (0..program_width)
                .into_iter()
                .map(|i| format!("sigma_{}", i))
                .collect(),
            _field: PhantomData,
            _domain: PhantomData,
        }
    }
}

impl<F: Field, D: Domain<F>> Widget<F, D> for PermutationWidget<F, D> {
    fn compute_oracles(&self, round: usize, prover: &mut Prover<F, D>) -> Result<(), Error> {
        if round == 2 {
            let values = prover.domain_values();
            let z = {
                let beta = prover.get_challenge("beta")?;
                let gamma = prover.get_challenge("gamma")?;
                let roots: Vec<_> = prover.domain.elements().collect();

                let n = prover.domain_size();
                let perms: Vec<_> = cfg_into_iter!((0..n))
                    .map(|i| {
                        let numerator_factor =
                            |(j, w)| values[w][i] + F::coset_generator(j) * beta * roots[i] + gamma;
                        let numerator = self
                            .wire_labels
                            .iter()
                            .enumerate()
                            .map(numerator_factor)
                            .product::<F>();

                        let denominator_factor =
                            |(w, sigma)| values[w][i] + beta * values[sigma][i] + gamma;
                        let denominator = self
                            .wire_labels
                            .iter()
                            .zip(self.sigma_labels.iter())
                            .map(denominator_factor)
                            .product::<F>();

                        numerator * denominator.inverse().unwrap()
                    })
                    .collect();

                let mut z = Vec::<F>::with_capacity(n);
                let mut acc = F::one();
                z.push(acc);
                cfg_into_iter!(0..(n - 1)).for_each(|i| {
                    acc *= perms[i];
                    z.push(acc);
                });
                assert_eq!(z[n - 1] * perms[n - 1], F::one());

                z
            };
            prover.insert("z", z);
        }
        Ok(())
    }

    fn compute_quotient_contribution(
        &self,
        prover: &mut Prover<F, D>,
        combinator: &mut F,
        quotient: &mut [F],
    ) -> Result<(), Error> {
        assert_eq!(quotient.len(), prover.coset_size());

        let beta = prover.get_challenge("beta")?;
        let gamma = prover.get_challenge("gamma")?;
        let alpha = prover.get_challenge("alpha")?;

        let values = prover.coset_values();
        let n = quotient.len();
        cfg_into_iter!((0..n)).for_each(|i| {
            let next_i = if i / self.program_width == (n / self.program_width - 1) {
                i % self.program_width
            } else {
                i + self.program_width
            };

            let numerator_factor =
                |(j, w)| values[w][i] + F::coset_generator(j) * beta * values["linear"][i] + gamma;
            let numerator = values["z"][i]
                * self
                    .wire_labels
                    .iter()
                    .enumerate()
                    .map(numerator_factor)
                    .product::<F>();

            let denominator_factor = |(w, sigma)| values[w][i] + beta * values[sigma][i] + gamma;
            let denominator = values["z"][next_i]
                * self
                    .wire_labels
                    .iter()
                    .zip(self.sigma_labels.iter())
                    .map(denominator_factor)
                    .product::<F>();

            quotient[i] += *combinator
                * (numerator - denominator
                    + (values["z"][i] - F::one()) * values["lagrange_1"][i] * alpha)
        });

        *combinator *= alpha.square();
        Ok(())
    }

    fn compute_linear_contribution(
        &self,
        prover: &mut Prover<F, D>,
        combinator: &mut F,
    ) -> Result<(LinearCombination<F>, F), Error> {
        let beta = prover.get_challenge("beta")?;
        let gamma = prover.get_challenge("gamma")?;
        let alpha = prover.get_challenge("alpha")?;
        let zeta = prover.get_challenge("zeta")?;

        let mut w_zeta = self
            .wire_labels
            .iter()
            .map(|l| prover.evaluate(l, "zeta"))
            .collect::<Result<Vec<_>, Error>>()?;

        let mut sigma_labels: Vec<_> = self.sigma_labels.iter().collect();
        let last_sigma = sigma_labels.pop().unwrap();
        let sigma_zeta = sigma_labels
            .into_iter()
            .map(|l| prover.evaluate(l, "zeta"))
            .collect::<Result<Vec<_>, Error>>()?;

        let z_zeta_omega = prover.evaluate("z", "zeta_omega")?;

        let numerator_factor = |(j, &w)| w + F::coset_generator(j) * beta * zeta + gamma;
        let numerator = w_zeta
            .iter()
            .enumerate()
            .map(numerator_factor)
            .product::<F>();

        let denominator_factor = |(&w, &sigma)| w + beta * sigma + gamma;
        let denominator = beta
            * z_zeta_omega
            * w_zeta
                .iter()
                .zip(sigma_zeta.iter())
                .map(denominator_factor)
                .product::<F>();
        let lagrange_1_zeta = prover.domain.evaluate_lagrange_polynomial(1, &zeta);

        let lc = LinearCombination::new(
            "permutation",
            vec![
                (*combinator * (numerator + alpha * lagrange_1_zeta), "z"),
                (-*combinator * denominator, last_sigma),
            ],
        );

        let complement = {
            let last_w_zeta = w_zeta.pop().unwrap();
            let product = w_zeta
                .into_iter()
                .zip(sigma_zeta)
                .map(|(w, sigma)| w + beta * sigma + gamma)
                .product::<F>();
            *combinator * (product * (last_w_zeta + gamma) * z_zeta_omega + alpha * lagrange_1_zeta)
        };

        *combinator *= alpha.square();

        Ok((lc, complement))
    }
}

#[cfg(test)]
mod tests {

    use ark_bn254::Fr;
    use ark_ff::Zero;
    use ark_poly::{univariate::DensePolynomial, EvaluationDomain, UVPolynomial};
    use ark_std::{cfg_iter_mut, test_rng, UniformRand};

    use crate::composer::Composer;
    use crate::GeneralEvaluationDomain;

    use super::*;

    #[test]
    fn prover_permutation() -> Result<(), Error> {
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
        let widget = PermutationWidget::new(cs.program_width);

        print!("initializing...");
        let mut prover = Prover::<Fr, GeneralEvaluationDomain<Fr>>::new(&cs.compute_prover_key()?);
        let wires = cs.compute_wire_values()?;
        for (k, w) in wires.into_iter() {
            prover.insert(&k, w);
        }
        println!("done");

        print!("compute accumulator polynomial...");
        prover.add_challenge("beta", Fr::rand(rng));
        prover.add_challenge("gamma", Fr::rand(rng));
        widget.compute_oracles(2, &mut prover)?;
        println!("done");

        {
            debug_assert!(prover.coset_values().contains_key("z"), "z is not added");
            // check division
            let polys = prover.polynomials();
            let beta = prover.get_challenge("beta")?;
            let gamma = prover.get_challenge("gamma")?;
            use ark_poly::Polynomial;
            for (i, omega) in prover.domain.elements().enumerate() {
                let numerator = polys["z"].evaluate(&omega)
                    * (polys["w_0"].evaluate(&omega)
                        + beta * omega * Fr::coset_generator(0)
                        + gamma)
                    * (polys["w_1"].evaluate(&omega)
                        + beta * omega * Fr::coset_generator(1)
                        + gamma)
                    * (polys["w_2"].evaluate(&omega)
                        + beta * omega * Fr::coset_generator(2)
                        + gamma)
                    * (polys["w_3"].evaluate(&omega)
                        + beta * omega * Fr::coset_generator(3)
                        + gamma);
                let denominator = polys["z"].evaluate(&(omega * prover.domain.generator()))
                    * (polys["w_0"].evaluate(&omega)
                        + beta * polys["sigma_0"].evaluate(&omega)
                        + gamma)
                    * (polys["w_1"].evaluate(&omega)
                        + beta * polys["sigma_1"].evaluate(&omega)
                        + gamma)
                    * (polys["w_2"].evaluate(&omega)
                        + beta * polys["sigma_2"].evaluate(&omega)
                        + gamma)
                    * (polys["w_3"].evaluate(&omega)
                        + beta * polys["sigma_3"].evaluate(&omega)
                        + gamma);
                print!("checking divisiblity at root {}...", i);
                assert_eq!(numerator - denominator, Fr::zero());
                println!("ok");
            }
        }

        print!("compute quotient...");
        prover.add_challenge("alpha", Fr::rand(rng));
        let mut quotient = vec![Fr::zero(); prover.coset_size()];
        let mut combinator = prover.get_challenge("alpha")?;
        widget.compute_quotient_contribution(&mut prover, &mut combinator, &mut quotient)?;
        let vi = prover.get_coset_values("vi")?;
        cfg_iter_mut!(quotient)
            .zip(vi.iter())
            .for_each(|(q, v)| *q *= v);
        let t = DensePolynomial::from_coefficients_vec(prover.coset.coset_ifft(&quotient));
        prover.add_polynomial("t", t);
        println!("done");

        print!("compute linearization...");
        let zeta = Fr::rand(rng);
        prover.add_challenge("zeta", zeta);
        prover.add_challenge("zeta_omega", zeta * prover.domain.generator());
        let mut combinator = prover.get_challenge("alpha")?;
        let (r, complement) = widget.compute_linear_contribution(&mut prover, &mut combinator)?;
        println!("done");

        print!("check equality...");
        let r_zeta = prover.evaluate_linear_combination(&r, "zeta")?;
        let t_zeta = prover.evaluate("t", "zeta")?;
        let v_zeta = prover.domain.evaluate_vanishing_polynomial(zeta);
        assert_eq!(t_zeta * v_zeta, r_zeta - complement, "permutation gate");
        println!("done");

        Ok(())
    }
}
