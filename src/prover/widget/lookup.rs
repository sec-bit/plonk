use ark_poly_commit::LinearCombination;
use ark_std::{cfg_into_iter, format, marker::PhantomData, vec, vec::Vec};

use crate::prover::Prover;
use crate::{Domain, Error, Field};

use super::Widget;

pub(crate) struct LookupWidget<F: Field, D: Domain<F>> {
    program_width: usize,
    wire_labels: Vec<String>,
    table_column_labels: Vec<String>,
    sorted_list_labels: Vec<String>,
    _field: PhantomData<F>,
    _domain: PhantomData<D>,
}

impl<F: Field, D: Domain<F>> LookupWidget<F, D> {
    const SELECTOR_LABELS: [&'static str; 2] = ["q_lookup", "q_table"];
    const AUXILARY_LABELS: [&'static str; 4] = ["s", "z_lookup", "lagrange_1", "lagrange_n"];

    pub fn new(program_width: usize) -> Self {
        Self {
            program_width,
            wire_labels: (0..program_width)
                .into_iter()
                .map(|i| format!("w_{}", i))
                .collect(),
            table_column_labels: (0..program_width)
                .into_iter()
                .map(|i| format!("table_{}", i))
                .collect(),
            sorted_list_labels: (0..program_width)
                .into_iter()
                .map(|i| format!("s_{}", i))
                .collect(),
            _field: PhantomData,
            _domain: PhantomData,
        }
    }
}

impl<F: Field, D: Domain<F>> Widget<F, D> for LookupWidget<F, D> {
    fn compute_oracles(&self, round: usize, prover: &mut Prover<F, D>) -> Result<(), Error> {
        if round == 1 {
            let eta = prover.get_challenge("eta")?;

            let values = prover.domain_values();
            let s = cfg_into_iter!((0..prover.domain_size()))
                .map(|i| {
                    combine(
                        eta,
                        self.sorted_list_labels
                            .iter()
                            .map(|l| values[l][i])
                            .collect(),
                    )
                })
                .collect();

            prover.insert("s", s);
        }

        if round == 2 {
            let eta = prover.get_challenge("eta")?;
            let beta = prover.get_challenge("beta")?;
            let gamma = prover.get_challenge("gamma")?;

            let values = prover.domain_values();
            let n = prover.domain_size();
            let t: Vec<_> = cfg_into_iter!((0..n))
                .map(|i| {
                    let t = combine(
                        eta,
                        self.table_column_labels
                            .iter()
                            .map(|l| values[l][i])
                            .collect(),
                    );
                    eta * t + values["q_table"][i]
                })
                .collect();
            let v: Vec<_> = cfg_into_iter!((0..n))
                .map(|i| {
                    if values["q_lookup"][i].is_zero() {
                        F::zero()
                    } else {
                        let v =
                            combine(eta, self.wire_labels.iter().map(|l| values[l][i]).collect());
                        (eta * v + values["q_table"][i]) * values["q_lookup"][i]
                    }
                })
                .collect();
            let s: Vec<_> = cfg_into_iter!((0..n))
                .map(|i| eta * values["s"][i] + values["q_table"][i])
                .collect();

            let beta_gamma_factor = (beta + F::one()) * gamma;
            let mut z = Vec::<F>::with_capacity(n);
            let mut acc = F::one();
            z.push(acc);
            cfg_into_iter!(0..(n - 1)).for_each(|i| {
                let numerator = (v[i] + gamma) * (t[i] + beta * t[i + 1] + beta_gamma_factor);
                let denominator = gamma * (s[i] + beta * s[i + 1] + beta_gamma_factor);
                acc *= numerator * denominator.inverse().unwrap();
                z.push(acc);
            });
            assert_eq!(z[n - 1], F::one());

            prover.insert("z_lookup", z);
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

        let eta = prover.get_challenge("eta")?;
        let beta = prover.get_challenge("beta")?;
        let gamma = prover.get_challenge("gamma")?;
        let alpha = prover.get_challenge("alpha")?;
        let values = prover.coset_values();

        let n = quotient.len();
        let t: Vec<_> = cfg_into_iter!((0..n))
            .map(|i| {
                let t = combine(
                    eta,
                    self.table_column_labels
                        .iter()
                        .map(|l| values[l][i])
                        .collect(),
                );
                eta * t + values["q_table"][i]
            })
            .collect();
        let v: Vec<_> = cfg_into_iter!((0..n))
            .map(|i| {
                let v = combine(eta, self.wire_labels.iter().map(|l| values[l][i]).collect());
                (eta * v + values["q_table"][i]) * values["q_lookup"][i]
            })
            .collect();
        let s: Vec<_> = cfg_into_iter!((0..n))
            .map(|i| eta * values["s"][i] + values["q_table"][i])
            .collect();

        let beta_gamma_factor = (beta + F::one()) * gamma;
        let alpha_2 = alpha.square();

        cfg_into_iter!((0..n)).for_each(|i| {
            let next_i = if i / self.program_width == (n / self.program_width - 1) {
                i % self.program_width
            } else {
                i + self.program_width
            };
            let numerator = values["z_lookup"][i]
                * (v[i] + gamma)
                * (t[i] + beta * t[next_i] + beta_gamma_factor);
            let denominator =
                values["z_lookup"][next_i] * gamma * (s[i] + beta * s[next_i] + beta_gamma_factor);

            quotient[i] += *combinator
                * (numerator - denominator
                    + (values["z_lookup"][i] - F::one()) * values["lagrange_1"][i] * alpha
                    + (values["z_lookup"][i] - F::one()) * values["lagrange_n"][i] * alpha_2)
        });

        *combinator *= alpha_2 * alpha;
        Ok(())
    }

    fn compute_linear_contribution(
        &self,
        prover: &mut Prover<F, D>,
        combinator: &mut F,
    ) -> Result<(LinearCombination<F>, F), Error> {
        let eta = prover.get_challenge("eta")?;
        let beta = prover.get_challenge("beta")?;
        let gamma = prover.get_challenge("gamma")?;
        let alpha = prover.get_challenge("alpha")?;
        let zeta = prover.get_challenge("zeta")?;

        let w_zeta = self
            .wire_labels
            .iter()
            .map(|l| prover.evaluate(l, "zeta"))
            .collect::<Result<Vec<_>, Error>>()?;
        let q_loolup_zeta = prover.evaluate("q_lookup", "zeta")?;
        let q_table_zeta = prover.evaluate("q_table", "zeta")?;
        let q_table_zeta_omega = prover.evaluate("q_table", "zeta_omega")?;
        let s_zeta_omega = prover.evaluate("s", "zeta_omega")?;
        let z_lookup_zeta_omega = prover.evaluate("z_lookup", "zeta_omega")?;

        let table_lc = {
            let mut etas = Vec::with_capacity(self.program_width);
            let mut acc = F::one();
            for _ in 0..self.program_width {
                etas.push(acc);
                acc *= eta;
            }
            LinearCombination::new(
                "table",
                self.table_column_labels
                    .iter()
                    .zip(etas)
                    .map(|(l, e)| (e, l.to_string()))
                    .collect(),
            )
        };
        let table_zeta = prover.evaluate_linear_combination(&table_lc, "zeta")?;
        let table_zeta_omega = prover.evaluate_linear_combination(&table_lc, "zeta_omega")?;

        let alpha_2 = alpha.square();
        let beta_gamma_factor = (beta + F::one()) * gamma;
        let lagrange_1_zeta = prover.domain.evaluate_lagrange_polynomial(1, &zeta);
        let lagrange_n_zeta = prover
            .domain
            .evaluate_lagrange_polynomial(prover.domain_size(), &zeta);

        let numerator = {
            let v_zeta = eta * combine(eta, w_zeta) + q_table_zeta;
            let t_zeta = eta * table_zeta + q_table_zeta;
            let t_zeta_omega = eta * table_zeta_omega + q_table_zeta_omega;

            (q_loolup_zeta * v_zeta + gamma) * (t_zeta + beta * t_zeta_omega + beta_gamma_factor)
        };
        let denominator = z_lookup_zeta_omega * gamma * eta;

        let lc = LinearCombination::new(
            "lookup",
            vec![
                (
                    *combinator * (numerator + alpha * lagrange_1_zeta + alpha_2 * lagrange_n_zeta),
                    "z_lookup",
                ),
                (-*combinator * denominator, "s"),
            ],
        );
        let complement = *combinator
            * (z_lookup_zeta_omega
                * gamma
                * (q_table_zeta
                    + beta * (q_table_zeta_omega + eta * s_zeta_omega)
                    + beta_gamma_factor)
                + alpha * lagrange_1_zeta
                + alpha_2 * lagrange_n_zeta);

        *combinator *= alpha_2 * alpha;

        Ok((lc, complement))
    }
}

fn combine<F: Field>(challenge: F, mut values: Vec<F>) -> F {
    let mut acc = F::zero();
    while let Some(v) = values.pop() {
        acc = acc * challenge + v
    }

    acc
}

#[cfg(test)]
mod tests {

    use ark_bn254::Fr;
    use ark_ff::{One, Zero};
    use ark_poly::{univariate::DensePolynomial, EvaluationDomain, UVPolynomial};
    use ark_std::{cfg_iter_mut, test_rng, UniformRand};

    use crate::composer::{Composer, Table};
    use crate::GeneralEvaluationDomain;

    use super::*;

    #[test]
    fn prover_lookup() -> Result<(), Error> {
        let mut cs = {
            let mut cs = Composer::new(4);
            let table_index = cs.add_table(Table::xor_table(2));
            let x = cs.alloc(Fr::from(1));
            let y = cs.alloc(Fr::from(2));
            let z = cs.read_from_table(table_index, vec![x, y])?;
            cs.enforce_constant(z[0], Fr::from(3));

            cs
        };
        let rng = &mut test_rng();
        let widget = LookupWidget::new(cs.program_width);

        print!("initializing...");
        let mut prover = Prover::<Fr, GeneralEvaluationDomain<Fr>>::new(&cs.compute_prover_key()?);
        let wires = cs.compute_wire_values()?;
        for (k, w) in wires.into_iter() {
            prover.insert(&k, w);
        }
        println!("done");

        print!("compute s polynomial...");
        prover.add_challenge("eta", Fr::rand(rng));
        widget.compute_oracles(1, &mut prover)?;
        println!("done");
        debug_assert!(prover.coset_values().contains_key("s"), "s is not added");

        print!("compute accumulator polynomial...");
        prover.add_challenge("beta", Fr::rand(rng));
        prover.add_challenge("gamma", Fr::rand(rng));
        widget.compute_oracles(2, &mut prover)?;
        println!("done");
        debug_assert!(
            prover.coset_values().contains_key("z_lookup"),
            "z_lookup is not added"
        );

        {
            // check division
            let polys = prover.polynomials();
            let eta = prover.get_challenge("eta")?;
            let beta = prover.get_challenge("beta")?;
            let gamma = prover.get_challenge("gamma")?;
            let beta_gamma_factor = (beta + Fr::one()) * gamma;
            use ark_poly::Polynomial;
            for (i, omega) in prover.domain.elements().enumerate() {
                let shifted_omega = omega * prover.domain.generator();

                let w_omega = {
                    let mut v = eta * polys["w_3"].evaluate(&omega) + polys["w_2"].evaluate(&omega);
                    v = eta * v + polys["w_1"].evaluate(&omega);
                    v = eta * v + polys["w_0"].evaluate(&omega);
                    v = eta * v + polys["q_table"].evaluate(&omega);
                    v
                };
                let table_omega = {
                    let mut v =
                        eta * polys["table_3"].evaluate(&omega) + polys["table_2"].evaluate(&omega);
                    v = eta * v + polys["table_1"].evaluate(&omega);
                    v = eta * v + polys["table_0"].evaluate(&omega);
                    v = eta * v + polys["q_table"].evaluate(&omega);

                    v
                };
                let table_shifted_omega = {
                    let mut v = eta * polys["table_3"].evaluate(&shifted_omega)
                        + polys["table_2"].evaluate(&shifted_omega);
                    v = eta * v + polys["table_1"].evaluate(&shifted_omega);
                    v = eta * v + polys["table_0"].evaluate(&shifted_omega);
                    v = eta * v + polys["q_table"].evaluate(&shifted_omega);

                    v
                };
                let s_omega = {
                    let s = polys["s"].evaluate(&omega);
                    s * eta + polys["q_table"].evaluate(&omega)
                };
                let s_shifted_omega = {
                    let s = polys["s"].evaluate(&shifted_omega);
                    s * eta + polys["q_table"].evaluate(&shifted_omega)
                };

                let numerator = polys["z_lookup"].evaluate(&omega)
                    * (polys["q_lookup"].evaluate(&omega) * w_omega + gamma)
                    * (beta * table_shifted_omega + table_omega + beta_gamma_factor);
                let denominator = polys["z_lookup"].evaluate(&shifted_omega)
                    * gamma
                    * (beta * s_shifted_omega + s_omega + beta_gamma_factor);

                print!("checking divisiblity at root {}...", i);
                assert_eq!(numerator - denominator, Fr::zero());
                println!("ok");
            }
        }

        print!("compute quotient...");
        prover.add_challenge("alpha", Fr::rand(rng));
        let mut quotient = vec![Fr::zero(); prover.coset_size()];
        let mut combinator = Fr::one();
        widget.compute_quotient_contribution(&mut prover, &mut combinator, &mut quotient)?;
        let vi = prover.get_coset_values("vi")?;
        cfg_iter_mut!(quotient)
            .zip(vi.iter())
            .for_each(|(q, v)| *q *= v);
        let t = DensePolynomial::from_coefficients_vec(prover.coset.coset_ifft(&quotient));
        prover.add_polynomial("t", t);
        println!("done");

        // third round
        print!("compute linearization...");
        let zeta = Fr::rand(rng);
        prover.add_challenge("zeta", zeta);
        prover.add_challenge("zeta_omega", zeta * prover.domain.generator());
        let mut combinator = Fr::one();
        let (r, complement) = widget.compute_linear_contribution(&mut prover, &mut combinator)?;
        println!("done");

        print!("check equality...");
        let r_zeta = prover.evaluate_linear_combination(&r, "zeta")?;
        let t_zeta = prover.evaluate("t", "zeta")?;
        let v_zeta = prover.domain.evaluate_vanishing_polynomial(zeta);

        println!("lookup widget lhs: {}", t_zeta * v_zeta);
        println!("lookup widget rhs: {}", r_zeta - complement);
        assert_eq!(t_zeta * v_zeta, r_zeta - complement, "lookup gate");
        println!("done");

        Ok(())
    }
}
