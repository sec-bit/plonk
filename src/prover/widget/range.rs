use ark_poly_commit::LinearCombination;
use ark_std::{cfg_into_iter, format, marker::PhantomData, vec::Vec};

#[cfg(feature = "parallel")]
use rayon::prelude::*;

use crate::prover::Prover;
use crate::{Domain, Error, Field};

use super::Widget;

pub(crate) struct RangeWidget<F: Field, D: Domain<F>> {
    program_width: usize,
    wire_labels: Vec<String>,
    _field: PhantomData<F>,
    _domain: PhantomData<D>,
}

impl<F: Field, D: Domain<F>> RangeWidget<F, D> {
    const SELECTOR_LABELS: [&'static str; 1] = ["q_range"];

    pub fn new(program_width: usize) -> Self {
        assert!(program_width >= 4);
        Self {
            program_width,
            wire_labels: (0..program_width)
                .into_iter()
                .map(|i| format!("w_{}", i))
                .collect(),
            _field: PhantomData,
            _domain: PhantomData,
        }
    }
}

impl<F: Field, D: Domain<F>> Widget<F, D> for RangeWidget<F, D> {
    fn compute_oracles(&self, _: usize, _: &mut Prover<F, D>) -> Result<(), Error> {
        Ok(())
    }

    fn compute_quotient_contribution(
        &self,
        prover: &mut Prover<F, D>,
        combinator: &mut F,
        quotient: &mut [F],
    ) -> Result<(), Error> {
        assert_eq!(quotient.len(), prover.coset_size());

        let alpha = prover.get_challenge("alpha")?;
        let eta = prover.get_challenge("eta")?;

        let values = prover.coset_values();
        let n = quotient.len();
        cfg_into_iter!((0..quotient.len())).for_each(|i| {
            let next_i = if i / self.program_width == (n / self.program_width - 1) {
                i % self.program_width
            } else {
                i + self.program_width
            };

            let mut quads: Vec<_> = (0..self.program_width - 1)
                .into_iter()
                .map(|j| {
                    quad(
                        values[&self.wire_labels[j]][i],
                        values[&self.wire_labels[j + 1]][i],
                    )
                })
                .collect();
            quads.push(quad(
                values[&self.wire_labels[self.program_width - 1]][i],
                values[&self.wire_labels[0]][next_i],
            ));

            quotient[i] += *combinator * values["q_range"][i] * combine(eta, quads);
        });

        *combinator *= alpha;

        Ok(())
    }

    fn compute_linear_contribution(
        &self,
        prover: &mut Prover<F, D>,
        combinator: &mut F,
    ) -> Result<(LinearCombination<F>, F), Error> {
        let eta = prover.get_challenge("eta")?;
        let alpha = prover.get_challenge("alpha")?;

        let quads = {
            let w_zeta = self
                .wire_labels
                .iter()
                .map(|l| prover.evaluate(l, "zeta"))
                .collect::<Result<Vec<_>, Error>>()?;
            let w_zeta_omega = prover.evaluate("w_0", "zeta_omega")?;

            let mut quads: Vec<_> = (0..self.program_width - 1)
                .into_iter()
                .map(|j| quad(w_zeta[j], w_zeta[j + 1]))
                .collect();
            quads.push(quad(w_zeta[self.program_width - 1], w_zeta_omega));

            quads
        };

        let lc = LinearCombination::new(
            "range",
            vec![(*combinator * combine(eta, quads), "q_range")],
        );

        *combinator *= alpha;

        Ok((lc, F::zero()))
    }
}

#[inline]
fn quad<F: Field>(lower: F, higher: F) -> F {
    let mut v = lower;
    v += v;
    v += v;
    v = higher - v;
    (0..4).into_iter().map(|i| v - F::from(i as u64)).product()
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
    use ark_ff::Zero;
    use ark_poly::{univariate::DensePolynomial, EvaluationDomain, UVPolynomial};
    use ark_std::{cfg_iter_mut, test_rng, UniformRand};

    use crate::composer::Composer;
    use crate::GeneralEvaluationDomain;

    use super::*;

    #[test]
    fn prover_range() -> Result<(), Error> {
        let mut cs = {
            let mut cs = Composer::new(4);
            let var = cs.alloc(Fr::from(15));
            cs.enforce_range(var, 14)?;

            cs
        };
        let rng = &mut test_rng();
        let widget = RangeWidget::new(cs.program_width);

        print!("initializing...");
        let mut prover = Prover::<Fr, GeneralEvaluationDomain<Fr>>::new(&cs.compute_prover_key()?);
        let wires = cs.compute_wire_values()?;
        for (k, w) in wires.into_iter() {
            prover.insert(&k, w);
        }
        prover.add_challenge("eta", Fr::rand(rng));
        println!("done");

        {
            // check division
            let polys = prover.polynomials();
            let eta = prover.get_challenge("eta")?;
            use ark_poly::Polynomial;
            for (i, omega) in prover.domain.elements().enumerate() {
                let q_range_omega = polys["q_range"].evaluate(&omega);
                let mut quads: Vec<_> = (0..3)
                    .into_iter()
                    .map(|j| {
                        quad(
                            polys[&format!("w_{}", j)].evaluate(&omega),
                            polys[&format!("w_{}", j + 1)].evaluate(&omega),
                        )
                    })
                    .collect();
                quads.push(quad(
                    polys[&format!("w_3")].evaluate(&omega),
                    polys[&format!("w_0")].evaluate(&(omega * prover.domain.generator())),
                ));

                print!("checking divisiblity at root {}...", i);
                assert_eq!(q_range_omega * combine(eta, quads), Fr::zero());
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
        let mut combinator = prover.get_challenge("alpha")?;
        prover.add_challenge("zeta", zeta);
        prover.add_challenge("zeta_omega", zeta * prover.domain.generator());
        let (r, complement) = widget.compute_linear_contribution(&mut prover, &mut combinator)?;
        println!("done");

        print!("check equality...");
        let r_zeta = prover.evaluate_linear_combination(&r, "zeta")?;
        let t_zeta = prover.evaluate("t", "zeta")?;
        let v_zeta = prover.domain.evaluate_vanishing_polynomial(zeta);
        assert_eq!(t_zeta * v_zeta, r_zeta - complement, "range gate");
        println!("done");

        Ok(())
    }
}
