use ark_poly_commit::LinearCombination;
use ark_std::{cfg_into_iter, format, marker::PhantomData, vec, vec::Vec};

#[cfg(feature = "parallel")]
use rayon::prelude::*;

use crate::prover::Prover;
use crate::{Domain, Error, Field};

use super::Widget;

pub(crate) struct ArithmeticWidget<F: Field, D: Domain<F>> {
    wire_labels: Vec<String>,
    scaling_labels: Vec<String>,
    _field: PhantomData<F>,
    _domain: PhantomData<D>,
}

impl<F: Field, D: Domain<F>> ArithmeticWidget<F, D> {
    const SELECTOR_LABELS: [&'static str; 4] = ["q_arith", "q_m", "q_c", "pi"];

    pub fn new(program_width: usize) -> Self {
        assert!(program_width >= 2);
        Self {
            wire_labels: (0..program_width)
                .into_iter()
                .map(|i| format!("w_{}", i))
                .collect(),
            scaling_labels: (0..program_width)
                .into_iter()
                .map(|i| format!("q_{}", i))
                .collect(),
            _field: PhantomData,
            _domain: PhantomData,
        }
    }
}

impl<F: Field, D: Domain<F>> Widget<F, D> for ArithmeticWidget<F, D> {
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

        let values = prover.coset_values();
        cfg_into_iter!((0..quotient.len())).for_each(|i| {
            let sum = self
                .wire_labels
                .iter()
                .zip(self.scaling_labels.iter())
                .map(|(w, q)| values[w][i] * values[q][i])
                .sum::<F>();

            quotient[i] += *combinator
                * values["q_arith"][i]
                * (-values["pi"][i]
                    + values["q_m"][i] * values["w_0"][i] * values["w_1"][i]
                    + values["q_c"][i]
                    + sum);
        });

        let alpha = prover.get_challenge("alpha")?;
        *combinator *= alpha;

        Ok(())
    }

    fn compute_linear_contribution(
        &self,
        prover: &mut Prover<F, D>,
        combinator: &mut F,
    ) -> Result<(LinearCombination<F>, F), Error> {
        let q_arith_zeta = *combinator * prover.evaluate("q_arith", "zeta")?;
        let w_0_zeta = prover.evaluate("w_0", "zeta")?;
        let w_1_zeta = prover.evaluate("w_1", "zeta")?;

        let mut terms = vec![
            (q_arith_zeta * w_0_zeta * w_1_zeta, "q_m"),
            (q_arith_zeta, "q_c"),
        ];
        for (w, q) in self.wire_labels.iter().zip(self.scaling_labels.iter()) {
            let w_zeta = prover.evaluate(w, "zeta")?;
            terms.push((q_arith_zeta * w_zeta, q));
        }

        let lc = LinearCombination::new("arithmetic", terms);

        let alpha = prover.get_challenge("alpha")?;
        *combinator *= alpha;

        Ok((lc, F::zero()))
    }
}

#[cfg(test)]
mod tests {
    use ark_bn254::Fr;
    use ark_ff::{One, Zero};
    use ark_poly::{univariate::DensePolynomial, EvaluationDomain, UVPolynomial};
    use ark_std::{cfg_iter_mut, test_rng, UniformRand};

    use crate::composer::Composer;
    use crate::prover::{Error, Prover};
    use crate::GeneralEvaluationDomain;

    use super::*;

    #[test]
    fn prover_arithmetic() -> Result<(), Error> {
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
        let widget = ArithmeticWidget::new(cs.program_width);

        print!("initializing...");
        let mut prover = Prover::<Fr, GeneralEvaluationDomain<Fr>>::new(&cs.compute_prover_key()?);
        let public_input = cs.compute_public_input();
        prover.insert("pi", public_input.to_vec());
        let wires = cs.compute_wire_values()?;
        for (k, w) in wires.into_iter() {
            prover.insert(&k, w);
        }
        println!("done");

        print!("compute quotient...");
        prover.add_challenge("alpha", Fr::rand(rng));
        let mut quotient = vec![Fr::zero(); prover.coset_size()];
        // the combinator for arithmetic widget has to be one, due to the presence of the public input.
        widget.compute_quotient_contribution(&mut prover, &mut Fr::one(), &mut quotient)?;
        let p = DensePolynomial::from_coefficients_vec(prover.coset.coset_ifft(&quotient));
        let (_, remainder) = p.divide_by_vanishing_poly(prover.domain).unwrap();
        assert_eq!(remainder, DensePolynomial::zero(), "division");
        let vi = prover.get_coset_values("vi")?;
        cfg_iter_mut!(quotient).zip(vi).for_each(|(q, v)| *q *= v);
        let t = DensePolynomial::from_coefficients_vec(prover.coset.coset_ifft(&quotient));
        prover.add_polynomial("t", t);
        println!("done");

        print!("compute linearization...");
        let zeta = Fr::rand(rng);
        prover.add_challenge("zeta", zeta);
        prover.add_challenge("zeta_omega", zeta * prover.domain.generator());
        let (r, complement) = widget.compute_linear_contribution(&mut prover, &mut Fr::one())?;
        println!("done");

        println!("check equality...");
        let r_zeta = prover.evaluate_linear_combination(&r, "zeta")?;
        let t_zeta = prover.evaluate("t", "zeta")?;
        let v_zeta = prover.domain.evaluate_vanishing_polynomial(zeta);
        let q_arith_zeta = prover.evaluate("q_arith", "zeta")?;
        let pi_zeta = prover.evaluate("pi", "zeta")?;
        assert_eq!(
            t_zeta * v_zeta,
            r_zeta - q_arith_zeta * pi_zeta - complement,
            "arithmetic gate"
        );
        println!("done");

        Ok(())
    }
}
