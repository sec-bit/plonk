use ark_std::vec::Vec;

use crate::Field;

use super::{Composer, Domain, Wire};

impl<F: Field> Composer<F> {
    pub(super) fn compute_sigmas(&self, domain: impl Domain<F>) -> Vec<Vec<F>> {
        let length = domain.size();
        let sigmas = {
            let mut sigmas: Vec<Vec<Wire>> = Vec::with_capacity(self.program_width);
            for col in 0..self.program_width {
                sigmas.push((0..length).map(|row| Wire::new(col, row)).collect())
            }

            for wires in self.epicycles.iter() {
                if wires.len() <= 1 {
                    continue;
                }

                for (curr, curr_wire) in wires.iter().enumerate() {
                    let next = match curr {
                        0 => wires.len() - 1,
                        _ => curr - 1,
                    };
                    let next_wire = &wires[next];

                    sigmas[curr_wire.col][curr_wire.row] = *next_wire;
                }
            }

            sigmas
        };

        let roots: Vec<_> = domain.elements().collect();
        let mut sigma_values = Vec::with_capacity(self.program_width);
        for sigma in sigmas {
            sigma_values.push(
                sigma
                    .iter()
                    .map(|w| roots[w.row] * F::coset_generator(w.col))
                    .collect(),
            );
        }
        sigma_values
    }
}

#[cfg(test)]
mod tests {
    use ark_bn254::Fr;
    use ark_poly::EvaluationDomain;
    use ark_std::cfg_iter;

    use crate::GeneralEvaluationDomain;

    use super::*;

    fn composer_permutation() {
        let mut cs = Composer::new(4);
        let (var_0, var_1, var_2, var_3) = (
            cs.alloc_variable(Fr::from(1)),
            cs.alloc_variable(Fr::from(2)),
            cs.alloc_variable(Fr::from(3)),
            cs.alloc_variable(Fr::from(4)),
        );
        let arrange: Vec<_> = vec![
            (var_1, var_0, var_0, var_2),
            (var_0, var_1, var_3, var_0),
            (var_2, var_0, var_1, var_0),
            (var_0, var_2, var_3, var_0),
        ];
        arrange.into_iter().for_each(|(w_0, w_1, w_2, w_3)| {
            cs.insert_gate(vec![w_0, w_1, w_2, w_3]);
        });

        check_permutation(&mut cs);
    }

    fn check_permutation(cs: &mut Composer<Fr>) {
        let pk = cs
            .compute_prover_key::<GeneralEvaluationDomain<Fr>>()
            .unwrap();
        let domain = pk.domain;
        let sigmas = cs.compute_sigmas(domain);

        let (id_0, id_1, id_2, id_3) = {
            let roots: Vec<_> = domain.elements().collect();
            let id_0: Vec<_> = cfg_iter!(roots)
                .map(|r| Fr::coset_generator(0) * r)
                .collect();
            let id_1: Vec<_> = cfg_iter!(roots)
                .map(|r| Fr::coset_generator(1) * r)
                .collect();
            let id_2: Vec<_> = cfg_iter!(roots)
                .map(|r| Fr::coset_generator(2) * r)
                .collect();
            let id_3: Vec<_> = cfg_iter!(roots)
                .map(|r| Fr::coset_generator(3) * r)
                .collect();
            (id_0, id_1, id_2, id_3)
        };

        let sigma: Vec<_> = sigmas.iter().map(|sigma| sigma.iter().product()).collect();
        let sigma_prod: Fr = sigma.iter().product();
        let id: Vec<_> = [id_0, id_1, id_2, id_3]
            .iter()
            .map(|id| id.iter().product())
            .collect();
        let id_prod: Fr = id.iter().product();
        assert_eq!(sigma_prod, id_prod);
    }
}
