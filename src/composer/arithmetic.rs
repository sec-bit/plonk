use ark_std::{format, vec, vec::Vec};

use crate::Field;

use super::{Composer, Variable};

/// arithmetic gates
impl<F: Field> Composer<F> {
    /// o = l + r
    pub fn add(&mut self, var_l: Variable, var_r: Variable) -> Variable {
        let var_o = self.alloc_variable(self.assignments[var_l.0] + self.assignments[var_r.0]);
        self.add_gate(var_l, var_r, var_o);

        var_o
    }

    pub fn add_gate(&mut self, var_l: Variable, var_r: Variable, var_o: Variable) {
        self.poly_gate(
            vec![(var_l, F::one()), (var_r, F::one()), (var_o, -F::one())],
            F::zero(),
            F::zero(),
        )
    }

    /// o = l * r
    pub fn mul(&mut self, var_l: Variable, var_r: Variable) -> Variable {
        let var_o = self.alloc_variable(self.assignments[var_l.0] * self.assignments[var_r.0]);
        self.mul_gate(var_l, var_r, var_o);

        var_o
    }

    pub fn mul_gate(&mut self, var_l: Variable, var_r: Variable, var_o: Variable) {
        self.poly_gate(
            vec![(var_l, F::zero()), (var_r, F::zero()), (var_o, -F::one())],
            F::one(),
            F::zero(),
        )
    }

    /// var = value
    pub fn enforce_constant(&mut self, var: Variable, value: F) {
        self.poly_gate(vec![(var, F::one())], F::zero(), -value);
    }

    /// q_arith * (q_0 * w_0 + q_1 * w_1 + q_2 * w_2 + q_3 * w_3 + q_m * w_0 * w_1 + q_c) = 0
    pub fn poly_gate(&mut self, wires: Vec<(Variable, F)>, mul_scaling: F, const_scaling: F) {
        assert!(!self.is_finalized);
        assert!(wires.len() <= self.program_width);

        let index = self.insert_gate(wires.iter().map(|(v, _)| *v).collect());
        for i in 0..wires.len() {
            self.selectors.get_mut(&format!("q_{}", i)).unwrap()[index] = wires[i].1;
        }
        self.selectors.get_mut("q_m").unwrap()[index] = mul_scaling;
        self.selectors.get_mut("q_c").unwrap()[index] = const_scaling;
        self.selectors.get_mut("q_arith").unwrap()[index] = F::one();
    }
}

#[cfg(test)]
pub mod tests {
    use ark_bn254::Fr;
    use ark_ff::Zero;

    use super::*;

    #[test]
    fn composer_arithmetic() {
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
        cs.finalize();

        debug_assert_eq!(
            cs.size(),
            6,
            "test circuit has wrong size {}, should be 6",
            cs.size()
        );
        debug_assert_eq!(
            cs.input_size(),
            1,
            "
        test circuit has wrong input size {}, should be 1",
            cs.input_size()
        );

        check_arithmetic(&mut cs);
    }

    fn check_arithmetic(cs: &mut Composer<Fr>) {
        let mut pi = cs.compute_public_input();
        pi.extend(vec![Fr::zero(); cs.size() - cs.input_size()]);
        for i in 0..cs.size() {
            let v = cs.selectors["q_arith"][i]
                * (cs.selectors["q_0"][i] * cs.assignments[cs.wires["w_0"][i].0]
                    + cs.selectors["q_1"][i] * cs.assignments[cs.wires["w_1"][i].0]
                    + cs.selectors["q_2"][i] * cs.assignments[cs.wires["w_2"][i].0]
                    + cs.selectors["q_3"][i] * cs.assignments[cs.wires["w_3"][i].0]
                    + cs.selectors["q_m"][i]
                        * cs.assignments[cs.wires["w_0"][i].0]
                        * cs.assignments[cs.wires["w_1"][i].0]
                    + cs.selectors["q_c"][i]
                    - pi[i]);
            assert!(v.is_zero());
        }
    }
}
