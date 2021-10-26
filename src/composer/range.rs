use ark_ff::BigInteger;
use ark_std::{format, vec::Vec};

use crate::{Error, Field};

use super::{Composer, Variable};

impl<F: Field> Composer<F> {
    /// here we enforce range constraint by quads (2-bit unit), so `num_bits` must be even.
    /// The quads are orgnized in the big-endian order
    pub fn enforce_range(&mut self, var: Variable, num_bits: usize) -> Result<usize, Error> {
        assert!(!self.is_finalized);
        assert!(self.program_width >= 4);
        assert_eq!((num_bits >> 1) << 1, num_bits);

        let value = self.assignments[var.0].into_repr();
        if value.num_bits() as usize > num_bits {
            return Err(Error::VariableOutOfRange(format!(
                "Variable {} has value {}, which exceeds the expected bit length of {}",
                var.0, value, num_bits
            )));
        }

        let mut accumulators = {
            let num_quads = num_bits >> 1;
            let num_gates = num_quads / self.program_width;

            let mut accumulators = Vec::with_capacity(num_gates * self.program_width);
            if num_quads % self.program_width != 0 {
                for _ in 0..self.program_width - num_quads % self.program_width {
                    accumulators.push(Self::null());
                }
            }
            accumulators.push(Self::null());

            let mut acc = F::zero();
            for i in (1..num_quads).rev() {
                // acc = 4 * acc + quad
                let quad = F::from_repr(BigInteger::from_bits_le(&[
                    value.get_bit(2 * i),
                    value.get_bit(2 * i + 1),
                ]))
                .unwrap();

                acc += acc;
                acc += acc;
                acc += quad;
                accumulators.push(self.alloc(acc));
            }

            assert_eq!(
                {
                    let quad = F::from_repr(BigInteger::from_bits_le(&[
                        value.get_bit(0),
                        value.get_bit(1),
                    ]))
                    .unwrap();
                    acc += acc;
                    acc += acc;

                    acc + quad
                },
                F::from_repr(value).unwrap()
            );

            accumulators
        };

        while accumulators.len() >= self.program_width {
            let index = self.insert_gate(accumulators.drain(0..self.program_width).collect());
            self.selectors.get_mut("q_range").unwrap()[index] = F::one();
        }
        let index = self.insert_gate(vec![var]);

        Ok(index)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_bn254::Fr;
    use ark_ff::{One, Zero};

    #[test]
    fn composer_range() -> Result<(), Error> {
        let mut cs = Composer::new(4);
        let var = cs.alloc(Fr::from(15));
        cs.enforce_range(var, 8)?;
        cs.finalize();

        assert_eq!(cs.size(), 2);
        assert_eq!(cs.selectors["q_range"], vec![Fr::one(), Fr::zero()]);
        assert_eq!(cs.selectors["q_arith"], vec![Fr::zero(), Fr::zero()]);
        assert_eq!(cs.selectors["q_lookup"], vec![Fr::zero(), Fr::zero()]);
        assert_eq!(cs.selectors["q_table"], vec![Fr::zero(), Fr::zero()]);
        assert_eq!(cs.selectors["q_m"], vec![Fr::zero(), Fr::zero()]);
        assert_eq!(cs.selectors["q_c"], vec![Fr::zero(), Fr::zero()]);
        assert_eq!(cs.selectors["q_0"], vec![Fr::zero(), Fr::zero()]);
        assert_eq!(cs.selectors["q_1"], vec![Fr::zero(), Fr::zero()]);
        assert_eq!(cs.selectors["q_2"], vec![Fr::zero(), Fr::zero()]);
        assert_eq!(cs.selectors["q_3"], vec![Fr::zero(), Fr::zero()]);
        assert_eq!(cs.wires["w_0"], vec![Variable(0), Variable(1)]);
        assert_eq!(cs.wires["w_1"], vec![Variable(2), Variable(0)]);
        assert_eq!(cs.wires["w_2"], vec![Variable(3), Variable(0)]);
        assert_eq!(cs.wires["w_3"], vec![Variable(4), Variable(0)]);

        for (i, v) in cs.assignments.iter().enumerate() {
            println!("{}: {}", i, v);
        }

        let mut cs = Composer::new(4);
        let var = cs.alloc(Fr::from(13));
        cs.enforce_range(var, 14)?;
        cs.finalize();

        assert_eq!(cs.size(), 3);
        assert_eq!(
            cs.selectors["q_range"],
            vec![Fr::one(), Fr::one(), Fr::zero()]
        );
        assert_eq!(
            cs.selectors["q_arith"],
            vec![Fr::zero(), Fr::zero(), Fr::zero()]
        );
        assert_eq!(
            cs.selectors["q_lookup"],
            vec![Fr::zero(), Fr::zero(), Fr::zero()]
        );
        assert_eq!(
            cs.selectors["q_table"],
            vec![Fr::zero(), Fr::zero(), Fr::zero()]
        );
        assert_eq!(
            cs.selectors["q_m"],
            vec![Fr::zero(), Fr::zero(), Fr::zero()]
        );
        assert_eq!(
            cs.selectors["q_c"],
            vec![Fr::zero(), Fr::zero(), Fr::zero()]
        );
        assert_eq!(
            cs.selectors["q_0"],
            vec![Fr::zero(), Fr::zero(), Fr::zero()]
        );
        assert_eq!(
            cs.selectors["q_1"],
            vec![Fr::zero(), Fr::zero(), Fr::zero()]
        );
        assert_eq!(
            cs.selectors["q_2"],
            vec![Fr::zero(), Fr::zero(), Fr::zero()]
        );
        assert_eq!(
            cs.selectors["q_3"],
            vec![Fr::zero(), Fr::zero(), Fr::zero()]
        );
        assert_eq!(cs.wires["w_0"], vec![Variable(0), Variable(4), Variable(1)]);
        assert_eq!(cs.wires["w_1"], vec![Variable(0), Variable(5), Variable(0)]);
        assert_eq!(cs.wires["w_2"], vec![Variable(2), Variable(6), Variable(0)]);
        assert_eq!(cs.wires["w_3"], vec![Variable(3), Variable(7), Variable(0)]);

        Ok(())
    }
}
