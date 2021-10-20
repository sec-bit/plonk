use ark_poly_commit::LinearCombination;

use crate::prover::Prover;
use crate::{Domain, Error, Field};

mod arithmetic;
pub(crate) use arithmetic::ArithmeticWidget;

mod permutation;
pub(crate) use permutation::PermutationWidget;

mod range;
pub(crate) use range::RangeWidget;

mod lookup;
pub(crate) use lookup::LookupWidget;

pub(crate) trait Widget<F: Field, D: Domain<F>> {
    fn compute_oracles(&self, round: usize, prover: &mut Prover<F, D>) -> Result<(), Error>;

    fn compute_quotient_contribution(
        &self,
        prover: &mut Prover<F, D>,
        combinator: &mut F,
        quotient: &mut [F],
    ) -> Result<(), Error>;

    fn compute_linear_contribution(
        &self,
        prover: &mut Prover<F, D>,
        combinator: &mut F,
    ) -> Result<(LinearCombination<F>, F), Error>;
}
