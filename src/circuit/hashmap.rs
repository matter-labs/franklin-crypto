use bellman::pairing::{
    Engine,
};

use bellman::{
    SynthesisError,
    ConstraintSystem
};

use super::{
    Assignment
};

use super::num::AllocatedNum;

use super::boolean::{
    AllocatedBit,
    Boolean
};

use super::permutation::{
    PermutationField
};

impl<E: Engine> PermutationField<E> for Vec<AllocatedNum<E>>
{
    fn switch_2x2<CS>(
        mut cs: CS,
        a: &Self,
        b: &Self,
        switched_on: bool
    ) -> Result<(Self, Self), SynthesisError>
        where CS: ConstraintSystem<E>
    {
        assert_eq!(a.len(), b.len());

        let mut c = vec![];
        let mut d = vec![];

        if (a.len() == 1){
            let c_value = match (a[0].get_value(), b[0].get_value(), switched_on){
                (Some(a), Some(b), false) => Some(a),
                (Some(a), Some(b), true) => Some(b),
                (_, _, _) => None
            };
            c.push(AllocatedNum::alloc(
                cs.namespace(|| "c"),
                || c_value.grab()
            )?);

            let d_value = match (a[0].get_value(), b[0].get_value(), switched_on){
                (Some(a), Some(b), false) => Some(b),
                (Some(a), Some(b), true) => Some(a),
                (_, _, _) => None
            };
            d.push(AllocatedNum::alloc(
                cs.namespace(|| "d"),
                || d_value.grab()
            )?);

            cs.enforce(
                || "(a == c) || (a == d)",
                |lc| lc + a[0].get_variable() - c[0].get_variable(),
                |lc| lc + a[0].get_variable() - d[0].get_variable(),
                |lc| lc
            );
            cs.enforce(
                || "a + b == c + d",
                |lc| lc + a[0].get_variable() + b[0].get_variable(),
                |lc| lc + CS::one(),
                |lc| lc + c[0].get_variable() + d[0].get_variable(),
            );
        }
        else {
            let switch = Boolean::from(AllocatedBit::alloc(
                cs.namespace(|| "switch variable"),
                Some(switched_on)
            )?);

            for (i, (a, b)) in a.iter().zip(b).enumerate() {
                c.push(AllocatedNum::conditionally_select(
                    cs.namespace(|| format!("c[{}]", i)), a, b, &switch.not())?
                );

                d.push(AllocatedNum::conditionally_select(
                    cs.namespace(|| format!("d[{}]", i)), a, b, &switch)?
                );
            }
        }

        Ok((c, d))
    }
}
