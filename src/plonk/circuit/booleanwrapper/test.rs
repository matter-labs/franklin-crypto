#[cfg(test)]
mod test {

    use super::super::base::*;
    use crate::bellman::pairing::bn256::Bn256;
    use crate::bellman::pairing::Engine;
    use crate::bellman::plonk::better_better_cs::cs::*;
    use crate::bellman::plonk::better_better_cs::cs::{TrivialAssembly, Width4MainGateWithDNext};
    use crate::bellman::SynthesisError;
    use crate::plonk::circuit::boolean::{AllocatedBit, Boolean};
    use plonk::circuit::booleanwrapper::utils::{smart_and, smart_or};
    #[test]
    fn test_1() {
        //with the usual call of the same methods with the same variables, two constraints are formed
        struct TestCircuit {
            value_1: Option<bool>,
            value_2: Option<bool>,
            value_3: Option<bool>,
            value_4: Option<bool>,
            value_5: Option<bool>,
            value_6: Option<bool>,
            value_7: Option<bool>,
        }
        impl<E: Engine> Circuit<E> for TestCircuit {
            type MainGate = Width4MainGateWithDNext;

            fn declare_used_gates() -> Result<Vec<Box<dyn GateInternal<E>>>, SynthesisError> {
                Ok(vec![Width4MainGateWithDNext::default().into_internal()])
            }

            fn synthesize<CS: ConstraintSystem<E>>(
                &self,
                cs: &mut CS,
            ) -> Result<(), SynthesisError> {
                let value_1 = AllocatedBit::alloc(cs, self.value_1).unwrap();
                let value_2 = AllocatedBit::alloc(cs, self.value_2).unwrap();
                let value_3 = AllocatedBit::alloc(cs, self.value_3).unwrap();
                let value_4 = AllocatedBit::alloc(cs, self.value_4).unwrap();
                let value_5 = AllocatedBit::alloc(cs, self.value_5).unwrap();
                let value_6 = AllocatedBit::alloc(cs, self.value_6).unwrap();
                let value_7 = AllocatedBit::alloc(cs, self.value_7).unwrap();

                let _experiment_1 = Boolean::xor(cs, &Boolean::Is(value_1), &Boolean::Is(value_2));
                let _experiment_2 = Boolean::xor(cs, &Boolean::Is(value_1), &Boolean::Is(value_2));

                let _experiment_3 = Boolean::or(cs, &Boolean::Is(value_3), &Boolean::Is(value_4));
                let _experiment_4 = Boolean::or(cs, &Boolean::Is(value_3), &Boolean::Is(value_4));

                let _experiment_5 = Boolean::and(cs, &Boolean::Not(value_2), &Boolean::Is(value_4));
                let _experiment_6 = Boolean::and(cs, &Boolean::Not(value_2), &Boolean::Is(value_4));

                let _experiment_7 = Boolean::conditionally_select(
                    cs,
                    &Boolean::Is(value_1),
                    &Boolean::Is(value_2),
                    &Boolean::Is(value_4),
                );
                let _experiment_8 = Boolean::conditionally_select(
                    cs,
                    &Boolean::Is(value_1),
                    &Boolean::Is(value_2),
                    &Boolean::Is(value_4),
                );

                let _experiment_9 = smart_and(
                    cs,
                    &[
                        Boolean::Not(value_2),
                        Boolean::Is(value_4),
                        Boolean::Is(value_5),
                        Boolean::Not(value_6),
                        Boolean::Is(value_7),
                    ],
                );
                let _experiment_10 = smart_or(
                    cs,
                    &[
                        Boolean::Not(value_2),
                        Boolean::Is(value_4),
                        Boolean::Is(value_3),
                        Boolean::Not(value_6),
                        Boolean::Is(value_7),
                    ],
                );

                Ok(())
            }
        }

        let circuit = TestCircuit {
            value_1: Some(true),
            value_2: Some(true),
            value_3: Some(false),
            value_4: Some(false),
            value_5: Some(true),
            value_6: Some(false),
            value_7: Some(true),
        };

        let mut assembly = TrivialAssembly::<
            Bn256,
            PlonkCsWidth4WithNextStepParams,
            Width4MainGateWithDNext,
        >::new();

        circuit.synthesize(&mut assembly).expect("must work");
        println!("Number of constraints without optimization");
        println!("Assembly contains {} gates", assembly.n());
        println!(
            "Total length of all tables: {}",
            assembly.total_length_of_all_tables
        );
        assert!(assembly.is_satisfied());
    }

    #[test]
    fn test_2() {
        //The test shows the number of constants with optimization
        struct TestCircuit {
            value_1: Option<bool>,
            value_2: Option<bool>,
            value_3: Option<bool>,
            value_4: Option<bool>,
            value_5: Option<bool>,
            value_6: Option<bool>,
            value_7: Option<bool>,
        }
        impl<E: Engine> Circuit<E> for TestCircuit {
            type MainGate = Width4MainGateWithDNext;

            fn declare_used_gates() -> Result<Vec<Box<dyn GateInternal<E>>>, SynthesisError> {
                Ok(vec![Width4MainGateWithDNext::default().into_internal()])
            }

            fn synthesize<CS: ConstraintSystem<E>>(
                &self,
                cs: &mut CS,
            ) -> Result<(), SynthesisError> {
                let value_1 = AllocatedBit::alloc(cs, self.value_1).unwrap();
                let value_2 = AllocatedBit::alloc(cs, self.value_2).unwrap();
                let value_3 = AllocatedBit::alloc(cs, self.value_3).unwrap();
                let value_4 = AllocatedBit::alloc(cs, self.value_4).unwrap();
                let value_5 = AllocatedBit::alloc(cs, self.value_5).unwrap();
                let value_6 = AllocatedBit::alloc(cs, self.value_6).unwrap();
                let value_7 = AllocatedBit::alloc(cs, self.value_7).unwrap();

                let _experiment_1 = BooleanWrapper::xor(
                    cs,
                    &BooleanWrapper(Boolean::Is(value_1)),
                    &BooleanWrapper(Boolean::Is(value_2)),
                );
                let _experiment_2 = BooleanWrapper::xor(
                    cs,
                    &BooleanWrapper(Boolean::Is(value_1)),
                    &BooleanWrapper(Boolean::Is(value_2)),
                );

                let _experiment_3 = BooleanWrapper::or(
                    cs,
                    &BooleanWrapper(Boolean::Is(value_3)),
                    &BooleanWrapper(Boolean::Is(value_4)),
                );
                let _experiment_4 = BooleanWrapper::or(
                    cs,
                    &BooleanWrapper(Boolean::Is(value_3)),
                    &BooleanWrapper(Boolean::Is(value_4)),
                );

                let _experiment_5 = BooleanWrapper::and(
                    cs,
                    &BooleanWrapper(Boolean::Not(value_2)),
                    &BooleanWrapper(Boolean::Is(value_4)),
                );
                let _experiment_6 = BooleanWrapper::and(
                    cs,
                    &BooleanWrapper(Boolean::Not(value_2)),
                    &BooleanWrapper(Boolean::Is(value_4)),
                );

                let _experiment_7 = BooleanWrapper::conditionally_select(
                    cs,
                    &BooleanWrapper(Boolean::Is(value_1)),
                    &BooleanWrapper(Boolean::Is(value_2)),
                    &BooleanWrapper(Boolean::Is(value_4)),
                );
                let _experiment_8 = BooleanWrapper::conditionally_select(
                    cs,
                    &BooleanWrapper(Boolean::Is(value_1)),
                    &BooleanWrapper(Boolean::Is(value_2)),
                    &BooleanWrapper(Boolean::Is(value_4)),
                );

                let _experiment_9 = BooleanWrapper::smart_and(
                    cs,
                    &[
                        BooleanWrapper(Boolean::Not(value_2)),
                        BooleanWrapper(Boolean::Is(value_4)),
                        BooleanWrapper(Boolean::Is(value_5)),
                        BooleanWrapper(Boolean::Not(value_6)),
                        BooleanWrapper(Boolean::Is(value_7)),
                    ],
                );
                let _experiment_10 = BooleanWrapper::smart_and(
                    cs,
                    &[
                        BooleanWrapper(Boolean::Not(value_2)),
                        BooleanWrapper(Boolean::Is(value_4)),
                        BooleanWrapper(Boolean::Is(value_3)),
                        BooleanWrapper(Boolean::Not(value_6)),
                        BooleanWrapper(Boolean::Is(value_7)),
                    ],
                );
                Ok(())
            }
        }

        let circuit = TestCircuit {
            value_1: Some(true),
            value_2: Some(true),
            value_3: Some(false),
            value_4: Some(false),
            value_5: Some(true),
            value_6: Some(false),
            value_7: Some(true),
        };

        let mut assembly = TrivialAssembly::<
            Bn256,
            PlonkCsWidth4WithNextStepParams,
            Width4MainGateWithDNext,
        >::new();

        circuit.synthesize(&mut assembly).expect("must work");
        println!("Number of constraints with optimization");
        println!("Assembly contains {} gates", assembly.n());
        println!(
            "Total length of all tables: {}",
            assembly.total_length_of_all_tables
        );
        assert!(assembly.is_satisfied());
    }
}
