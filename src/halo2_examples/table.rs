use std::marker::PhantomData;

use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::{Layouter, Value},
    plonk::{ConstraintSystem, TableColumn},
};

#[derive(Clone, Copy)]
pub(super) struct RangTableConfig<F: FieldExt> {
    pub(super) col_value: TableColumn,
    _marker: PhantomData<F>,
}

impl<F: FieldExt> RangTableConfig<F> {
    pub fn configure(meta: &mut ConstraintSystem<F>) -> Self {
        let table_column = meta.lookup_table_column();

        Self {
            col_value: table_column,
            _marker: PhantomData,
        }
    }

    pub fn load(
        &self,
        layouter: &mut impl Layouter<F>,
        values: Vec<usize>,
    ) -> Result<(), halo2_proofs::plonk::Error> {
        layouter.assign_table(
            || "range check",
            |mut table| {
                let mut offset = 0;

                println!("load values: {:?}", values);
                for el in values.clone() {
                    println!("assign cell, offset {:?}, element: {:?}", offset, el);
                    table.assign_cell(
                        || "assign table cell",
                        self.col_value,
                        offset,
                        || Value::known(F::from(el as u64)),
                    )?;
                    offset += 1;
                }

                Ok(())
            },
        )
    }
}

mod tests {
    use halo2_proofs::{
        arithmetic::FieldExt,
        circuit::{SimpleFloorPlanner, Value, floor_planner::V1},
        plonk::{Advice, Circuit, Column, Selector, Assigned},
        poly::Rotation, pasta::Fp, dev::MockProver,
    };

    use super::RangTableConfig;

    #[derive(Clone, Copy)]
    struct TestConfig<F: FieldExt> {
        a: Column<Advice>,
        q_selector: Selector,
        lookup_table: RangTableConfig<F>,
    }

    #[derive(Default)]
    struct MyCircuit<F: FieldExt> {
        value: Value<Assigned<F>>
    }

    impl<F: FieldExt> Circuit<F> for MyCircuit<F> {
        type Config = TestConfig<F>;

        type FloorPlanner = V1;

        fn without_witnesses(&self) -> Self {
            Self::default()
        }

        fn configure(meta: &mut halo2_proofs::plonk::ConstraintSystem<F>) -> Self::Config {
            let a = meta.advice_column();

            let q_selector = meta.complex_selector();

            let lookup_table = RangTableConfig::configure(meta);

            meta.lookup(|meta| {
                let q_selector = meta.query_selector(q_selector);

                let value = meta.query_advice(a, Rotation::cur());

                vec![(q_selector*value, lookup_table.col_value)]
            });

            TestConfig {
                a,
                q_selector,
                lookup_table,
            }
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl halo2_proofs::circuit::Layouter<F>,
        ) -> Result<(), halo2_proofs::plonk::Error> {
            config.lookup_table.load(&mut layouter, vec![0,3,4])?;

            layouter.assign_region(
                || "assign columns",
                |mut region| {
                    config.q_selector.enable(&mut region, 0)?;

                    region.assign_advice(
                        || "assign a",
                        config.a,
                        0,
                        || self.value,
                    )
                },
            )?;
            Ok(())
        }
    }

    #[test]
    pub fn test() {
        let test_value: u64 = 3;

        let circuit = MyCircuit::<Fp> { value: Value::known(Fp::from(test_value as u64).into()) };

        let prover = MockProver::run(4, &circuit, vec![]).unwrap();

        prover.assert_satisfied();

    }
}
