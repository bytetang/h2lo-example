use std::marker::PhantomData;

use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::{AssignedCell, Chip, Layouter, SimpleFloorPlanner},
    plonk::{Advice, Circuit, Column, ConstraintSystem, Error, Instance, Selector},
    poly::Rotation,
};

#[derive(Clone, Debug)]
struct FieldConfig {
    // f(n-2)
    a: Column<Advice>,
    // f(n-1)
    b: Column<Advice>,
    // f(n)
    c: Column<Advice>,
    // selector
    selector: Selector,
    // instance
    instance: Column<Instance>,
}

struct FabonacciChip<F: FieldExt> {
    config: FieldConfig,
    _marker: PhantomData<F>,
}

impl<F: FieldExt> Chip<F> for FabonacciChip<F> {
    type Config = FieldConfig;

    type Loaded = ();

    fn config(&self) -> &Self::Config {
        &self.config
    }

    fn loaded(&self) -> &Self::Loaded {
        &()
    }
}

impl<F: FieldExt> FabonacciChip<F> {
    fn construct(config: <Self as Chip<F>>::Config) -> Self {
        Self {
            config: config,
            _marker: PhantomData,
        }
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> <Self as Chip<F>>::Config {
        let a = meta.advice_column();
        let b = meta.advice_column();
        let c = meta.advice_column();
        let instance = meta.instance_column();

        let selector = meta.selector();

        meta.enable_equality(a);
        meta.enable_equality(b);
        meta.enable_equality(c);

        meta.enable_equality(instance);

        meta.create_gate("addition gate", |meta| {
            let a_exp = meta.query_advice(a, Rotation::cur());
            let b_exp = meta.query_advice(b, Rotation::cur());
            let c_exp = meta.query_advice(c, Rotation::cur());
            let selector_exp = meta.query_selector(selector);

            vec![selector_exp * ((a_exp + b_exp) - c_exp)]
        });

        FieldConfig {
            a,
            b,
            c,
            selector,
            instance,
        }
    }
}

trait FabonacciInstruction<F: FieldExt>: Chip<F> {
    fn assign_first_row(
        &self,
        layouter: impl Layouter<F>,
    ) -> Result<(AssignedCell<F, F>, AssignedCell<F, F>, AssignedCell<F, F>), Error>;

    fn assign_row(
        &self,
        layouter: impl Layouter<F>,
        prev_b: &AssignedCell<F, F>,
        prev_c: &AssignedCell<F, F>,
    ) -> Result<AssignedCell<F, F>, Error>;

    fn expose_public(
        &self,
        layouter: impl Layouter<F>,
        out: &AssignedCell<F, F>,
        row: usize,
    ) -> Result<(), Error>;
}

impl<F: FieldExt> FabonacciInstruction<F> for FabonacciChip<F> {
    fn assign_first_row(
        &self,
        mut layouter: impl Layouter<F>,
    ) -> Result<(AssignedCell<F, F>, AssignedCell<F, F>, AssignedCell<F, F>), Error> {
        let config = self.config();

        layouter.assign_region(
            || "fabonacci",
            |mut region| {
                config.selector.enable(&mut region, 0)?;
                let a_cell = region.assign_advice_from_instance(
                    || "load f0",
                    config.instance,
                    0,
                    config.a,
                    0,
                )?;

                let b_cell = region.assign_advice_from_instance(
                    || "load f1",
                    config.instance,
                    1,
                    config.b,
                    0,
                )?;

                let c_cell = region.assign_advice(
                    || "a + b",
                    config.c,
                    0,
                    || a_cell.value().copied() + b_cell.value(),
                )?;

                Ok((a_cell, b_cell, c_cell))
            },
        )
    }

    fn assign_row(
        &self,
        mut layouter: impl Layouter<F>,
        prev_b: &AssignedCell<F, F>,
        prev_c: &AssignedCell<F, F>,
    ) -> Result<AssignedCell<F, F>, Error> {
        let config = self.config();
        layouter.assign_region(
            || "next row",
            |mut region| {
                prev_b.copy_advice(|| "cp to a", &mut region, config.a, 0)?;

                prev_c.copy_advice(|| "cp to b", &mut region, config.b, 0)?;

                let c_cell = region.assign_advice(
                    || "c",
                    config.c,
                    0,
                    || prev_b.value().copied() + prev_c.value(),
                )?;

                Ok(c_cell)
            },
        )
    }

    fn expose_public(
        &self,
        mut layouter: impl Layouter<F>,
        out: &AssignedCell<F, F>,
        row: usize,
    ) -> Result<(), Error> {
        layouter.constrain_instance(out.cell(), self.config.instance, row)
    }
}

#[derive(Default)]
struct MyCircuit {
    k: usize
}

impl<F: FieldExt> Circuit<F> for MyCircuit {
    type Config = FieldConfig;

    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        FabonacciChip::configure(meta)
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        let chip = FabonacciChip::construct(config);

        let (_, mut prev_b, mut prev_c) =
            chip.assign_first_row(layouter.namespace(|| "first row"))?;

        // left include, right exclude
        for _n in 3..self.k {
            let c_cell = chip.assign_row(layouter.namespace(|| "next row"), &prev_b, &prev_c)?;

            println!("index: {:?}, prev_b:{:?}, prev_c: {:?}", _n, prev_b.value(), prev_c.value());

            prev_b = prev_c;
            prev_c = c_cell;
        }

        chip.expose_public(layouter.namespace(|| "out"), &prev_c, 2)?;

        Ok(())
    }
}

mod tests {
    use std::{marker::PhantomData, vec};

    use halo2_proofs::{pasta::Fp, dev::MockProver};

    use super::MyCircuit;


    #[test]
    fn test() {
        let my_circuit = MyCircuit {
            k: 10
        };

        let a = Fp::from(1);
        let b = Fp::from(1);

        let out = Fp::from(55);

        let mut public_input = vec![a, b, out];

        let prover = MockProver::run(4, &my_circuit, vec![public_input.clone()]).unwrap();
        prover.assert_satisfied();

        public_input[2] += Fp::one();

        let _prover = MockProver::run(4, &my_circuit, vec![public_input]).unwrap();
        assert!(_prover.verify().is_err());

    }
}