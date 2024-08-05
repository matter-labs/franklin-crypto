use super::*;

use boojum::field::traits::field_like::PrimeFieldLike;
use boojum::field::goldilocks::GoldilocksField as GL;

#[derive(Derivative)]
#[derivative(Clone, Copy, Debug(bound = ""), Hash(bound = ""))]
pub struct GoldilocksAsFieldWrapper<E: Engine, CS: ConstraintSystem<E>> {
    inner: GoldilocksField<E>,
    #[derivative(Debug = "ignore", Hash = "ignore")]
    _marker: std::marker::PhantomData<fn() -> CS>,
}

impl<E: Engine, CS: ConstraintSystem<E>> From<GoldilocksField<E>> for GoldilocksAsFieldWrapper<E, CS> {
    fn from(value: GoldilocksField<E>) -> Self {
        Self {
            inner: value,
            _marker: std::marker::PhantomData,
        }
    }
}

impl<E: Engine, CS: ConstraintSystem<E>> std::fmt::Display for GoldilocksAsFieldWrapper<E, CS> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "Num as PrimeFieldLike{{")?;
        writeln!(f, "inner num: {:?},", self.inner.inner)?;
        writeln!(f, "}}")
    }
}

impl<E: Engine, CS: ConstraintSystem<E>> GoldilocksAsFieldWrapper<E, CS> {
    pub fn conditionally_select(cs: &mut CS, bit: Boolean, first: &Self, second: &Self) -> Self {
        let inner = GoldilocksField::conditionally_select(cs, bit, &first.inner, &second.inner).unwrap();
        inner.into()
    }
}

impl<E: Engine, CS: ConstraintSystem<E>> PrimeFieldLike for GoldilocksAsFieldWrapper<E, CS>
where
    CS: 'static,
{
    type Base = GL;
    type Context = CS;

    // identities
    fn zero(_ctx: &mut Self::Context) -> Self {
        let inner = GoldilocksField::zero();
        inner.into()
    }

    fn one(_ctx: &mut Self::Context) -> Self {
        let inner = GoldilocksField::one();
        inner.into()
    }

    fn minus_one(_ctx: &mut Self::Context) -> Self {
        let inner = GoldilocksField::minus_one();
        inner.into()
    }

    // Arithmetics. Expressed in mutable way. It would not matter in after inlining
    fn add_assign(&'_ mut self, other: &Self, ctx: &mut Self::Context) -> &'_ mut Self {
        let new = self.inner.add(ctx, &other.inner).unwrap();
        *self = new.into();

        self
    }

    fn sub_assign(&'_ mut self, other: &Self, ctx: &mut Self::Context) -> &'_ mut Self {
        let mut other_negate = *other;
        other_negate.negate(ctx);
        self.add_assign(&other_negate, ctx);

        self
    }

    fn mul_assign(&'_ mut self, other: &Self, ctx: &mut Self::Context) -> &'_ mut Self {
        let new = self.inner.mul(ctx, &other.inner).unwrap();
        *self = new.into();

        self
    }

    fn square(&'_ mut self, ctx: &mut Self::Context) -> &'_ mut Self {
        let this = self.inner;
        let new = self.inner.mul(ctx, &this).unwrap();
        *self = new.into();

        self
    }

    fn negate(&'_ mut self, ctx: &mut Self::Context) -> &'_ mut Self {
        self.inner = self.inner.negate(ctx).unwrap();

        self
    }

    fn double(&'_ mut self, ctx: &mut Self::Context) -> &'_ mut Self {
        let this = self.inner;
        let new = self.inner.add(ctx, &this).unwrap();
        *self = new.into();

        self
    }

    // infallible inverse
    fn inverse(&self, ctx: &mut Self::Context) -> Self {
        self.inner.inverse(ctx).unwrap().into()
    }

    // constant creation
    fn constant(value: Self::Base, _ctx: &mut Self::Context) -> Self {
        GoldilocksField::constant_from_field(value).into()
    }
}


#[derive(Derivative)]
#[derivative(Clone, Copy, Debug(bound = ""), Hash(bound = ""))]
pub struct GoldilocksExtAsFieldWrapper<E: Engine, CS: ConstraintSystem<E>> {
    inner: GoldilocksFieldExt<E>,
    #[derivative(Debug = "ignore", Hash = "ignore")]
    _marker: std::marker::PhantomData<fn() -> CS>,
}

impl<E: Engine, CS: ConstraintSystem<E>> From<GoldilocksFieldExt<E>> for GoldilocksExtAsFieldWrapper<E, CS> {
    fn from(value: GoldilocksFieldExt<E>) -> Self {
        Self {
            inner: value,
            _marker: std::marker::PhantomData,
        }
    }
}

impl<E: Engine, CS: ConstraintSystem<E>> std::fmt::Display for GoldilocksExtAsFieldWrapper<E, CS> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "Num as PrimeFieldLike{{")?;
        writeln!(f, "inner field coeffs: {:?},", self.inner)?;
        writeln!(f, "}}")
    }
}

impl<E: Engine, CS: ConstraintSystem<E>> GoldilocksExtAsFieldWrapper<E, CS> {
    pub fn conditionally_select(cs: &mut CS, bit: Boolean, first: &Self, second: &Self) -> Self {
        let inner = GoldilocksFieldExt::conditionally_select(cs, bit, &first.inner, &second.inner).unwrap();
        inner.into()
    }

    pub fn from_coeffs_in_base(coeffs: [GoldilocksField<E>; 2]) -> Self {
        let inner = GoldilocksFieldExt::from_coords(coeffs);
        inner.into()
    }

    pub const fn into_coeffs_in_base(self) -> [GoldilocksField<E>; 2] {
        [self.inner.inner[0], self.inner.inner[1]]
    }

    pub fn from_wrapper_coeffs_in_base(coeffs: [GoldilocksAsFieldWrapper<E, CS>; 2]) -> Self {
        let coeffs = [
            coeffs[0].inner,
            coeffs[1].inner,
        ];
        Self::from_coeffs_in_base(coeffs)
    }

    pub fn mul_by_base_and_accumulate_into(
        dst: &mut Self,
        base: &GoldilocksAsFieldWrapper<E, CS>,
        other: &Self,
        cs: &mut CS,
    ) -> Result<(), SynthesisError> {
        for (dst, src) in dst.inner.inner.iter_mut()
            .zip(other.inner.inner.iter()) {
            *dst = src.mul_add(cs, &base.inner, dst)?;
        }

        Ok(())
    }

    pub fn mul_assign_by_base(
        &mut self, 
        cs: &mut CS, 
        base: &GoldilocksAsFieldWrapper<E, CS>
    ) -> Result<(), SynthesisError> {
        for dst in self.inner.inner.iter_mut() {
            *dst = dst.mul(cs, &base.inner)?;
        }

        Ok(())
    }
}

impl<E: Engine, CS: ConstraintSystem<E>> PrimeFieldLike for GoldilocksExtAsFieldWrapper<E, CS>
where
    CS: 'static,
{
    type Base = GL;
    type Context = CS;

    // identities
    fn zero(_ctx: &mut Self::Context) -> Self {
        let inner = GoldilocksFieldExt::zero();
        inner.into()
    }

    fn one(_ctx: &mut Self::Context) -> Self {
        let inner = GoldilocksFieldExt::one();
        inner.into()
    }

    fn minus_one(_ctx: &mut Self::Context) -> Self {
        let inner = GoldilocksFieldExt::minus_one();
        inner.into()
    }

    // Arithmetics. Expressed in mutable way. It would not matter in after inlining
    fn add_assign(&'_ mut self, other: &Self, ctx: &mut Self::Context) -> &'_ mut Self {
        let new = self.inner.add(ctx, &other.inner).unwrap();
        *self = new.into();

        self
    }

    fn sub_assign(&'_ mut self, other: &Self, ctx: &mut Self::Context) -> &'_ mut Self {
        let mut other_negate = *other;
        other_negate.negate(ctx);
        self.add_assign(&other_negate, ctx);

        self
    }

    fn mul_assign(&'_ mut self, other: &Self, ctx: &mut Self::Context) -> &'_ mut Self {
        let new = self.inner.mul(ctx, &other.inner).unwrap();
        *self = new.into();

        self
    }

    fn square(&'_ mut self, ctx: &mut Self::Context) -> &'_ mut Self {
        let this = self.inner;
        let new = self.inner.mul(ctx, &this).unwrap();
        *self = new.into();

        self
    }

    fn negate(&'_ mut self, ctx: &mut Self::Context) -> &'_ mut Self {
        self.inner = self.inner.negate(ctx).unwrap();

        self
    }

    fn double(&'_ mut self, ctx: &mut Self::Context) -> &'_ mut Self {
        let this = self.inner;
        let new = self.inner.add(ctx, &this).unwrap();
        *self = new.into();

        self
    }

    // infallible inverse
    fn inverse(&self, ctx: &mut Self::Context) -> Self {
        self.inner.inverse(ctx).unwrap().into()
    }
    
    // constant creation
    fn constant(value: Self::Base, _ctx: &mut Self::Context) -> Self {
        GoldilocksFieldExt::constant_from_field(value).into()
    }
}