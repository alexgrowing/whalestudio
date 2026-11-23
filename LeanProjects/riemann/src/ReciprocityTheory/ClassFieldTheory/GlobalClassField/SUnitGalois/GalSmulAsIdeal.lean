import Mathlib

noncomputable section

open NumberField IsDedekindDomain

namespace ReciprocityTheory.DiscreteGroups.GlobalClassField.SUnit

abbrev sUnits (K : Type*) [Field K] [NumberField K] (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Subgroup Kˣ :=
  (S : Set (HeightOneSpectrum (𝓞 K))).unit K

def unitsToSUnits (K : Type*) [Field K] [NumberField K] (S : Finset (HeightOneSpectrum (𝓞 K))) :
    (𝓞 K)ˣ →* sUnits K S :=
  (Units.map (algebraMap (𝓞 K) K : 𝓞 K →* K)).codRestrict (sUnits K S) fun x v _ => by
    rw [← HeightOneSpectrum.valuationOfNeZero_eq, HeightOneSpectrum.valuation_of_unit_eq]
    rfl

def valS (K : Type*) [Field K] [NumberField K] (S : Finset (HeightOneSpectrum (𝓞 K))) :
    sUnits K S →* (S → Multiplicative ℤ) :=
  MonoidHom.pi fun v => (HeightOneSpectrum.valuationOfNeZero (K := K) v.1).comp (sUnits K S).subtype

open scoped Pointwise in

instance galSmul (K L : Type*) [Field K] [Field L] [NumberField L] [Algebra K L] :
    MulAction (L ≃ₐ[K] L) (HeightOneSpectrum (𝓞 L)) where
  smul σ v :=
    { asIdeal := σ • v.asIdeal
      isPrime := Ideal.IsPrime.smul σ
      ne_bot := by
        rw [Ideal.pointwise_smul_def, ne_eq,
          Ideal.map_eq_bot_iff_of_injective (MulAction.injective σ)]
        exact v.ne_bot }
  one_smul v := HeightOneSpectrum.ext (one_smul _ v.asIdeal)
  mul_smul σ τ v := HeightOneSpectrum.ext (mul_smul σ τ v.asIdeal)

def galUnits {K L : Type*} [Field K] [Field L] [Algebra K L] (σ : L ≃ₐ[K] L) : Lˣ →* Lˣ :=
  Units.map σ.toRingEquiv.toMonoidHom
