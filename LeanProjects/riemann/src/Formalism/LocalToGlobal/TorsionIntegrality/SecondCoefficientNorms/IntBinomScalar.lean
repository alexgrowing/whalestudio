import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.HasSecondLogDeriv

noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.C

def MvExpLaws : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (σ : Type),
    mvExp (0 : MvPowerSeries σ K) = 1 ∧
    (∀ f : MvPowerSeries σ K, MvPowerSeries.constantCoeff f = 0 →
      MvPowerSeries.constantCoeff (mvExp f) = 1) ∧
    (∀ f g : MvPowerSeries σ K, MvPowerSeries.constantCoeff f = 0 →
      MvPowerSeries.constantCoeff g = 0 → mvExp (f + g) = mvExp f * mvExp g) ∧
    (∀ f g : MvPowerSeries σ K, MvPowerSeries.constantCoeff f = 0 →
      MvPowerSeries.constantCoeff g = 0 → mvExp f = mvExp g → f = g)

def MvExpSubst : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (σ : Type) (f : PowerSeries K) (a : MvPowerSeries σ K),
    PowerSeries.constantCoeff f = 0 → MvPowerSeries.constantCoeff a = 0 →
      PowerSeries.subst a (mvExp f : PowerSeries K) = mvExp (PowerSeries.subst a f)

def LGSubgroup : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (R : Subring K) (σ : Type),
    LG R (0 : MvPowerSeries σ K) ∧
    (∀ f g : MvPowerSeries σ K, LG R f → LG R g → LG R (f + g)) ∧
    (∀ f : MvPowerSeries σ K, LG R f → LG R (-f))

def LGBinom : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (R : Subring K) (σ : Type) (z : K), IsBinomScalar R z →
    ∀ f : MvPowerSeries σ K, LG R f → LG R (z • f)

def LGHalf : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (R : Subring K) (σ : Type), (2 : K)⁻¹ ∈ R →
    ∀ f : MvPowerSeries σ K, LG R (f + f) → LG R f

def IntBinomScalar : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (R : Subring K) (n : ℤ), IsBinomScalar R (n : K)

def LGSubst : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (R : Subring K) (f : PowerSeries K), LG R f →
    ∀ (σ : Type) (a : MvPowerSeries σ K), IsPt R a → LG R (PowerSeries.subst a f)

def LGSubstMv : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (R : Subring K) (σ : Type) [Finite σ]
    (f : MvPowerSeries σ K), LG R f →
    ∀ (τ : Type) (a : σ → MvPowerSeries τ K), (∀ s, IsPt R (a s)) → LG R (MvPowerSeries.subst a f)

def IntSubst : Prop :=
  ∀ (K : Type) [Field K] (R : Subring K) (f : PowerSeries K), IntPS R f →
    ∀ (σ : Type) (a : MvPowerSeries σ K), IsPt R a → IntMv R (PowerSeries.subst a f)

def LGDeriv : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (R : Subring K) (σ : Type) (f : MvPowerSeries σ K),
    LG R f → ∀ i : σ, IntMv R (MvPowerSeries.pderiv K i f)

end Formalism.L2.Th1.C
