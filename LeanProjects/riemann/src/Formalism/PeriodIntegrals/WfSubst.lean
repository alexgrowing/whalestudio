import Formalism.PeriodIntegrals.ExpIntW

namespace PI

def SubstSub : Prop :=
  ∀ (A : Type) [CommRing A] (S : Subring A) (σ : Type) (f : PowerSeries A) (a : MvPowerSeries σ A),
    (∀ n, PowerSeries.coeff n f ∈ S) → (∀ n, MvPowerSeries.coeff n a ∈ S) →
    MvPowerSeries.constantCoeff a = 0 → ∀ n, MvPowerSeries.coeff n (PowerSeries.subst a f) ∈ S

def WfSubst : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (σ : Type) (f : PowerSeries ℂ_[p]) (a : MvPowerSeries σ ℂ_[p]),
    CoefWf f → CoefWf a → MvPowerSeries.constantCoeff a = 0 → CoefWf (PowerSeries.subst a f)

end PI
