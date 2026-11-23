import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.MainNotions

namespace GlobalTheory.CompanionTheory.Ar.HS

open NumberField

def PropHS : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [StarRing F] [IsTotallyComplex F] (D N n δ T : ℕ)
    (X : ChowData F D N n δ) (Z : HSData X T) (J C : ℝ), 2 ≤ D → D + 1 ≤ T → 26 ≤ C → Z.ResBound J →
    Claim C T D n 1 X.Λ Z.β Z.ΛD Z.ΛT J δ X.h (Z.d T) Z.degMT

def RankBound : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyComplex F] (D N n δ T : ℕ)
    (X : ChowData F D N n δ) (Z : HSData X T) (J : ℝ), 2 ≤ D → D + 1 ≤ T → Z.ResBound J →
    (T - 1).choose D * δ ≤ Z.d T

end GlobalTheory.CompanionTheory.Ar.HS
