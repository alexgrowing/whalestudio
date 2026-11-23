import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.CntPartners

noncomputable section

namespace Formalism.MainNotions.BridgeLemma₂

open NumberField Module Formalism.BasicNotions Formalism.MainNotions.S.Lat

def IsCMFieldViaStar (E : Type) [Field E] [NumberField E] [StarRing E] : Prop :=
  (∀ (σ : E →+* ℂ) (a : E), σ (star a) = (starRingEnd ℂ) (σ a)) ∧ NumberField.IsTotallyComplex E

def IsPositiveDefiniteForm {E : Type} [Field E] [NumberField E] [StarRing E] (S : HSpace E) : Prop :=
  ∀ (σ : E →+* ℂ) (x : S.V), x ≠ 0 → 0 < (σ (S.hT x x)).re

def numInfinitePlaces (E : Type) [Field E] [NumberField E] : ℕ := Fintype.card (InfinitePlace E)

def ShortVectorCountBound : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (S : HSpace E), IsCMFieldViaStar E → IsPositiveDefiniteForm S →
    ∀ L : Submodule (𝓞 E) S.V, Formalism.HermitianLatticesTheory.IsIntegralLat S.hT L → ∀ c : ℝ, 1 ≤ c →
      {y : S.V | y ∈ L ∧ ∀ σ : E →+* ℂ, (σ (S.hT y y)).re ≤ c}.Finite ∧
      ({y : S.V | y ∈ L ∧ ∀ σ : E →+* ℂ, (σ (S.hT y y)).re ≤ c}.ncard : ℝ) ≤
        9 ^ (S.rank * numInfinitePlaces E) * (c ^ numInfinitePlaces E) ^ S.rank

def ShortVectorExists : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (S : HSpace E), IsCMFieldViaStar E → IsPositiveDefiniteForm S →
    ∀ M₀ : Submodule (𝓞 E) S.V, M₀.FG → finrank E (Submodule.span E (M₀ : Set S.V)) = 1 →
      ∃ y ∈ M₀, y ≠ 0 ∧ ∀ σ : E →+* ℂ,
        (σ (S.hT y y)).re ≤ (|(discr E : ℝ)| ^ ((1 : ℝ) / 2) * latDetH S.hT M₀) ^ ((1 : ℝ) / numInfinitePlaces E)

end Formalism.MainNotions.BridgeLemma₂

end
