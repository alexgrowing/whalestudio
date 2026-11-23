import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsArithNakaiMoishezon
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory
open GroundTheory.Heights₂.Heights.HilbertSamuel

noncomputable section

section Objects

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

def IsGenBySmallSections (y : (Σ k, ι k) → Ω) (L : HermLine ι) : Prop :=
  ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∃ (q : ℕ) (w : Fin q → Ω),
    (∀ j, w j ∈ chartLat y (GroundTheory.Heights₂.Heights.Inter.hermZpow L n).a 1) ∧
    KH.GeneratesOn y (GroundTheory.Heights₂.Heights.Inter.hermZpow L n).a w ∧
    ∃ c : ℝ, c < 1 ∧
      ∀ j, IsBoundedH (mCoordIdeal y) y (GroundTheory.Heights₂.Heights.Inter.hermZpow L n) 1 c (w j)

end Objects

def ArithNMLift.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (L : HermLine ι) (P0 : Ideal (MRing ι)),
    IsArithVar (mCoordIdeal y) (D + 1) →
    P0 ≤ mCoordIdeal y → IsSemipositiveRel P0 (mCoordIdeal y) L → IsConjInvariantH L →
    IsAmpleOnModel y L.a →
    (∃ m : ℕ, 1 ≤ m ∧ ∃ s ∈ chartLat y (GroundTheory.Heights₂.Heights.Inter.hermZpow L m).a 1, s ≠ 0 ∧
      ∃ c : ℝ, c < 1 ∧ IsBoundedH (mCoordIdeal y) y (GroundTheory.Heights₂.Heights.Inter.hermZpow L m) 1 c s) →
    (∀ (W : Ideal (MRing ι)) (e : ℕ), IsArithVar W (e + 1) → mCoordIdeal y ≤ W → e < D →
      ∀ (Ω' : Type) [Field Ω'] (y' : (Σ k, ι k) → Ω'), mCoordIdeal y' = W → IsGenBySmallSections y' L) →
    IsGenBySmallSections y L

end

end GroundTheory.Heights₂.Heights.Targets
