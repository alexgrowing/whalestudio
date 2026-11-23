import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsLiftModel
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

def LiftBirationalAmple.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]
    (Ω : Type) [Field Ω] [CharZero Ω] (y : (Σ k, ι k) → Ω) (D : ℕ) (N : K → ℤ) (c : ℕ),
    IsArithVar (mCoordIdeal y) (D + 1) → Birational y → 1 ≤ c →
    KH.AmpleV ℚ (KH.genIdeal y) (c • N - fun _ => 1) →
    ∃ q t₀ : ℕ, 1 ≤ q ∧ ∀ t : ℕ, t₀ ≤ t →
      ∃ (r : ℕ) (x' : Fin r → Ω), (∀ j, x' j ∈ chartLat y ((t * q) • N) 1) ∧
        Birational (fun p : Σ _ : Unit, Fin r => x' p.2)

end GroundTheory.Heights₂.Heights.HilbertSamuel
