import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

noncomputable section

def ProjAvoidingForm.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (df : K → ℕ) (f : MRing ι),
    IsArithVar (mCoordIdeal y) (D + 1) → IsMultiHomog f df → f ∉ mCoordIdeal y →
    ∃ (e : K → ℕ) (L : Fin (D + 1) → MRing ι) (G : MvPolynomial (Fin (D + 1)) ℤ),
      (∀ k, 1 ≤ e k) ∧ (∀ j, IsMultiHomog (L j) e) ∧
      (∀ z ∈ mcPts (mCoordIdeal y), ∃ j, eval z (map (Int.castRingHom ℂ) (L j)) ≠ 0) ∧ G ≠ 0 ∧
      ∀ ζ : Fin (D + 1) → ℂ, eval ζ (map (Int.castRingHom ℂ) G) ≠ 0 →
        ∀ z ∈ mcPts (mCoordIdeal y),
          (∃ t : ℂ, ∀ j, eval z (map (Int.castRingHom ℂ) (L j)) = t * ζ j) →
          eval z (map (Int.castRingHom ℂ) f) ≠ 0

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
