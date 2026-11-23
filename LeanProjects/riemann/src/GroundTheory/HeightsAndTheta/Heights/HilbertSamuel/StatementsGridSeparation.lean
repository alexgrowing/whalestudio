import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

noncomputable section

def GridSeparation.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (A : HermLine ι),
    IsArithVar (mCoordIdeal y) (D + 1) → Birational y → IsSmoothHerm A →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ τ : ℕ, ∃ Z : Finset ((Σ k, ι k) → ℂ),
      (∀ z ∈ Z, z ∈ mcPts (mCoordIdeal y)) ∧
      (∀ s ∈ chartLatNm y A.a τ, ∀ z ∈ Z, ∃ (dg dh : K → ℕ) (g h : MRing ι),
        IsMultiHomog g dg ∧ IsMultiHomog h dh ∧ (∀ k, (dg k : ℤ) = dh k + τ * A.a k) ∧
        aeval y g = s * aeval y h ∧ eval z (map (Int.castRingHom ℂ) h) ≠ 0) ∧
      ∀ u ∈ chartLatNm y A.a τ, u ≠ 0 → ∃ z ∈ Z, ∃ (dg dh : K → ℕ) (g h : MRing ι),
        IsMultiHomog g dg ∧ IsMultiHomog h dh ∧ (∀ k, (dg k : ℤ) = dh k + τ * A.a k) ∧
        aeval y g = u * aeval y h ∧ eval z (map (Int.castRingHom ℂ) h) ≠ 0 ∧
        Real.exp (-(C * ((τ : ℝ) + 1))) * A.h z ^ τ * ‖eval z (map (Int.castRingHom ℂ) h)‖ ≤
          ‖eval z (map (Int.castRingHom ℂ) g)‖

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
