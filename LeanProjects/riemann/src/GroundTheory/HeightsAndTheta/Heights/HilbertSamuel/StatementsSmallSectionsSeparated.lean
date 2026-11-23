import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSmallPacking
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

noncomputable section

def SmallSectionsSeparated.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (A : HermLine ι),
    IsArithVar (mCoordIdeal y) (D + 1) → Birational y → IsSmoothHerm A →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ τ : ℕ, ∃ (Z : Finset ((Σ k, ι k) → ℂ)) (ev : chartLatNm y A.a τ →+ (Z → ℂ)),
      (∀ z ∈ Z, z ∈ mcPts (mCoordIdeal y)) ∧
      (∀ (s : chartLatNm y A.a τ) (z : Z), ∃ (dg dh : K → ℕ) (g h : MRing ι),
        IsMultiHomog g dg ∧ IsMultiHomog h dh ∧ (∀ k, (dg k : ℤ) = dh k + τ * A.a k) ∧
        aeval y g = (s : Ω) * aeval y h ∧ eval (z : (Σ k, ι k) → ℂ) (map (Int.castRingHom ℂ) h) ≠ 0 ∧
        ev s z * eval (z : (Σ k, ι k) → ℂ) (map (Int.castRingHom ℂ) h) =
          eval (z : (Σ k, ι k) → ℂ) (map (Int.castRingHom ℂ) g)) ∧
      ∀ s t : chartLatNm y A.a τ, IsSmallH (mCoordIdeal y) y A τ (s : Ω) →
        IsSmallH (mCoordIdeal y) y A τ (t : Ω) → s ≠ t →
        ∃ z : Z, Real.exp (-(C * ((τ : ℝ) + 1))) * A.h z ^ τ ≤ ‖ev s z - ev t z‖

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
