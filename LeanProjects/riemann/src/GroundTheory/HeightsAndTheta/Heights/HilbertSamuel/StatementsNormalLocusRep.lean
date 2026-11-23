import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

noncomputable section

def NormalLocusRep.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ),
    IsArithVar (mCoordIdeal y) (D + 1) → Birational y →
    ∃ (df : K → ℕ) (f : MRing ι), IsMultiHomog f df ∧ f ∉ mCoordIdeal y ∧
      ∀ (a : K → ℤ) (τ : ℕ), ∀ s ∈ chartLatNm y a τ, ∀ z ∈ mcPts (mCoordIdeal y),
        eval z (map (Int.castRingHom ℂ) f) ≠ 0 →
        ∃ (dg dh : K → ℕ) (g h : MRing ι), IsMultiHomog g dg ∧ IsMultiHomog h dh ∧
          (∀ k, (dg k : ℤ) = dh k + τ * a k) ∧ aeval y g = s * aeval y h ∧
          eval z (map (Int.castRingHom ℂ) h) ≠ 0

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
