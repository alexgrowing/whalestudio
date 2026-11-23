import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentValuationBound
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentTraceSeparatingElement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RootsOfUnityAndPValuation
open NumberField
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.different_valuation_bound : ∀ (E : Type) [Field E] [NumberField E] [IsGalois ℚ E] (K : Type) [Field K] (w : AbsoluteValue K ℝ),
    IsNonarchimedean w → ∀ p : ℕ, p.Prime → w (p : K) < 1 → ∀ φ : E →+* K,
    (∀ k, w (φ ((integralBasis E).traceDual k)) ≤ w (p : K) ^ (-GlobalTheory.ShFam.Pad.vDiff E p)) ∧
      ∃ k, w (φ ((integralBasis E).traceDual k)) = w (p : K) ^ (-GlobalTheory.ShFam.Pad.vDiff E p) := by
  first | exact @GlobalTheory.AbsDifferent.abs_traceDual | exact GlobalTheory.AbsDifferent.abs_traceDual | (intros; apply GlobalTheory.AbsDifferent.abs_traceDual <;> assumption)
