import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitOneAddOfSq
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemBand
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.ExistsNormRconvLeSiegel
import GroundTheory.AutomorphicForms.ReductionSiegel
open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.HCF Topology
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_signed_sum_integral_le : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (β : Lie E a → ℂ), ContDiff ℝ ∞ β →
    HasCompactSupport β → tsupport β ⊆ invSet E a → ∀ (m : ℕ) (R : ℝ), ∃ (c : ℝ) (Q : Set (Lie E a)),
    0 ≤ c ∧ IsCompact Q ∧ Q ⊆ invSet E a ∧ ∀ f : Lie E a → ℂ, ContinuousOn f (invSet E a) →
    ∀ F : ℝ, 0 ≤ F → (∀ w ∈ Q, ‖f w‖ ≤ F) →
    ∀ Y : Fin m → Matrix (Fin a) (Fin a) (Cinf E), (∀ i j, Y i * Y j = 0) → (∀ i, ‖toL (Y i)‖ ≤ R) →
    ‖∑ ε : Fin m → Bool, (GroundTheory.Automorphic.altSign ε : ℂ) *
        ∫ w, f (toL ((1 + GroundTheory.Automorphic.altPoint Y ε) * Matrix.of w)) * β w‖ ≤ c * F * ∏ i, ‖toL (Y i)‖ := by
  first | exact @GlobalTheory.AltConv.norm_sum_altSign_integral_le | exact GlobalTheory.AltConv.norm_sum_altSign_integral_le | (intros; apply GlobalTheory.AltConv.norm_sum_altSign_integral_le <;> assumption)
