import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GramRootDeterminantErase
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.InverseChamberMap
open GlobalTheory.Chamber
open scoped InnerProductSpace ContDiff Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gram_root_determinant_erase : ∀ {k : ℕ} {T : Finset (SV k)} {u : SV k} (s : Finset (SV k)), IsPar T → u ∈ T → s ⊆ T.erase u →
  ∀ x : A0 k, ⟪x, rt T u⟫_ℝ = 0 →
  √(Matrix.gram ℝ fun v : ↥(insert u s) => rt T v).det * ∏ v ∈ s, (⟪x, rt T v⟫_ℝ)⁻¹ =
    ‖rt T u‖ * √(Matrix.gram ℝ fun v : ↥s => rt (T.erase u) v).det * ∏ v ∈ s, (⟪x, rt (T.erase u) v⟫_ℝ)⁻¹ := by
  first | exact @GlobalTheory.Chamber.rt_residue_identity | exact GlobalTheory.Chamber.rt_residue_identity | (intros; apply GlobalTheory.Chamber.rt_residue_identity <;> assumption)
