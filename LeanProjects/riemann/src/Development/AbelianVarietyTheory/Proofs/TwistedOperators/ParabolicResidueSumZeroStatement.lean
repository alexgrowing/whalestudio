import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParabolicResidueSumZero
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.InverseChamberMap
open GlobalTheory.Chamber
open scoped InnerProductSpace ContDiff Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parabolic_residue_sum_zero : ∀ {k : ℕ} (𝔞 : Submodule ℝ (A0 k)) (c : Finset (SV k) → A0 k → ℂ), IsGMFam 𝔞 c → ∀ Q ∈ parF 𝔞 ∅,
  ∀ b : A0 k, b ≠ 0 → ∀ x : A0 k, ⟪x, b⟫_ℝ = 0 →
  ∑ P ∈ parP 𝔞 Q, ∑ u ∈ (P \ Q).filter (fun u => ∃ r : ℝ, rt P u = r • b),
    ((√(Matrix.gram ℝ fun v : ↥(P \ Q) => rt P v).det : ℝ) : ℂ) * (∏ _v ∈ P \ Q, Complex.I)⁻¹ * c P x *
      ((⟪rt P u, b⟫_ℝ : ℂ)⁻¹ * ∏ v ∈ (P \ Q).erase u, (⟪x, rt P v⟫_ℝ : ℂ)⁻¹) = 0 := by
  first | exact @GlobalTheory.Chamber.ResM.residues_cancel | exact GlobalTheory.Chamber.ResM.residues_cancel | (intros; apply GlobalTheory.Chamber.ResM.residues_cancel <;> assumption)
