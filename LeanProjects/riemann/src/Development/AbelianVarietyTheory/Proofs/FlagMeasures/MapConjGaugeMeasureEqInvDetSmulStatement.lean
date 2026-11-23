import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MapConjGaugeMeasureEqInvDetSmul
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsGaugeAll
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.map_conj_gaugeMeasure_eq_inv_det_smul : ∀ (n : ℕ) (ε : Fin n → Bool) (A : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) (d : ℕ) (E : Fin d → Matrix (Fin n) (Fin n) ℂ) (S : Subgroup (Formalism.REAL.UJ ε)), (∀ X ∈ A, ∀ Y ∈ A, X * Y ∈ A) → (∀ i k, ((E i * (E k)ᴴ).trace).re = if i = k then 1 else 0) → (∀ X, (X ∈ A ∧ Formalism.REAL.inG ε X) ↔ X ∈ Submodule.span ℝ (Set.range E)) → (∀ g, g ∈ S ↔ uMat g - 1 ∈ A) → IsClosed (S : Set (Formalism.REAL.UJ ε)) → ∀ μ : Measure (Formalism.REAL.UJ ε), IsGaugeSub (S : Set (Formalism.REAL.UJ ε)) d μ → ∀ (m : Formalism.REAL.UJ ε) (L : Matrix (Fin d) (Fin d) ℝ), (∀ g, g ∈ S ↔ m * g * m⁻¹ ∈ S) → (∀ k, uMat m * E k * uMat m⁻¹ = ∑ i, L i k • E i) → L.det ≠ 0 → μ.map (fun u => m * u * m⁻¹) = ENNReal.ofReal |L.det|⁻¹ • μ := by
  first | exact @GlobalTheory.GaugeConjScale.map_conj_eq_inv_det_smul | exact GlobalTheory.GaugeConjScale.map_conj_eq_inv_det_smul | (intros; apply GlobalTheory.GaugeConjScale.map_conj_eq_inv_det_smul <;> assumption)
