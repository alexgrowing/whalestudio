import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CapelliKFiniteCoefficient
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.capelli_k_finite_coefficient : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [CompleteSpace Wq] [FiniteDimensional ℂ Wq] (l : R.H → Wp) (l' : R.H → Wq), R.IsDS ε mu → (∀ f : Mx k r → (Wq →L[ℂ] Wp), PI.CapelliEig.IsKFinCoefT (k := k) (r := r) R.σ f → ∃ s, IsCoef R l l' f s) ∧ (∀ F s (t : ℂ), IsCoef R l l' F s → IsCoef R l l' (fun g => t • F g) (t * s)) ∧ ((∃ x ∈ R.TK, l x ≠ 0) → (∃ y ∈ R.TK, l' y ≠ 0) → ∀ s : ℂ, ∃ F, IsCoef R l l' F s) := by
  first | exact @GlobalTheory.isCoef_of_translate_smul_exists | exact GlobalTheory.isCoef_of_translate_smul_exists | (intros; apply GlobalTheory.isCoef_of_translate_smul_exists <;> assumption)
