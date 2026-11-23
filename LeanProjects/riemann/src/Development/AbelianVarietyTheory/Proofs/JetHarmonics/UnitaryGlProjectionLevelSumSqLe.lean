import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.UnitaryGlModuleProjDualTensorLevelAddTwoStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SumNormSqProjectionsTensorUnitaryGlLeStatement
open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace

namespace GlobalTheory

theorem lev_proj_and_sum_sq_le : ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (N : Fin n → Type) [∀ s, NormedAddCommGroup (N s)] [∀ s, InnerProductSpace ℂ (N s)] (F : ∀ s, Fin n → Fin n → Module.End ℂ (N s)) (io : ∀ s, N s →ₗ[ℂ] (Fin n → M)) (pr : ∀ s, (Fin n → M) →ₗ[ℂ] N s) (μ : Fin n → ℝ) (kk j : ℕ) (bv : ℝ) (w : M), IsMod ε E μ → (∀ s, IsMod ε (F s) (μ - Pi.single s 1)) → AlgTens ε E N F io pr → Shape ε kk μ bv → j ≤ 4 * n ^ 2 → Lev ε E μ j w → ∀ c, (∀ s, Lev ε (F s) (μ - Pi.single s 1) (j + 2) (pr s (Pi.single c w))) ∧ ∑ s, ‖pr s (Pi.single c w)‖ ^ 2 ≤ (6 * bv) ^ (2 * (n + 1 - kk)) * ‖w‖ ^ 2 := by
  intro M _ _ n ε E N _ _ F io pr μ kk j bv w h1 h2 h3 h4 h5 h6 c
  exact ⟨GlobalTheory.T.unitary_glModule_proj_dual_tensor_level_add_two M n ε E N F io pr μ kk j bv w h1 h2 h3 h4 h5 h6 c,
    GlobalTheory.T.sum_normSq_projections_tensor_unitary_gl_le M n ε E N F io pr μ kk j bv w h1 h2 h3 h4 h5 h6 c⟩

end GlobalTheory
