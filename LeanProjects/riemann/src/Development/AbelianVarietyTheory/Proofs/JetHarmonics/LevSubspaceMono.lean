import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CompactCasimirLeSubspaceMonotoneStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.WtNearLeOfAddDistLe

open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace

namespace GlobalTheory

theorem lev_subspace_mono :
    ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (n : ℕ) (ε : Fin n → Bool)
      (E : Fin n → Fin n → Module.End ℂ M) (μ : Fin n → ℝ), GlRel E → IsUnitary ε E →
      (∀ j, Lev ε E μ j 0) ∧ (∀ j x y, Lev ε E μ j x → Lev ε E μ j y → Lev ε E μ j (x + y)) ∧
      (∀ j (a : ℂ) x, Lev ε E μ j x → Lev ε E μ j (a • x)) ∧
      ∀ j j' x, j ≤ j' → Lev ε E μ j x → Lev ε E μ j' x := by
  intro M _ _ n ε E μ _ hU
  obtain ⟨h0, hadd, hsmul, hmono⟩ := GlobalTheory.T.compactCasimirLe_subspace_monotone M n ε E (isUnitary_kUnit ε E hU)
  refine ⟨fun j => ⟨h0 _, Submodule.zero_mem _⟩,
    fun j x y hx hy => ⟨hadd _ _ _ hx.1 hy.1, Submodule.add_mem _ hx.2 hy.2⟩,
    fun j a x hx => ⟨hsmul _ _ _ hx.1, Submodule.smul_mem _ _ hx.2⟩, ?_⟩
  intro j j' x hj hx
  have hj' : (j : ℝ) ≤ (j' : ℝ) := by exact_mod_cast hj
  refine ⟨hmono _ _ _ (by positivity) ?_ hx.1, ?_⟩
  · gcongr
  · exact wtNear_le_of_add_dist_le M n ε E _ _ _ _ (by simpa using hj') hx.2

end GlobalTheory
