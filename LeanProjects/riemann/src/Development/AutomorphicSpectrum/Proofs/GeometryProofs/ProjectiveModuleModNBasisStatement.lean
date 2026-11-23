import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ProjectiveModuleModNBasis
import Mathlib
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.projective_module_mod_N_basis : ∀ (E : Type) [Field E] [NumberField E] (M : Type) [AddCommGroup M] [Module (𝓞 E) M], Module.Finite (𝓞 E) M → Module.Projective (𝓞 E) M → ∀ (n N : ℕ), Module.finrank (𝓞 E) M = n → 0 < N → ∃ φ : (Fin n → 𝓞 E) →ₗ[𝓞 E] M, (∀ m, ∃ x b, m = φ x + N • b) ∧ ∀ x b, φ x = N • b → ∃ x', x = N • x' := by
  first | exact @GlobalTheory.CompanionTheory.ModFree.exists_free_map_mod | exact GlobalTheory.CompanionTheory.ModFree.exists_free_map_mod | (intros; apply GlobalTheory.CompanionTheory.ModFree.exists_free_map_mod <;> assumption)
