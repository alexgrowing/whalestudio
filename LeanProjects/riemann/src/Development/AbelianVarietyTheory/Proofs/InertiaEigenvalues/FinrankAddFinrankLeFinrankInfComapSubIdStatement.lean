import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankAddFinrankLeFinrankInfComapSubId
import Mathlib
open TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_add_finrank_le_finrank_inf_comap_sub_id' : ∀ (k : Type) [Field k] (M W : Type) [AddCommGroup M] [Module k M] [AddCommGroup W] [Module k W] (D R : Submodule k M) [FiniteDimensional k ↥D] (F : M →ₗ[k] M) (B : M →ₗ[k] W →ₗ[k] k), R ≤ D → (∀ x ∈ D, F x ∈ D) → (∀ x ∈ R, ∀ w, B x w = 0) → (∀ x ∈ D, ∀ w, B (F x) w = B x w) → (∀ w, (∀ x ∈ D, B x w = 0) → w = 0) → finrank k W + finrank k ↥R ≤ finrank k ↥(D ⊓ R.comap (F - LinearMap.id)) := by
  first | exact @GlobalTheory.finrank_add_finrank_le_finrank_inf_comap_sub_id | exact GlobalTheory.finrank_add_finrank_le_finrank_inf_comap_sub_id | (intros; apply GlobalTheory.finrank_add_finrank_le_finrank_inf_comap_sub_id <;> assumption)
