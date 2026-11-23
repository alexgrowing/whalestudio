import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantSubmoduleInImageSpan
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasLocType

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.invariant_submodule_in_image_span : ∀ (G U W : Type) [Group G] [AddCommGroup U] [Module ℂ U] [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ G U) (ρ : Representation ℂ G W), π.IsIrreducible →
    ∀ M : Submodule ℂ W, (∀ g, ∀ w ∈ M, ρ g w ∈ M) → ∀ w ∈ M, w ∈ GlobalTheory.LocTypeGood.imgSpan π ρ →
      w ∈ Submodule.span ℂ {y | ∃ T : U →ₗ[ℂ] W, (∀ g, T ∘ₗ π g = ρ g ∘ₗ T) ∧ (∀ u, T u ∈ M) ∧ ∃ u, y = T u} := by
  first | exact @GlobalTheory.mem_span_equivariant_into_of_mem_imgSpan | exact GlobalTheory.mem_span_equivariant_into_of_mem_imgSpan | (intros; apply GlobalTheory.mem_span_equivariant_into_of_mem_imgSpan <;> assumption)
