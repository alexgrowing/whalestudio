import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEqOfIsAlgebraic

noncomputable section

open Formalism.L2.Host GlobalTheory.Published GlobalTheory.NT GlobalTheory.Mem.Fld GlobalTheory.Mem.HD NumberField IsDedekindDomain

namespace GlobalTheory.HilbertInClosure

theorem rayField_top_maximal_unramified : GlobalArtinReciprocity → ∀ (E : Type) [Field E] [NumberField E]
    [IsTotallyComplex E] (j : E →ₐ[ℚ] Qb) (ι : Qb →+* ℂ) (M : IntermediateField ℚ ℂ),
    IsRayFieldIn (ι.comp j.toRingHom) ⊤ M →
    ∃ _ : NumberField (qb ι M),
      (j.fieldRange ≤ qb ι M ∧
        (∀ σ : Qb ≃ₐ[ℚ] Qb, (∀ x ∈ j.fieldRange, σ x = x) → ∀ y ∈ qb ι M, σ y ∈ qb ι M) ∧
        ∀ σ τ : Qb ≃ₐ[ℚ] Qb, (∀ x ∈ j.fieldRange, σ x = x) → (∀ x ∈ j.fieldRange, τ x = x) →
          ∀ y ∈ qb ι M, σ (τ y) = τ (σ y)) ∧
      (discr (qb ι M)).natAbs = (discr E).natAbs ^ (Module.finrank ℚ (qb ι M) / Module.finrank ℚ E) ∧
      ∀ (L : Fld) [NumberField L],
        (j.fieldRange ≤ L ∧ (∀ σ : Qb ≃ₐ[ℚ] Qb, (∀ x ∈ j.fieldRange, σ x = x) → ∀ y ∈ L, σ y ∈ L) ∧
          ∀ σ τ : Qb ≃ₐ[ℚ] Qb, (∀ x ∈ j.fieldRange, σ x = x) → (∀ x ∈ j.fieldRange, τ x = x) →
            ∀ y ∈ L, σ (τ y) = τ (σ y)) →
        (discr L).natAbs = (discr E).natAbs ^ (Module.finrank ℚ L / Module.finrank ℚ E) → L ≤ qb ι M := by
  intro H E _ _ _ j ι M hM
  obtain ⟨hN, h, hst, hc, hd, hmax⟩ := hilbert_qb_aut H E j ι M hM
  have hm : ∀ σ : Qb ≃ₐ[ℚ] Qb, σ ∈ GalOf j.fieldRange ↔ ∀ x ∈ j.fieldRange, σ x = x := fun σ =>
    IntermediateField.mem_fixingSubgroup_iff _ _
  exact ⟨hN, ⟨h, fun σ hσ => hst σ ((hm σ).2 hσ), fun σ τ hσ hτ => hc σ ((hm σ).2 hσ) τ ((hm τ).2 hτ)⟩, hd,
    fun L _ hL => hmax L hL.1 fun σ hσ τ hτ => hL.2.2 σ τ ((hm σ).1 hσ) ((hm τ).1 hτ)⟩

end GlobalTheory.HilbertInClosure

end
