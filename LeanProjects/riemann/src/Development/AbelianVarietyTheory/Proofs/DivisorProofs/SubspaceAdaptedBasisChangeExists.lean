import Mathlib

open Module

namespace GlobalTheory

theorem exists_invertible_matrix_rows_span : ∀ (F : Type) [Field F] (κ : Type) [Fintype κ] [DecidableEq κ] (Y₀ : Submodule F (κ → F)),
    ∃ P : Matrix κ κ F, IsUnit P.det ∧ ∃ s : Set κ, (∀ i ∈ s, P i ∈ Y₀) ∧
      ∀ y ∈ Y₀, ∃ c : κ → F, (∀ i ∉ s, c i = 0) ∧ y = Matrix.vecMul c P := by
  intro F _ κ _ _ Y₀
  obtain ⟨S, hSY, hspan, hli⟩ := exists_linearIndependent F (Y₀ : Set (κ → F))
  have hli' : LinearIndepOn F id S := hli
  let B := Basis.extend hli'
  let e := B.indexEquiv (Pi.basisFun F κ)
  let v : κ → (κ → F) := fun i => ((e.symm i : _) : κ → F)
  have hv : ∀ i, v i = B.reindex e i := by
    intro i; simp [v, B, Basis.reindex_apply, Basis.coe_extend]
  refine ⟨Matrix.of v, ?_, {i | v i ∈ S}, ?_, ?_⟩
  · apply (Matrix.isUnit_iff_isUnit_det _).mp
    apply Matrix.linearIndependent_rows_iff_isUnit.mp
    have : v = ⇑(B.reindex e) := funext hv
    have h2 : LinearIndependent F v := by
      rw [this]; exact (B.reindex e).linearIndependent
    exact h2
  · intro i hi; exact hSY hi
  · intro y hy
    have himg : v '' {i | v i ∈ S} = S := by
      ext x; simp only [Set.mem_image, Set.mem_setOf_eq]
      constructor
      · rintro ⟨i, hi, rfl⟩; exact hi
      · intro hx
        refine ⟨e ⟨x, hli'.subset_extend (Set.subset_univ _) hx⟩, ?_, ?_⟩ <;> simp [v, hx]
    have hy' : y ∈ Submodule.span F (v '' {i | v i ∈ S}) := by
      rw [himg, hspan, Submodule.span_eq]; exact hy
    obtain ⟨l, hl, rfl⟩ := (Finsupp.mem_span_image_iff_linearCombination F).mp hy'
    refine ⟨l, fun i hi => ?_, ?_⟩
    · by_contra h
      exact hi ((Finsupp.mem_supported _ _).mp hl (Finsupp.mem_support_iff.mpr h))
    · rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (by simp)]
      ext j
      simp [Matrix.vecMul, dotProduct, Finset.sum_apply]

end GlobalTheory
