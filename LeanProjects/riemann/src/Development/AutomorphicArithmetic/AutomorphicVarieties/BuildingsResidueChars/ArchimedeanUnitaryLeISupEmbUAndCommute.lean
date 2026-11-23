import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsContinuousRetractionOntoUnitaryArchimedean
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeightEqOfFinitePartNeBot
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.BasicNotions
open scoped TensorProduct

section
open GlobalTheory.DefU Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

private theorem infinite_unitary_generated_by_embeddings (s : Finset (InfinitePlace E)) :
    ∀ g ∈ infU E n, (∀ w, w ∉ s → evGL w (cInf g) = 1) → g ∈ ⨆ τ : E →+* ℂ, embU n τ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro g hg h
    have h2 : GeneralLinearGroup.map (pFin E) g.1 = 1 := hg
    have h1 : cInf g = 1 := gl_ext_evGL fun w => by
      rw [h w (Finset.notMem_empty w), map_one]
    have : g = 1 := by
      refine Subtype.ext (ga_ext ?_ ?_)
      · change cInf g = cInf 1
        rw [h1, map_one]
      · rw [h2]
        exact (map_one _).symm
    rw [this]
    exact one_mem _
  | insert v s hv ih =>
    intro g hg h
    have hr : (embRet v.embedding g : UA E n) ∈ embU n v.embedding := (embRet v.embedding g).2
    have hr' : (embRet v.embedding g : UA E n) ∈ ⨆ τ : E →+* ℂ, embU n τ :=
      (le_iSup (fun τ : E →+* ℂ => embU n τ) v.embedding) hr
    have hk : (embRet v.embedding g : UA E n)⁻¹ * g ∈ ⨆ τ : E →+* ℂ, embU n τ := by
      refine ih _ (mul_mem (inv_mem (embU_le_infU _ hr)) hg) fun w hw => ?_
      rw [map_mul, map_inv, cInf_embRet, map_mul, map_inv, InfinitePlace.mk_embedding]
      by_cases e : w = v
      · subst e
        rw [evGL_cutGL_self, inv_mul_cancel]
      · rw [evGL_cutGL_of_ne e, h w (by simp [e, hw]), inv_one, one_mul]
    simpa using mul_mem hr' hk

end

open GlobalTheory.DefU Matrix in
theorem UpperTheory.archimedeanUnitary_le_iSup_embU_and_commute :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), infU E n ≤ (⨆ τ : E →+* ℂ, embU n τ) ∧ ∀ τ τ' : E →+* ℂ, InfinitePlace.mk τ ≠ InfinitePlace.mk τ' → ∀ a ∈ embU (E := E) n τ, ∀ b ∈ embU n τ', a * b = b * a := by
  intro E _ _ _ n
  refine ⟨fun g hg => infinite_unitary_generated_by_embeddings Finset.univ g hg fun w hw => (hw (Finset.mem_univ w)).elim, ?_⟩
  intro τ τ' hne a ha b hb
  have h2 : GeneralLinearGroup.map (pFin E) b.1 = 1 := hb.1
  refine Subtype.ext (ga_ext ?_ ?_)
  · change cInf (a * b) = cInf (b * a)
    rw [map_mul, map_mul]
    refine gl_ext_evGL fun w => ?_
    rw [map_mul, map_mul]
    by_cases h : w = InfinitePlace.mk τ'
    · rw [evGL_cInf_of_mem ha (h ▸ hne.symm), one_mul, mul_one]
    · rw [evGL_cInf_of_mem hb h, one_mul, mul_one]
  · simp only [Subgroup.coe_mul, map_mul, h2, one_mul, mul_one]
