import Mathlib
open CategoryTheory Limits AlgebraicGeometry

namespace GlobalTheory

theorem trdeg_le_of_closure_range_union_eq_top (K₀ K₁ K₂ L : Type) [Field K₀] [Field K₁] [Field K₂]
    [Field L] [Algebra K₀ K₁] [Algebra K₀ K₂] [Algebra K₁ L] (φ : K₂ →+* L)
    (hφ : φ.comp (algebraMap K₀ K₂) = (algebraMap K₁ L).comp (algebraMap K₀ K₁))
    (hcl : Subfield.closure (Set.range (algebraMap K₁ L) ∪ Set.range φ) = ⊤) :
    Algebra.trdeg K₁ L ≤ Algebra.trdeg K₀ K₂ := by
  obtain ⟨ι, x, hx⟩ := exists_isTranscendenceBasis' K₀ K₂
  rw [← hx.cardinalMk_eq_trdeg]
  let E := IntermediateField.adjoin K₁ (Set.range fun i => φ (x i))
  have hm : ∀ a ∈ Algebra.adjoin K₀ (Set.range x), φ a ∈ E := by
    intro a ha
    induction ha using Algebra.adjoin_induction with
    | mem a ha =>
      obtain ⟨i, rfl⟩ := ha
      exact IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩
    | algebraMap r =>
      have h : φ (algebraMap K₀ K₂ r) = algebraMap K₁ L (algebraMap K₀ K₁ r) :=
        RingHom.congr_fun hφ r
      rw [h]
      exact E.algebraMap_mem _
    | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
    | mul a b _ _ ha hb => rw [map_mul]; exact mul_mem ha hb
  have halg : ∀ f, IsAlgebraic E (φ f) := by
    intro f
    have hf : IsAlgebraic (Algebra.adjoin K₀ (Set.range x)) f := hx.isAlgebraic.isAlgebraic f
    let g : Algebra.adjoin K₀ (Set.range x) →+* E :=
      (φ.comp (Algebra.adjoin K₀ (Set.range x)).val.toRingHom).codRestrict E fun a => hm a a.2
    have hg : Function.Injective g := fun a b h =>
      Subtype.ext (φ.injective (congrArg Subtype.val h))
    exact hf.ringHom_of_comp_eq g φ hg rfl
  have hL : Algebra.IsAlgebraic E L := by
    refine ⟨fun z => ?_⟩
    have hle : Subfield.closure (Set.range (algebraMap K₁ L) ∪ Set.range φ) ≤
        (algebraicClosure E L).toSubfield := by
      refine Subfield.closure_le.2 ?_
      rintro _ (⟨k, rfl⟩ | ⟨f, rfl⟩)
      · exact (algebraicClosure E L).algebraMap_mem (algebraMap K₁ E k)
      · exact mem_algebraicClosure_iff.2 (halg f)
    rw [hcl] at hle
    exact mem_algebraicClosure_iff.1 (hle (Subfield.mem_top z))
  have hE : Algebra.trdeg K₁ E ≤ Cardinal.mk ι := by
    have : Algebra.IsAlgebraic (Algebra.adjoin K₁ (Set.range fun i => (⟨φ (x i),
        IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩⟩ : E))) E := by
      rw [← IntermediateField.isAlgebraic_adjoin_iff_top]
      have htop : IntermediateField.adjoin K₁ (Set.range fun i => (⟨φ (x i),
        IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩⟩ : E)) = ⊤ := by
        apply IntermediateField.lift_injective
        rw [IntermediateField.lift_adjoin, IntermediateField.lift_top, ← Set.range_comp]
        rfl
      rw [htop]
      infer_instance
    exact (Algebra.IsAlgebraic.trdeg_le_cardinalMk K₁ _ (alg := this)).trans Cardinal.mk_range_le
  haveI : FaithfulSMul E L :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (algebraMap E L).injective
  calc Algebra.trdeg K₁ L = Algebra.trdeg K₁ E := by
        rw [← trdeg_add_eq K₁ E (A := L), trdeg_eq_zero (R := E) (A := L), add_zero]
    _ ≤ _ := hE

end GlobalTheory
