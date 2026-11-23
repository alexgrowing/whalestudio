import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasNormGroups
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChevalleyUnits
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpanBasisImageAdicCompletionEqTop
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory

theorem normGroup_adjoin_eq_norm_range_completion : ∀ (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K] (w : HeightOneSpectrum (𝓞 E)) (W : HeightOneSpectrum (𝓞 K)) (j : K → Kbar w) (f : w.adicCompletion E →+* W.adicCompletion K) (b : Kbar w ≃+* Kbar W), Continuous f → (∀ x, b (algebraMap _ _ x) = algebraMap _ _ (f x)) → (∀ x : K, b (j x) = algebraMap (W.adicCompletion K) _ (algebraMap K (W.adicCompletion K) x)) → (∀ x : E, f (algebraMap E _ x) = algebraMap K _ (algebraMap E K x)) → letI := f.toAlgebra; Neutral.B1.normGroup (w.adicCompletion E) (IntermediateField.adjoin (w.adicCompletion E) (Set.range j)) = (Units.map (Algebra.norm (w.adicCompletion E) : W.adicCompletion K →* w.adicCompletion E)).range := by
  intro E K _ _ _ _ _ w W j f b hfc hb hj hf
  letI := f.toAlgebra

  let c : W.adicCompletion K →ₐ[w.adicCompletion E] Kbar w :=
    { toRingHom := b.symm.toRingHom.comp (algebraMap (W.adicCompletion K) (Kbar W))
      commutes' := fun x => by
        change b.symm (algebraMap _ _ (f x)) = _
        rw [← hb x]; exact b.symm_apply_apply _ }
  have hcj : ∀ x : K, c (algebraMap K (W.adicCompletion K) x) = j x := by
    intro x
    change b.symm (algebraMap _ _ _) = _
    rw [← hj x]; exact b.symm_apply_apply _
  have hrange : c.fieldRange = IntermediateField.adjoin (w.adicCompletion E) (Set.range j) := by
    apply le_antisymm
    · rintro _ ⟨y, rfl⟩
      have hspan := span_basis_image_adicCompletion_eq_top E K w W f hfc hf _ (Module.finBasis E K)
      have hy : y ∈ Submodule.span (w.adicCompletion E)
          (Set.range fun i => algebraMap K (W.adicCompletion K) (Module.finBasis E K i)) := by
        rw [hspan]; trivial
      induction hy using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨i, rfl⟩ := hx
        change c _ ∈ _
        rw [hcj]
        exact IntermediateField.subset_adjoin _ _ ⟨_, rfl⟩
      | zero => simp
      | add x y _ _ hx hy =>
        simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_add] at hx hy ⊢
        exact add_mem hx hy
      | smul a x _ hx =>
        simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_smul] at hx ⊢
        exact IntermediateField.smul_mem _ hx
    · rw [IntermediateField.adjoin_le_iff]
      rintro _ ⟨x, rfl⟩
      exact ⟨algebraMap K _ x, hcj x⟩
  let e : W.adicCompletion K ≃ₐ[w.adicCompletion E]
      IntermediateField.adjoin (w.adicCompletion E) (Set.range j) :=
    (AlgEquiv.ofInjectiveField c).trans (IntermediateField.equivOfEq hrange)
  ext u
  simp only [Neutral.B1.normGroup, MonoidHom.mem_range]
  constructor
  · rintro ⟨v, rfl⟩
    refine ⟨Units.map e.symm.toRingEquiv.toMonoidHom v, ?_⟩
    ext
    simp [Algebra.norm_eq_of_algEquiv]
  · rintro ⟨v, rfl⟩
    refine ⟨Units.map e.toRingEquiv.toMonoidHom v, ?_⟩
    ext
    simp [Algebra.norm_eq_of_algEquiv]

end GlobalTheory
