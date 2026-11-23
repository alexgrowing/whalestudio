import Mathlib
import Development.EtaleCohomology.EtaleSheaves.CurveThroughGenericPointSpreadsToSmoothProperFamily2
import Development.AutomorphicArithmetic.CommutativeAlgebra.TopologicalKrullDimLeOfIsOpenImmersionIntegral
import Development.AutomorphicArithmetic.CommutativeAlgebra.IsFiniteFromNormalizationOfPerfectField
import Development.AutomorphicArithmetic.CommutativeAlgebra.MemRangeOfProperGenericFibreSeparated

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafGeoVCut

namespace UpperTheory.Cb.ZariskiExtensionByZero

private theorem stage (k : Type) [Field k] [PerfectField k] {T D : Scheme.{0}} (t : T ⟶ Sp k)
    [LocallyOfFiniteType t] (f : D ⟶ T) [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
    [LocallyQuasiFinite f] [IsIntegral D] :
    ∃ (Y : Scheme.{0}) (g : Y ⟶ T) (j : D ⟶ Y), IsFinite g ∧ IsOpenImmersion j ∧ j ≫ g = f ∧
      IsIntegral Y ∧ Dense (Set.range j) :=
  ⟨f.normalization, f.fromNormalization, f.toNormalization, UpperTheory.isFinite_fromNormalization_of_perfectField k t f, inferInstance,
    f.toNormalization_fromNormalization, inferInstance,
    (inferInstance : IsDominant f.toNormalization).denseRange⟩

private theorem pull_of {B D Y C S T : Scheme.{0}} (j : D ⟶ Y) [IsOpenImmersion j] (π : Y ⟶ B)
    (ι : S ⟶ B) [Mono ι] (q : D ⟶ S) (w : j ≫ π = q ≫ ι) (v : C ⟶ D) (c : C ⟶ T) (s : T ⟶ S)
    (hP : IsPullback v c q s) (h : ∀ y, π y ∈ Set.range (s ≫ ι) → y ∈ Set.range j) :
    IsPullback (v ≫ j) c π (s ≫ ι) := by
  have hw : (v ≫ j) ≫ π = c ≫ s ≫ ι := by
    rw [Category.assoc, w, ← Category.assoc, hP.w, Category.assoc]
  have hr : ∀ z : PullbackCone π (s ≫ ι), Set.range z.fst ⊆ Set.range j := by
    rintro z _ ⟨x, rfl⟩
    refine h _ ⟨z.snd x, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, z.condition]
  have hl : ∀ z : PullbackCone π (s ≫ ι),
      IsOpenImmersion.lift j z.fst (hr z) ≫ q = z.snd ≫ s := by
    intro z
    rw [← cancel_mono ι, Category.assoc, ← w, IsOpenImmersion.lift_fac_assoc, z.condition,
      Category.assoc]
  refine ⟨⟨hw⟩, ⟨PullbackCone.IsLimit.mk _ (fun z => hP.lift (IsOpenImmersion.lift j z.fst (hr z)) z.snd (hl z))
    (fun z => ?_) (fun z => ?_) (fun z m h1 h2 => ?_)⟩⟩
  · rw [IsPullback.lift_fst_assoc, IsOpenImmersion.lift_fac]
  · rw [IsPullback.lift_snd]
  · refine hP.hom_ext ?_ ?_
    · rw [IsPullback.lift_fst, ← cancel_mono j, IsOpenImmersion.lift_fac, Category.assoc]
      exact h1
    · rw [IsPullback.lift_snd]; exact h2

private theorem smooth_of {B D Y S : Scheme.{0}} (j : D ⟶ Y) [IsOpenImmersion j] (π : Y ⟶ B)
    (ι : S ⟶ B) [IsOpenImmersion ι] (q : D ⟶ S) [Smooth q] (w : j ≫ π = q ≫ ι) (V : B.Opens)
    (h : ∀ y, π y ∈ V → y ∈ Set.range j) : Smooth (π ∣_ V) := by
  have hr : Set.range (π ⁻¹ᵁ V).ι ⊆ Set.range j := by
    rw [Scheme.Opens.range_ι]
    intro y hy
    exact h y hy
  have e : (π ⁻¹ᵁ V).ι ≫ π = IsOpenImmersion.lift j _ hr ≫ q ≫ ι := by
    rw [← w, ← Category.assoc, IsOpenImmersion.lift_fac]
  have hs : Smooth ((π ∣_ V) ≫ V.ι) := by
    rw [morphismRestrict_ι, e]
    infer_instance
  haveI hloc : IsZariskiLocalAtTarget @Smooth.{0} :=
    HasRingHomProperty.instIsZariskiLocalAtTarget _
  haveI : MorphismProperty.RespectsIso @Smooth.{0} :=
    MorphismProperty.respectsIso_of_isStableUnderComposition
      (fun _ _ f (_ : IsIso f) => inferInstance)
  haveI : MorphismProperty.HasOfPostcompProperty @Smooth.{0} @IsOpenImmersion.{0} :=
    hasOfPostcompProperty_isOpenImmersion_of_morphismRestrict _
      (fun f U hf => IsZariskiLocalAtTarget.restrict hf U)
  exact MorphismProperty.of_postcomp (W := @Smooth.{0}) (W' := @IsOpenImmersion.{0}) _ V.ι
    inferInstance hs

end UpperTheory.Cb.ZariskiExtensionByZero

open UpperTheory.Cb.ZariskiExtensionByZero in
theorem UpperTheory.Cb.extension_by_zero_of_zariski_quasi_finite_factorization :
    LateralTheory.E.LeafGeoVV2Cut.LeafExtendZMT := by
  intro k _ _ X p _ Ω _ _ R B b _ ι _ hιb C0 C1 C2 c0 γ1 γ2 e hc0 hc1 hc2 he D0 D1 D2 q d1 d2 f
    v0 v1 v2 hf hs0 hq0 hsm0 hs1 hq1 hsm1 hs2 hq2 hsm2 hI0 hI1 hI2 hlqf hd1 hd2 hP0 hP1 hP2
    hc10 hc21 hve
  haveI hsq0 : Smooth q := SmoothOfRelativeDimension.smooth 1 q
  haveI hsq1 : Smooth (d1 ≫ q) := SmoothOfRelativeDimension.smooth 1 _
  haveI hsq2 : Smooth (d2 ≫ d1 ≫ q) := SmoothOfRelativeDimension.smooth 1 _
  have hcond : (q ≫ ι) ≫ b = f ≫ p := by rw [Category.assoc, hιb, hf]
  let F0 : D0 ⟶ pullback b p := pullback.lift (q ≫ ι) f hcond
  have hF0f : F0 ≫ pullback.fst b p = q ≫ ι := pullback.lift_fst _ _ _
  have hF0s : F0 ≫ pullback.snd b p = f := pullback.lift_snd _ _ _
  have hF0m : F0 = pullback.lift q f hf.symm ≫
      pullback.map (Spec.map (CommRingCat.ofHom (algebraMap k R))) p b p ι (𝟙 X) (𝟙 _)
        (by rw [Category.comp_id, hιb]) (by simp) := by
    apply pullback.hom_ext
    · rw [hF0f, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
    · rw [hF0s, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, Category.comp_id]
  haveI : LocallyQuasiFinite F0 := by rw [hF0m]; infer_instance
  haveI : QuasiCompact ι := MorphismProperty.of_postcomp (W := @QuasiCompact)
    (W' := @QuasiSeparated) ι b inferInstance (by rw [hιb]; infer_instance)
  haveI : LocallyOfFiniteType F0 := by
    have : LocallyOfFiniteType (F0 ≫ pullback.fst b p) := by rw [hF0f]; infer_instance
    exact locallyOfFiniteType_of_comp F0 (pullback.fst b p)
  haveI : QuasiCompact F0 := MorphismProperty.of_postcomp (W := @QuasiCompact)
    (W' := @QuasiSeparated) F0 (pullback.fst b p) inferInstance (by rw [hF0f]; infer_instance)
  haveI : IsSeparated F0 := MorphismProperty.of_postcomp (W := @IsSeparated)
    (W' := ⊤) F0 (pullback.fst b p) trivial (by rw [hF0f]; infer_instance)
  obtain ⟨Y0, g0, j0, hg0, hj0, hjg0, hY0, hdn0⟩ := stage k (pullback.fst b p ≫ b) F0
  obtain ⟨π, hπ⟩ : ∃ π' : Y0 ⟶ B, π' = g0 ≫ pullback.fst b p := ⟨_, rfl⟩
  haveI : IsProper π := by rw [hπ]; infer_instance
  have hw0 : j0 ≫ π = q ≫ ι := by rw [hπ, ← Category.assoc, hjg0, hF0f]
  haveI : LocallyOfFiniteType d1 := locallyOfFiniteType_of_comp d1 q
  have hF1 : (d1 ≫ j0) ≫ π = (d1 ≫ q) ≫ ι := by rw [Category.assoc, hw0, Category.assoc]
  haveI : QuasiCompact (d1 ≫ j0) := MorphismProperty.of_postcomp (W := @QuasiCompact)
    (W' := @QuasiSeparated) _ π inferInstance (by rw [hF1]; infer_instance)
  haveI : IsSeparated (d1 ≫ j0) := MorphismProperty.of_postcomp (W := @IsSeparated)
    (W' := ⊤) _ π trivial (by rw [hF1]; infer_instance)
  obtain ⟨Y1, g1, j1, hg1, hj1, hjg1, hY1, hdn1⟩ := stage k (π ≫ b) (d1 ≫ j0)
  have hw1 : j1 ≫ g1 ≫ π = (d1 ≫ q) ≫ ι := by rw [← Category.assoc, hjg1, hF1]
  haveI : LocallyOfFiniteType d2 := locallyOfFiniteType_of_comp d2 (d1 ≫ q)
  have hF2 : (d2 ≫ j1) ≫ g1 ≫ π = (d2 ≫ d1 ≫ q) ≫ ι := by
    rw [Category.assoc, hw1]
    simp only [Category.assoc]
  haveI : QuasiCompact (d2 ≫ j1) := MorphismProperty.of_postcomp (W := @QuasiCompact)
    (W' := @QuasiSeparated) _ (g1 ≫ π) inferInstance (by rw [hF2]; infer_instance)
  haveI : IsSeparated (d2 ≫ j1) := MorphismProperty.of_postcomp (W := @IsSeparated)
    (W' := ⊤) _ (g1 ≫ π) trivial (by rw [hF2]; infer_instance)
  obtain ⟨Y2, g2, j2, hg2, hj2, hjg2, hY2, hdn2⟩ := stage k ((g1 ≫ π) ≫ b) (d2 ≫ j1)
  have hw2 : j2 ≫ g2 ≫ g1 ≫ π = (d2 ≫ d1 ≫ q) ≫ ι := by rw [← Category.assoc, hjg2, hF2]
  haveI := hc0.2.1
  haveI := hc1.2.1
  haveI := hc2.2.1
  have hinj : Function.Injective (algebraMap R Ω) := fun x y hxy => Subtype.ext hxy
  have hpl0 := UpperTheory.mem_range_of_proper_generic_fibre_separated R Ω hinj ι π j0 hdn0 q hw0 c0 v0 hP0
  have hpl1 := UpperTheory.mem_range_of_proper_generic_fibre_separated R Ω hinj ι (g1 ≫ π) j1 hdn1 (d1 ≫ q) hw1 (γ1 ≫ c0) v1 hP1
  have hpl2 := UpperTheory.mem_range_of_proper_generic_fibre_separated R Ω hinj ι (g2 ≫ g1 ≫ π) j2 hdn2 (d2 ≫ d1 ≫ q) hw2
    (γ2 ≫ γ1 ≫ c0) v2 hP2
  have hZ : ∀ {Y W : Scheme} (π' : Y ⟶ B) [IsProper π'] (j : W ⟶ Y) [IsOpenImmersion j],
      IsClosed (π' '' (Set.range j)ᶜ) := fun π' _ j _ =>
    π'.isClosedMap _ j.isOpenEmbedding.isOpen_range.isClosed_compl
  let V : B.Opens := ⟨(π '' (Set.range j0)ᶜ ∪ (g1 ≫ π) '' (Set.range j1)ᶜ ∪
      (g2 ≫ g1 ≫ π) '' (Set.range j2)ᶜ)ᶜ,
    (((hZ π j0).union (hZ _ j1)).union (hZ _ j2)).isOpen_compl⟩
  have hV0 : ∀ y, π y ∈ V → y ∈ Set.range j0 := by
    intro y hy
    by_contra hn
    exact hy (Or.inl (Or.inl ⟨y, hn, rfl⟩))
  have hV1 : ∀ y, (g1 ≫ π) y ∈ V → y ∈ Set.range j1 := by
    intro y hy
    by_contra hn
    exact hy (Or.inl (Or.inr ⟨y, hn, rfl⟩))
  have hV2 : ∀ y, (g2 ≫ g1 ≫ π) y ∈ V → y ∈ Set.range j2 := by
    intro y hy
    by_contra hn
    exact hy (Or.inr ⟨y, hn, rfl⟩)
  have hVr : Set.range (Spec.map (CommRingCat.ofHom (algebraMap R Ω)) ≫ ι) ⊆ (V : Set B) := by
    intro x hx hmem
    rcases hmem with (⟨z, hz, rfl⟩ | ⟨z, hz, rfl⟩) | ⟨z, hz, rfl⟩
    · exact hz (hpl0 z hx)
    · exact hz (hpl1 z hx)
    · exact hz (hpl2 z hx)
  refine ⟨Y0, Y1, Y2, π, g1, g2, g0 ≫ pullback.snd b p, V, v0 ≫ j0, v1 ≫ j1, v2 ≫ j2, hVr,
    by unfold SmP; exact ⟨inferInstance, smooth_of j0 π ι q hw0 V hV0⟩,
    by unfold SmP; exact ⟨inferInstance, smooth_of j1 (g1 ≫ π) ι (d1 ≫ q) hw1 V hV1⟩,
    by unfold SmP; exact ⟨inferInstance, smooth_of j2 (g2 ≫ g1 ≫ π) ι _ hw2 V hV2⟩,
    inferInstance, inferInstance, UpperTheory.topologicalKrullDim_le_of_isOpenImmersion_integral k (π ≫ b) j0,
    pull_of j0 π ι q hw0 v0 c0 _ hP0 hpl0, pull_of j1 _ ι _ hw1 v1 _ _ hP1 hpl1,
    pull_of j2 _ ι _ hw2 v2 _ _ hP2 hpl2, ?_, ?_, ?_⟩
  · rw [← Category.assoc, hc10, Category.assoc, Category.assoc, hjg1]
  · rw [← Category.assoc, hc21, Category.assoc, Category.assoc, hjg2]
  · rw [Category.assoc, ← Category.assoc j0, hjg0, hF0s, hve]

end
