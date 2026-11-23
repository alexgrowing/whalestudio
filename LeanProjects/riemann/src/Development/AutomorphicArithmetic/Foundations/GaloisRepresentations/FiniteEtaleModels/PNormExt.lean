import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.IsQuotTriv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtensionOverNormalQuasiProjectiveBase

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo
open UpperTheory.Gal.G3 (sp)
open UpperTheory.Gal.FiniteEtaleModels

private theorem exists_affine_irreducible_open_nhd (S : Scheme) [IsLocallyNoetherian S]
    (hd : ∀ x : S, IsDomain (S.presheaf.stalk x)) (x : S) :
    ∃ V : S.Opens, IsAffineOpen V ∧ x ∈ V ∧ IsIrreducible (V : Set S) := by
  have hG : IsIrreducible {y : S | y ⤳ x} := by
    rw [← Scheme.range_fromSpecStalk]
    haveI := hd x
    simpa [Set.image_univ] using
      (IrreducibleSpace.isIrreducible_univ _).image _ (S.fromSpecStalk x).continuous.continuousOn
  obtain ⟨N, hN, hxN, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp S.isBasis_affineOpens)
    (show x ∈ (⊤ : S.Opens) from trivial)
  haveI : IsNoetherianRing Γ(S, N) := IsLocallyNoetherian.component_noetherian ⟨N, hN⟩
  haveI : TopologicalSpace.NoetherianSpace N := noetherianSpace_of_isAffineOpen N hN
  let x' : N := ⟨x, hxN⟩
  let C : Set (Set N) := {Z | Z ∈ irreducibleComponents N ∧ x' ∉ Z}
  have hCfin : C.Finite :=
    TopologicalSpace.NoetherianSpace.finite_irreducibleComponents.subset (fun Z hZ => hZ.1)
  let O : Set N := (⋃₀ C)ᶜ
  have hO : IsOpen O := by
    refine isOpen_compl_iff.mpr ?_
    rw [Set.sUnion_eq_biUnion]
    exact hCfin.isClosed_biUnion (fun Z hZ => isClosed_of_mem_irreducibleComponents Z hZ.1)
  have hxO : x' ∈ O := fun ⟨Z, hZ, hxZ⟩ => hZ.2 hxZ
  let O' : Set S := Subtype.val '' O
  have hO' : IsOpen O' := N.isOpen.isOpenMap_subtype_val O hO
  have hsub : O' ⊆ closure {y : S | y ⤳ x} := by
    rintro _ ⟨y, hyO, rfl⟩
    obtain ⟨Z, hZ, hyZ⟩ : ∃ Z ∈ irreducibleComponents N, y ∈ Z := by
      have h := Set.mem_univ y
      rw [← sUnion_irreducibleComponents] at h
      obtain ⟨Z, hZ, hyZ⟩ := h
      exact ⟨Z, hZ, hyZ⟩
    have hxZ : x' ∈ Z := by
      by_contra h
      exact hyO ⟨Z, ⟨hZ, h⟩, hyZ⟩
    have hT : IsIrreducible (Subtype.val '' Z) := hZ.1.image _ continuous_subtype_val.continuousOn
    have hgen := hT.isGenericPoint_genericPoint_closure
    have h1 : hT.genericPoint ⤳ x := hgen.specializes (subset_closure ⟨x', hxZ, rfl⟩)
    have h2 : (y : S) ∈ closure {hT.genericPoint} :=
      specializes_iff_mem_closure.mp (hgen.specializes (subset_closure ⟨y, hyZ, rfl⟩))
    exact closure_mono (Set.singleton_subset_iff.mpr h1) h2
  obtain ⟨V, hV, hxV, hVO⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp S.isBasis_affineOpens)
    (show x ∈ (⟨O', hO'⟩ : S.Opens) from ⟨x', hxO, rfl⟩)
  exact ⟨V, hV, hxV, ⟨x, hxV⟩, hG.closure.2.open_subset V.isOpen (fun z hz => hsub (hVO hz))⟩

private theorem injective_germ_of_generic_in_open (X : Scheme) [IsReduced X] (W : X.Opens) (x : X) (hx : x ∈ W)
    (hgen : ∀ y ∈ W, x ⤳ y) : Function.Injective (X.presheaf.germ W x hx).hom := by
  rw [injective_iff_map_eq_zero]
  intro s hs
  rw [← basicOpen_eq_bot_iff]
  refine eq_bot_iff.mpr (fun y hy => ?_)
  have hyW : y ∈ W := X.basicOpen_le s hy
  have hxb : x ∈ X.basicOpen s := (hgen y hyW).mem_open (X.basicOpen s).isOpen hy
  rw [Scheme.mem_basicOpen X s x hx] at hxb
  rw [hs] at hxb
  exact absurd hxb not_isUnit_zero

private theorem normalization_affine_open_irreducible_of_normal {U S : Scheme} (i : U ⟶ S) [IsOpenImmersion i] [IsDominant i]
    (hd : ∀ x : S, IsDomain (S.presheaf.stalk x))
    (hc : ∀ x : S, IsIntegrallyClosed (S.presheaf.stalk x))
    (V : S.Opens) (hV : IsAffineOpen V) (hirr : IsIrreducible (V : Set S)) :
    letI := (i.app V).hom.toAlgebra
    Function.Bijective (algebraMap Γ(S, V) (integralClosure Γ(S, V) Γ(U, i ⁻¹ᵁ V))) := by
  letI := (i.app V).hom.toAlgebra
  haveI : ∀ x : S, _root_.IsReduced (S.presheaf.stalk x) := fun x => by
    haveI := hd x
    infer_instance
  haveI : IsReduced S := isReduced_of_isReduced_stalk S
  haveI : IsReduced U := isReduced_of_isOpenImmersion i
  have hgen := hirr.isGenericPoint_genericPoint_closure
  have hηV : hirr.genericPoint ∈ V := (hgen.mem_open_set_iff V.isOpen).mpr
    ⟨hirr.1.some, subset_closure hirr.1.some_mem, hirr.1.some_mem⟩
  have hsp : ∀ y ∈ V, hirr.genericPoint ⤳ y := fun y hy => hgen.specializes (subset_closure hy)
  obtain ⟨u, hu⟩ : hirr.genericPoint ∈ Set.range i := by
    obtain ⟨z, hzV, hzr⟩ := i.denseRange.inter_open_nonempty V V.isOpen hirr.1
    exact (hsp z hzV).mem_open i.isOpenEmbedding.isOpen_range hzr
  have hiuV : i u ∈ V := hu ▸ hηV
  have hspS : ∀ y ∈ V, i u ⤳ y := fun y hy => hu ▸ hsp y hy
  have huV : u ∈ i ⁻¹ᵁ V := hiuV
  have hspU : ∀ y ∈ i ⁻¹ᵁ V, u ⤳ y := fun y hy => by
    rw [← i.isOpenEmbedding.isInducing.specializes_iff]
    exact hspS _ hy
  have hφ : i.app V ≫ (U.presheaf.germ (i ⁻¹ᵁ V) u huV ≫ inv (i.stalkMap u)) =
      S.presheaf.germ V (i u) hiuV := by
    rw [← cancel_mono (i.stalkMap u), Category.assoc, Category.assoc, IsIso.inv_hom_id,
      Category.comp_id]
    exact (i.germ_stalkMap V u hiuV).symm
  have hg0inj : Function.Injective (S.presheaf.germ V (i u) hiuV).hom :=
    injective_germ_of_generic_in_open S V (i u) hiuV hspS
  have hφinj : Function.Injective
      (U.presheaf.germ (i ⁻¹ᵁ V) u huV ≫ inv (i.stalkMap u)).hom := by
    have h1 := injective_germ_of_generic_in_open U (i ⁻¹ᵁ V) u huV hspU
    have h2 : Function.Injective (inv (i.stalkMap u)).hom :=
      ((ConcreteCategory.isIso_iff_bijective _).mp inferInstance).1
    rw [CommRingCat.hom_comp, RingHom.coe_comp]
    exact h2.comp h1
  haveI : IsDomain (S.presheaf.stalk (i u)) := hd _
  haveI : IsDomain Γ(S, V) := Function.Injective.isDomain _ hg0inj
  letI : Algebra Γ(S, V) (S.presheaf.stalk (i u)) :=
    TopCat.Presheaf.algebra_section_stalk S.presheaf (⟨i u, hiuV⟩ : V)
  have hloc := hV.isLocalization_stalk ⟨i u, hiuV⟩
  have hP : (hV.primeIdealOf ⟨i u, hiuV⟩).asIdeal = ⊥ := by
    refine eq_bot_iff.mpr (fun a ha => ?_)
    have hnu : ¬ IsUnit (algebraMap Γ(S, V) (S.presheaf.stalk (i u)) a) := by
      rw [IsLocalization.AtPrime.isUnit_to_map_iff _ (hV.primeIdealOf ⟨i u, hiuV⟩).asIdeal]
      exact fun h => h ha
    have hnot : i u ∉ S.basicOpen a := by
      rw [Scheme.mem_basicOpen S a (i u) hiuV]
      exact hnu
    rw [Submodule.mem_bot, ← basicOpen_eq_bot_iff]
    exact eq_bot_iff.mpr (fun y hy =>
      hnot ((hspS y (S.basicOpen_le a hy)).mem_open (S.basicOpen a).isOpen hy))
  haveI hfr : IsFractionRing Γ(S, V) (S.presheaf.stalk (i u)) := by
    have e : (hV.primeIdealOf ⟨i u, hiuV⟩).asIdeal.primeCompl = nonZeroDivisors Γ(S, V) := by
      ext a
      simp [Ideal.primeCompl, hP, mem_nonZeroDivisors_iff_ne_zero]
    unfold IsLocalization.AtPrime at hloc
    rw [e] at hloc
    exact hloc
  haveI : IsIntegrallyClosed Γ(S, V) := by
    refine IsIntegrallyClosed.of_localization_maximal ?_
    intro p _ hpm
    let q : PrimeSpectrum Γ(S, V) := ⟨p, hpm.isPrime⟩
    have hq : hV.fromSpec q ∈ V := by
      show hV.fromSpec q ∈ (V : Set S)
      rw [← hV.range_fromSpec]
      exact ⟨q, rfl⟩
    letI : Algebra Γ(S, V) (S.presheaf.stalk (hV.fromSpec q)) :=
      TopCat.Presheaf.algebra_section_stalk S.presheaf (⟨hV.fromSpec q, hq⟩ : V)
    haveI : IsLocalization p.primeCompl (S.presheaf.stalk (hV.fromSpec q)) :=
      hV.isLocalization_stalk' q hq
    haveI := hc (hV.fromSpec q)
    exact IsIntegrallyClosed.of_equiv (IsLocalization.algEquiv p.primeCompl
      (S.presheaf.stalk (hV.fromSpec q)) (Localization.AtPrime p)).toRingEquiv
  constructor
  · intro a b hab
    apply hg0inj
    have hab' : (i.app V).hom a = (i.app V).hom b := congrArg Subtype.val hab
    rw [← hφ, CommRingCat.hom_comp, RingHom.comp_apply, RingHom.comp_apply, hab']
  · rintro ⟨t, ht⟩
    have hint : IsIntegral Γ(S, V)
        ((U.presheaf.germ (i ⁻¹ᵁ V) u huV ≫ inv (i.stalkMap u)).hom t) := by
      refine IsIntegral.map_of_comp_eq (RingHom.id _) _ ?_ ht
      ext a
      exact (congrArg (fun f => CommRingCat.Hom.hom f a) hφ).symm
    obtain ⟨r, hr⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
    refine ⟨r, Subtype.ext (hφinj ?_)⟩
    rw [← hr]
    exact congrArg (fun f => CommRingCat.Hom.hom f r) hφ

private theorem isIso_fromNormalization_of_normal_noetherian {U S : Scheme} (i : U ⟶ S) [IsOpenImmersion i] [IsDominant i]
    [IsLocallyNoetherian S]
    (hd : ∀ x : S, IsDomain (S.presheaf.stalk x))
    (hc : ∀ x : S, IsIntegrallyClosed (S.presheaf.stalk x)) :
    IsIso i.fromNormalization := by
  have hcov : iSup (fun V : {V : S.Opens // IsAffineOpen V ∧ IsIrreducible (V : Set S)} => V.1) = ⊤ := by
    refine eq_top_iff.mpr (fun x _ => ?_)
    obtain ⟨V, hV, hxV, hirr⟩ := exists_affine_irreducible_open_nhd S hd x
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨V, hV, hirr⟩, hxV⟩
  rw [← MorphismProperty.isomorphisms.iff,
    IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := MorphismProperty.isomorphisms Scheme) _ hcov]
  rintro ⟨V, hV, hirr⟩
  let W : S.AffineZariskiSite := ⟨V, hV⟩
  haveI : IsOpenImmersion (i.normalizationOpenCover.f W) := i.normalizationOpenCover.map_prop W
  let e := IsOpenImmersion.isoOfRangeEq (i.fromNormalization ⁻¹ᵁ V).ι
    (i.normalizationOpenCover.f W)
    (by
      rw [Scheme.Opens.range_ι]
      exact congr($(i.fromNormalization_preimage ⟨V, hV⟩).1))
  rw [← MorphismProperty.cancel_left_of_respectsIso (MorphismProperty.isomorphisms Scheme) e.inv,
    ← MorphismProperty.cancel_right_of_respectsIso (MorphismProperty.isomorphisms Scheme) _
      hV.isoSpec.hom]
  have hb := normalization_affine_open_irreducible_of_normal i hd hc V hV hirr
  haveI : IsIso (i.normalizationDiagramMap.app (.op V)) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    exact hb
  rw [MorphismProperty.isomorphisms.iff]
  have key : e.inv ≫ (i.fromNormalization ∣_ V) ≫ hV.isoSpec.hom =
      (Spec.map (i.normalizationDiagramMap.app (.op V)) :
        i.normalizationOpenCover.X W ⟶ Spec Γ(S, V)) := by
    refine (cancel_mono hV.fromSpec).mp ?_
    simp [IsAffineOpen.isoSpec_hom, e, Scheme.Hom.ι_fromNormalization]
    exact i.ι_fromNormalization ⟨V, hV⟩
  show IsIso (e.inv ≫ (i.fromNormalization ∣_ V) ≫ hV.isoSpec.hom)
  rw [key]
  exact (inferInstance : IsIso (Spec.map (i.normalizationDiagramMap.app (.op V))))

theorem UpperTheory.Gal.FiniteEtaleModels.normExt_holds :
    NormExt := by
  unfold UpperTheory.Gal.FiniteEtaleModels.NormExt
  intro U S Y B i f g y hi hdom hnoeth hdst hic hfin hcomm
  haveI := hi
  haveI := hdom
  haveI := hnoeth
  haveI := hfin
  haveI : IsIso i.fromNormalization := isIso_fromNormalization_of_normal_noetherian i hdst hic
  have H : i = pullback.lift y i hcomm ≫ pullback.snd g f := (pullback.lift_snd _ _ _).symm
  refine ⟨inv i.fromNormalization ≫
    i.normalizationDesc (pullback.lift y i hcomm) (pullback.snd g f) H ≫ pullback.fst g f, ?_, ?_⟩
  · have h1 : i ≫ inv i.fromNormalization = i.toNormalization := by
      rw [IsIso.comp_inv_eq, Scheme.Hom.toNormalization_fromNormalization]
    rw [reassoc_of% h1, Scheme.Hom.toNormalization_normalizationDesc_assoc, pullback.lift_fst]
  · rw [Category.assoc, Category.assoc, pullback.condition,
      Scheme.Hom.normalizationDesc_comp_assoc, IsIso.inv_hom_id_assoc]
