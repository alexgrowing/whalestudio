import Mathlib
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GenericExistsUniqueOActOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIntegralClosureOfEssFiniteTypeField
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ResidueCover

theorem exists_integral_multiple (A κ K : Type) [CommRing A] [Field κ] [Field K] [Algebra A κ]
    [Algebra κ K] [Algebra A K] [IsScalarTower A κ K] [Algebra.IsAlgebraic κ K]
    (h : ∀ z : κ, ∃ a b : A, z = algebraMap A κ a / algebraMap A κ b) (k : K) :
    ∃ y : A, algebraMap A K y ≠ 0 ∧ IsIntegral A (y • k) := by
  let B : Subalgebra A κ := ⊥
  haveI : IsFractionRing B κ := IsFractionRing.of_field B κ fun z => by
    obtain ⟨a, b, rfl⟩ := h z
    exact ⟨algebraMap A B a, algebraMap A B b, rfl⟩
  have hs : Function.Surjective (algebraMap A B) := by
    rintro ⟨_, a, rfl⟩
    exact ⟨a, rfl⟩
  haveI : Algebra.IsIntegral A B := Algebra.isIntegral_of_surjective hs
  have halg : IsAlgebraic B k :=
    (IsFractionRing.isAlgebraic_iff B κ K).mpr (Algebra.IsAlgebraic.isAlgebraic k)
  obtain ⟨y, hy0, hc⟩ := halg.exists_integral_multiple
  obtain ⟨a, rfl⟩ := hs y
  refine ⟨a, fun h0 => hy0 ?_, ?_⟩
  · rw [IsScalarTower.algebraMap_apply A κ K, map_eq_zero] at h0
    exact Subtype.ext h0
  · rw [algebraMap_smul] at hc
    exact isIntegral_trans _ hc

theorem isPreimmersion_toNormalization {Z : Scheme.{0}} (z₀ : Z) {K : Type} [Field K]
    [Algebra (Z.residueField z₀) K] [Algebra.IsAlgebraic (Z.residueField z₀) K]
    (g : Spec (CommRingCat.of K) ⟶ Z) [QuasiCompact g] [QuasiSeparated g]
    (hg : g = Spec.map (Z.residue z₀ ≫ CommRingCat.ofHom (algebraMap (Z.residueField z₀) K)) ≫
      Z.fromSpecStalk z₀) : IsPreimmersion g.toNormalization := by
  set cp : Spec (CommRingCat.of K) := IsLocalRing.closedPoint K with hcp
  set j := g.toNormalization with hj
  set π := g.fromNormalization with hπ
  have hjπ : j ≫ π = g := g.toNormalization_fromNormalization
  haveI hloc : IsLocalHom
      (Z.residue z₀ ≫ CommRingCat.ofHom (algebraMap (Z.residueField z₀) K)).hom := by
    refine ⟨fun a ha => ?_⟩
    by_contra hn
    have h : (Z.residue z₀).hom a = 0 := (IsLocalRing.residue_eq_zero_iff a).mpr hn
    exact ha.ne_zero ((congrArg (algebraMap (Z.residueField z₀) K) h).trans (map_zero _))
  have hgcp : g cp = z₀ := by
    rw [hg, Scheme.Hom.comp_apply, hcp]
    erw [Spec_closedPoint]
    exact Scheme.fromSpecStalk_closedPoint
  let φ := Scheme.stalkClosedPointTo (R := CommRingCat.of K) j
  have hsurj : Function.Surjective φ.hom := by
    intro k
    obtain ⟨_, ⟨U, hU, rfl⟩, hηU, -⟩ :=
      Z.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ z₀) isOpen_univ
    letI : Algebra Γ(Z, U) (Z.residueField z₀) := (Z.evaluation U z₀ hηU).hom.toAlgebra
    letI : Algebra Γ(Z, U) K :=
      ((algebraMap (Z.residueField z₀) K).comp (algebraMap Γ(Z, U) (Z.residueField z₀))).toAlgebra
    haveI : IsScalarTower Γ(Z, U) (Z.residueField z₀) K := .of_algebraMap_eq' rfl
    have hfrac : ∀ z : Z.residueField z₀, ∃ a b : Γ(Z, U),
        z = algebraMap _ _ a / algebraMap _ _ b := by
      intro z
      obtain ⟨s, rfl⟩ := Z.residue_surjective z₀ z
      letI := Z.presheaf.algebra_section_stalk (⟨z₀, hηU⟩ : U)
      haveI := hU.isLocalization_stalk ⟨z₀, hηU⟩
      obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (hU.primeIdealOf ⟨z₀, hηU⟩).asIdeal.primeCompl
        (S := Z.presheaf.stalk z₀) s
      have hu := (IsLocalization.map_units (Z.presheaf.stalk z₀) b).map (Z.residue z₀).hom
      refine ⟨a, b, ?_⟩
      have := congrArg (Z.residue z₀).hom hab
      rw [map_mul] at this
      exact (eq_div_iff hu.ne_zero).mpr this
    obtain ⟨y, hy0, hc⟩ := exists_integral_multiple Γ(Z, U) (Z.residueField z₀) K hfrac k
    have hcU : g cp ∈ U := hgcp ▸ hηU
    letI : Algebra Γ(Z, U) Γ(Spec (CommRingCat.of K), g ⁻¹ᵁ U) := (g.app U).hom.toAlgebra
    let ρ : Γ(Spec (CommRingCat.of K), g ⁻¹ᵁ U) →+* K :=
      ((Spec (CommRingCat.of K)).presheaf.germ (g ⁻¹ᵁ U) cp hcU ≫
        (stalkClosedPointIso (CommRingCat.of K)).hom).hom
    have hρA : ∀ a : Γ(Z, U), ρ (algebraMap _ _ a) = algebraMap Γ(Z, U) K a := by
      intro a
      have key : ∀ (g' : Spec (CommRingCat.of K) ⟶ Z) (hg' : g' = Spec.map (Z.residue z₀ ≫
          CommRingCat.ofHom (algebraMap (Z.residueField z₀) K)) ≫ Z.fromSpecStalk z₀)
          (hU' : g' (IsLocalRing.closedPoint K) ∈ U),
          (stalkClosedPointIso (CommRingCat.of K)).hom
            ((Spec (CommRingCat.of K)).presheaf.germ (g' ⁻¹ᵁ U) (IsLocalRing.closedPoint K) hU'
              (g'.app U a)) = algebraMap Γ(Z, U) K a := by
        intro g' hg' hU'
        subst hg'
        have e := Scheme.germ_stalkClosedPointTo_Spec_fromSpecStalk
          (Z.residue z₀ ≫ CommRingCat.ofHom (algebraMap (Z.residueField z₀) K)) U hU'
        refine Eq.trans ?_ (congrArg (fun q => q.hom a) e)
        change _ = (stalkClosedPointIso (CommRingCat.of K)).hom.hom ((Scheme.Hom.stalkMap _ _).hom
          ((Z.presheaf.germ U _ hU').hom a))
        congr 1
        exact (Scheme.Hom.germ_stalkMap_apply _ _ _ _ _).symm
      exact key g hg hcU
    have htop : g ⁻¹ᵁ U = ⊤ := Scheme.preimage_eq_top_of_closedPoint_mem g hcU
    let res := (Spec (CommRingCat.of K)).presheaf.map (homOfLE (le_top : g ⁻¹ᵁ U ≤ ⊤)).op
    have hres : Function.Bijective res.hom := by
      have : IsIso res := by
        have e : homOfLE (le_top : g ⁻¹ᵁ U ≤ ⊤) = eqToHom htop := Subsingleton.elim _ _
        simp only [res, e]; infer_instance
      exact ConcreteCategory.bijective_of_isIso res
    have hρres : ∀ t, ρ (res.hom t) = (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom t := by
      intro t
      change (stalkClosedPointIso _).hom.hom (((Spec _).presheaf.germ _ cp hcU).hom (res.hom t)) = _
      refine (congrArg (stalkClosedPointIso (CommRingCat.of K)).hom.hom
        (TopCat.Presheaf.germ_res_apply (Spec (CommRingCat.of K)).presheaf
          (homOfLE (le_top : g ⁻¹ᵁ U ≤ ⊤)) cp hcU t)).trans ?_
      exact congrArg (fun q => q.hom t) (germ_stalkClosedPointIso_hom (CommRingCat.of K))
    have hρ : Function.Bijective ρ := by
      have hb : Function.Bijective (ρ ∘ res.hom) := by
        rw [show ρ ∘ res.hom = (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom from funext hρres]
        exact ConcreteCategory.bijective_of_isIso _
      exact (Function.Bijective.of_comp_iff ρ hres).mp hb
    let ρA : Γ(Spec (CommRingCat.of K), g ⁻¹ᵁ U) →ₐ[Γ(Z, U)] K := { ρ with commutes' := hρA }
    obtain ⟨r, hr⟩ := hρ.2 (y • k)
    have hrint : IsIntegral Γ(Z, U) r :=
      (isIntegral_algHom_iff ρA hρ.1).mp (by rw [show ρA r = y • k from hr]; exact hc)
    have hξU : j cp ∈ π ⁻¹ᵁ U := by
      change π (j cp) ∈ U
      rw [← Scheme.Hom.comp_apply, hjπ]
      exact hcU
    have hval : ∀ (r : Γ(Spec (CommRingCat.of K), g ⁻¹ᵁ U)) (hr : IsIntegral Γ(Z, U) r),
        φ.hom (g.normalization.presheaf.germ (π ⁻¹ᵁ U) _ hξU
          ((g.normalizationObjIso hU).inv.hom ⟨r, hr⟩)) = ρ r := by
      intro r hr
      set b : Γ(g.normalization, π ⁻¹ᵁ U) := (g.normalizationObjIso hU).inv.hom ⟨r, hr⟩ with hb
      have hφ : φ.hom (g.normalization.presheaf.germ (π ⁻¹ᵁ U) _ hξU b) =
          (stalkClosedPointIso (CommRingCat.of K)).hom
            ((Spec (CommRingCat.of K)).presheaf.germ (j ⁻¹ᵁ π ⁻¹ᵁ U) cp hξU (j.app _ b)) := by
        change (stalkClosedPointIso (CommRingCat.of K)).hom.hom ((Scheme.Hom.stalkMap j cp).hom _) = _
        congr 1
        exact Scheme.Hom.germ_stalkMap_apply _ _ _ _ _
      refine hφ.trans ?_
      have hv : ((g.normalizationObjIso hU).hom ≫
          CommRingCat.ofHom (Subalgebra.val _).toRingHom).hom b = r := by
        change ((g.normalizationObjIso hU).hom.hom ((g.normalizationObjIso hU).inv.hom ⟨r, hr⟩)).1 = r
        rw [Iso.inv_hom_id_apply]
      rw [g.normalizationObjIso_hom_val hU, Scheme.Hom.appLE] at hv
      rw [← hv]
      change _ = (stalkClosedPointIso _).hom.hom (((Spec _).presheaf.germ _ cp hcU).hom
        (((Spec _).presheaf.map _).hom ((g.toNormalization.app _).hom b)))
      exact congrArg (stalkClosedPointIso (CommRingCat.of K)).hom.hom
        (TopCat.Presheaf.germ_res_apply (Spec (CommRingCat.of K)).presheaf _ cp hcU _).symm
    have h1 := (hval r hrint).trans hr
    have h2 := (hval (algebraMap _ _ y) isIntegral_algebraMap).trans (hρA y)
    have hu : IsUnit (g.normalization.presheaf.germ (π ⁻¹ᵁ U) _ hξU
        ((g.normalizationObjIso hU).inv.hom ⟨algebraMap _ _ y, isIntegral_algebraMap⟩)) :=
      IsLocalHom.map_nonunit (f := φ.hom) _ (by rw [h2]; exact hy0.isUnit)
    obtain ⟨v, hv⟩ := hu.exists_right_inv
    have h3 := congrArg φ.hom hv
    rw [map_mul, map_one, h2] at h3
    refine ⟨g.normalization.presheaf.germ (π ⁻¹ᵁ U) _ hξU
      ((g.normalizationObjIso hU).inv.hom ⟨r, hrint⟩) * v, ?_⟩
    rw [map_mul, h1, Algebra.smul_def, mul_right_comm]
    exact (congrArg (· * k) h3).trans (one_mul k)
  refine { stalkMap_surjective := fun x => ?_, isEmbedding := .of_subsingleton _ }
  obtain rfl : x = cp := Subsingleton.elim _ _
  exact Function.Surjective.of_comp_left (f := (stalkClosedPointIso (CommRingCat.of K)).hom.hom)
    hsurj (ConcreteCategory.bijective_of_isIso (stalkClosedPointIso (CommRingCat.of K)).hom).1

theorem exists_normal_finite_cover : ∀ (F : Type) [Field F] [CharZero F] (Y : Scheme.{0}) (p : Y ⟶ Sp F) [LocallyOfFiniteType p] [QuasiCompact p] (y₀ : Y) (k' : Type) [Field k'] [Algebra (Y.residueField y₀) k'] [FiniteDimensional (Y.residueField y₀) k'], ∃ (W : Scheme.{0}) (_ : IsIntegral W) (π : W ⟶ Y) (j : Sp k' ⟶ W), IsFinite π ∧ AlgebraicGeometry.IsNoetherian W ∧ ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme W ∧ GlobalTheory.IsGenericPointHom j ∧ j ≫ π = spMap (algebraMap (Y.residueField y₀) k') ≫ Y.fromSpecResidueField y₀ := by
  intro F _ _ Y p _ _ y₀ k' _ _ _
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian p
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace p
  haveI : CharZero (Y.residueField y₀) := charZero_of_injective_ringHom
    ((Scheme.ΓSpecIso (.of F)).inv ≫ p.appTop ≫ Y.Γevaluation y₀).hom.injective
  haveI : CharZero k' := charZero_of_injective_algebraMap (algebraMap (Y.residueField y₀) k').injective
  let φ : Y.presheaf.stalk y₀ ⟶ .of k' :=
    Y.residue y₀ ≫ CommRingCat.ofHom (algebraMap (Y.residueField y₀) k')
  have hφ : φ.hom.EssFiniteType :=
    .comp (RingHom.FiniteType.of_surjective _ (Y.residue_surjective y₀)).essFiniteType
      (RingHom.finite_algebraMap.mpr inferInstance).finiteType.essFiniteType
  let g : Spec (.of k') ⟶ Y := Spec.map φ ≫ Y.fromSpecStalk y₀
  haveI hfin : IsFinite g.fromNormalization :=
    GlobalTheory.isFinite_fromNormalization_SpecMap_fromSpecStalk p y₀ φ hφ
  haveI := isPreimmersion_toNormalization y₀ g rfl
  haveI := GlobalTheory.IsNormalScheme.normalization_of_isIntegral g
  haveI : IsLocallyNoetherian g.normalization :=
    LocallyOfFiniteType.isLocallyNoetherian g.fromNormalization
  haveI : CompactSpace g.normalization :=
    QuasiCompact.compactSpace_of_compactSpace g.fromNormalization
  refine ⟨g.normalization, inferInstance, g.fromNormalization, g.toNormalization, hfin, {},
    GlobalTheory.IsNormalScheme.pred _, .of_isPreimmersion _, ?_⟩
  rw [g.toNormalization_fromNormalization]
  exact ((Spec.map_comp _ _) =≫ _).trans (Category.assoc _ _ _)

end GlobalTheory.ResidueCover
