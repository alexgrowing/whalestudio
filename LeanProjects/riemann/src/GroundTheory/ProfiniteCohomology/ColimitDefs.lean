import Mathlib
import GroundTheory.ProfiniteCohomology.ContinuousCochains.Functoriality
import GroundTheory.ProfiniteCohomology.OpenNormal
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory groupCohomology

universe u

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G]

theorem isLocallyConstant_comp_quotient_mk [IsTopologicalGroup G] (U : OpenNormalSubgroup G) {n : ℕ} {X : Type*}
    (y : (Fin n → G ⧸ (U : Subgroup G)) → X) :
    IsLocallyConstant fun g : Fin n → G => y fun i => (g i : G ⧸ (U : Subgroup G)) :=
  (IsLocallyConstant.of_discrete y).comp_continuous
    (continuous_pi fun i => continuous_quot_mk.comp (continuous_apply i))

noncomputable abbrev quotientMapOfLE {U V : OpenNormalSubgroup G} (h : V ≤ U) :
    G ⧸ (V : Subgroup G) →* G ⧸ (U : Subgroup G) :=
  QuotientGroup.map _ _ (MonoidHom.id G) fun _ hx => h hx

@[simp]
theorem quotientMapOfLE_mk {U V : OpenNormalSubgroup G} (h : V ≤ U) (g : G) :
    quotientMapOfLE h (g : G ⧸ (V : Subgroup G)) = (g : G ⧸ (U : Subgroup G)) :=
  rfl

section Level

variable (A : Rep.{u} k G)

noncomputable def invariantsInclusion {U V : OpenNormalSubgroup G} (h : V ≤ U) :
    Rep.res (quotientMapOfLE h) (A.quotientToInvariants (U : Subgroup G)) ⟶
      A.quotientToInvariants (V : Subgroup G) :=
  Rep.ofHom ⟨Submodule.inclusion (invariants_comp_subtype_antitone A fun _ hx => h hx),
    fun g => QuotientGroup.induction_on g fun _ => LinearMap.ext fun _ => rfl⟩

@[simp]
theorem invariantsInclusion_hom_apply {U V : OpenNormalSubgroup G} (h : V ≤ U)
    (x : Representation.invariants (A.ρ.comp (U : Subgroup G).subtype)) :
    ((invariantsInclusion A h).hom x : A) = x :=
  rfl

noncomputable abbrev transitionCochains {U V : OpenNormalSubgroup G} (h : V ≤ U) :
    inhomogeneousCochains (A.quotientToInvariants (U : Subgroup G)) ⟶
      inhomogeneousCochains (A.quotientToInvariants (V : Subgroup G)) :=
  groupCohomology.cochainsMap (quotientMapOfLE h) (invariantsInclusion A h)

noncomputable def transition {U V : OpenNormalSubgroup G} (h : V ≤ U) (n : ℕ) :
    groupCohomology (A.quotientToInvariants (U : Subgroup G)) n ⟶
      groupCohomology (A.quotientToInvariants (V : Subgroup G)) n :=
  groupCohomology.map (quotientMapOfLE h) (invariantsInclusion A h) n

theorem transitionCochains_refl (U : OpenNormalSubgroup G) :
    transitionCochains A (le_refl U) = 𝟙 _ := by
  rw [← groupCohomology.cochainsMap_id]
  exact groupCohomology.cochainsMap_congr
    (MonoidHom.ext fun g => QuotientGroup.induction_on g fun _ => rfl) (LinearMap.ext fun _ => rfl)

theorem transitionCochains_trans {U V W : OpenNormalSubgroup G} (hVU : V ≤ U) (hWV : W ≤ V) :
    transitionCochains A (hWV.trans hVU) =
      transitionCochains A hVU ≫ transitionCochains A hWV := by
  rw [← groupCohomology.cochainsMap_comp]
  exact groupCohomology.cochainsMap_congr
    (MonoidHom.ext fun g => QuotientGroup.induction_on g fun _ => rfl) (LinearMap.ext fun _ => rfl)

variable (k G) in

example [Nonempty (OpenNormalSubgroup G)] : IsFiltered (OpenNormalSubgroup G)ᵒᵖ := inferInstance

@[simps]
noncomputable def levelCochains :
    (OpenNormalSubgroup G)ᵒᵖ ⥤ CochainComplex (ModuleCat k) ℕ where
  obj U := inhomogeneousCochains (A.quotientToInvariants (U.unop : Subgroup G))
  map f := transitionCochains A (leOfHom f.unop)
  map_id U := transitionCochains_refl A U.unop
  map_comp f g := transitionCochains_trans A (leOfHom f.unop) (leOfHom g.unop)

noncomputable abbrev levelFunctor (n : ℕ) : (OpenNormalSubgroup G)ᵒᵖ ⥤ ModuleCat k :=
  levelCochains A ⋙ HomologicalComplex.homologyFunctor (ModuleCat k) (ComplexShape.up ℕ) n

theorem levelFunctor_obj (n : ℕ) (U : (OpenNormalSubgroup G)ᵒᵖ) :
    (levelFunctor A n).obj U = groupCohomology (A.quotientToInvariants (U.unop : Subgroup G)) n :=
  rfl

theorem levelFunctor_map (n : ℕ) {U V : (OpenNormalSubgroup G)ᵒᵖ} (f : U ⟶ V) :
    (levelFunctor A n).map f = transition A (leOfHom f.unop) n :=
  rfl

variable [IsTopologicalGroup G] [IsDiscreteRep A]

noncomputable abbrev infCochains (U : OpenNormalSubgroup G) :
    inhomogeneousCochains (A.quotientToInvariants (U : Subgroup G)) ⟶ inhomogeneousCochains A :=
  groupCohomology.cochainsMap (QuotientGroup.mk' (U : Subgroup G))
    (Rep.ofHom (A.ρ.quotientToInvariants_lift (U : Subgroup G)))

noncomputable def inflationCochainsX (U : OpenNormalSubgroup G) (n : ℕ) :
    (inhomogeneousCochains (A.quotientToInvariants (U : Subgroup G))).X n ⟶
      (cochainsComplex A).X n :=
  ModuleCat.ofHom <| LinearMap.codRestrict (locallyConstantCochains A n)
    ((infCochains A U).f n).hom
    fun x => isLocallyConstant_comp_quotient_mk U fun q => (x q : A)

theorem inflationCochainsX_comp_ι (U : OpenNormalSubgroup G) (n : ℕ) :
    inflationCochainsX A U n ≫ (cochainsComplexι A).f n = (infCochains A U).f n :=
  rfl

noncomputable def inflationCochains (U : OpenNormalSubgroup G) :
    inhomogeneousCochains (A.quotientToInvariants (U : Subgroup G)) ⟶ cochainsComplex A where
  f n := inflationCochainsX A U n
  comm' i j _ := by
    rw [← cancel_mono ((cochainsComplexι A).f j), Category.assoc, Category.assoc,
      ← (cochainsComplexι A).comm i j, ← Category.assoc, inflationCochainsX_comp_ι,
      inflationCochainsX_comp_ι, HomologicalComplex.Hom.comm]

@[simp]
theorem inflationCochains_f_hom_apply (U : OpenNormalSubgroup G) (n : ℕ)
    (x : (Fin n → G ⧸ (U : Subgroup G)) →
      Representation.invariants (A.ρ.comp (U : Subgroup G).subtype)) (g : Fin n → G) :
    ((cochainsComplexι A).f n).hom (((inflationCochains A U).f n).hom x) g =
      (x fun i => (g i : G ⧸ (U : Subgroup G)) : A) :=
  rfl

theorem inflationCochains_comp_cochainsComplexι (U : OpenNormalSubgroup G) :
    inflationCochains A U ≫ cochainsComplexι A = infCochains A U := by
  ext n : 1
  exact inflationCochainsX_comp_ι A U n

noncomputable def inflation (U : OpenNormalSubgroup G) (n : ℕ) :
    groupCohomology (A.quotientToInvariants (U : Subgroup G)) n ⟶ cohomology A n :=
  HomologicalComplex.homologyMap (inflationCochains A U) n

theorem inflation_comp_cohomologyToGroupCohomology (U : OpenNormalSubgroup G) (n : ℕ) :
    inflation A U n ≫ cohomologyToGroupCohomology A n =
      (groupCohomology.infNatTrans k (U : Subgroup G) n).app A := by
  unfold inflation cohomologyToGroupCohomology
  refine (HomologicalComplex.homologyMap_comp _ _ n).symm.trans ?_
  rw [inflationCochains_comp_cochainsComplexι]
  rfl

theorem transitionCochains_comp_inflationCochains {U V : OpenNormalSubgroup G} (h : V ≤ U) :
    transitionCochains A h ≫ inflationCochains A V = inflationCochains A U := by
  ext n : 1
  rw [← cancel_mono ((cochainsComplexι A).f n), HomologicalComplex.comp_f, Category.assoc]
  ext x : 2
  rfl

theorem transition_comp_inflation {U V : OpenNormalSubgroup G} (h : V ≤ U) (n : ℕ) :
    transition A h n ≫ inflation A V n = inflation A U n := by
  unfold transition inflation
  refine (HomologicalComplex.homologyMap_comp _ _ n).symm.trans ?_
  rw [transitionCochains_comp_inflationCochains]

@[simps]
noncomputable def inflationCochainsCocone : Limits.Cocone (levelCochains A) where
  pt := cochainsComplex A
  ι :=
    { app U := inflationCochains A U.unop
      naturality U V f := by
        exact (transitionCochains_comp_inflationCochains A (leOfHom f.unop)).trans
          (Category.comp_id _).symm }

noncomputable abbrev inflationCocone (n : ℕ) : Limits.Cocone (levelFunctor A n) :=
  (HomologicalComplex.homologyFunctor (ModuleCat k) (ComplexShape.up ℕ) n).mapCocone
    (inflationCochainsCocone A)

theorem inflationCocone_pt (n : ℕ) : (inflationCocone A n).pt = cohomology A n :=
  rfl

theorem inflationCocone_ι_app (n : ℕ) (U : (OpenNormalSubgroup G)ᵒᵖ) :
    (inflationCocone A n).ι.app U = inflation A U.unop n :=
  rfl

end Level

end GroundTheory.ProfCoh
