import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime
import Development.AbelianVarietyTheory.Statements.HeckeInFamilies.GenericMemChart
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.BijectiveAlgebraMapIntegralClosureOfBirational
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueLiftOfDensePart
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory

theorem isOpenImmersion_of_isFinite_of_densePart {U W Z : Scheme.{0}} [IsIntegral W]
    [IsLocallyNoetherian Z] [GlobalTheory.IsNormalScheme Z] (j : U ⟶ W) (g : W ⟶ Z) [IsFinite g]
    [IsPreimmersion j] [Flat j] [IsDominant j] [QuasiCompact j] [Flat (j ≫ g)]
    [SurjectiveOnStalks (j ≫ g)] : IsOpenImmersion g := by
  have hη : genericPoint W ∈ genericPoints W := by
    rw [genericPoints_eq_singleton]; rfl
  obtain ⟨u, hu⟩ := genericPoints_subset_range_of_isDominant j hη
  let V : Z.Opens := GlobalTheory.IsNormalScheme.component
    ⟨_, irreducibleComponent_mem_irreducibleComponents (g (genericPoint W))⟩
  have hVc : IsClosed (V : Set Z) := GlobalTheory.IsNormalScheme.isClosed_component _
  have : IsIntegral V.toScheme := GlobalTheory.IsNormalScheme.isIntegral_component _
  have hr : Set.range g ⊆ Set.range V.ι := by
    rintro _ ⟨w, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact (((genericPoint_spec W).specializes (Set.mem_univ w)).map g.continuous).mem_closed hVc
      mem_irreducibleComponent
  let g' : W ⟶ V.toScheme := IsOpenImmersion.lift V.ι g hr
  have hg' : g' ≫ V.ι = g := IsOpenImmersion.lift_fac _ _ _
  have : IsFinite (g' ≫ V.ι) := hg' ▸ inferInstance
  have : IsFinite g' := IsFinite.of_comp g' V.ι
  have hlift : j ≫ g' = IsOpenImmersion.lift V.ι (j ≫ g) (by
      rintro _ ⟨w, rfl⟩
      exact hr ⟨j w, rfl⟩) :=
    IsOpenImmersion.lift_uniq _ _ _ _ (by rw [Category.assoc, hg'])
  have hs : SurjectiveOnStalks ((j ≫ g') ≫ V.ι) := by rw [Category.assoc, hg']; infer_instance
  have : Flat (j ≫ g') := by
    rw [hlift]
    exact MorphismProperty.of_isPullback (P := @Flat)
      (IsOpenImmersion.isPullback_lift_id (j ≫ g) V.ι _).flip ‹Flat (j ≫ g)›
  have : SurjectiveOnStalks (j ≫ g') := SurjectiveOnStalks.of_comp _ V.ι
  have : IsDominant g' := by
    obtain ⟨u', hu', hu''⟩ := Flat.generalizingMap (j ≫ g')
      ((genericPoint_spec V.toScheme).specializes (Set.mem_univ ((j ≫ g') u)))
    refine ⟨?_⟩
    refine Dense.mono (s₁ := {genericPoint V.toScheme}) ?_ ?_
    · rintro _ rfl
      exact ⟨j u', hu''⟩
    · exact dense_iff_closure_eq.mpr (genericPoint_spec V.toScheme)
  have : IsIso (g'.stalkMap (genericPoint W)) := by
    rw [← hu]
    have h := isIso_stalkMap_of_flat_of_surjectiveOnStalks (j ≫ g') u
    have := isIso_stalkMap_of_flat_of_surjectiveOnStalks j u
    rw [Scheme.Hom.stalkMap_comp] at h
    exact @IsIso.of_isIso_comp_right _ _ _ _ _ (g'.stalkMap (j u)) (j.stalkMap u) _ h
  have := isIso_of_isIntegralHom_of_isIso_stalkMap g' (fun y => inferInstance)
  rw [← hg']
  infer_instance

theorem etale_and_surjective_of_densePart_mono_finiteEtale : ∀ (S S₀ Y Y₀ Z : Scheme.{0}) [IsLocallyNoetherian S] [IsLocallyNoetherian Y] (j : S₀ ⟶ S) (j' : Y₀ ⟶ Y) (e : Y ⟶ S) (e₀ : Y₀ ⟶ S₀) (p : Z ⟶ S) (i : Y₀ ⟶ Z), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme S → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Y → IsPreimmersion j → Flat j → IsDominant j → QuasiCompact j → IsPreimmersion j' → Flat j' → IsDominant j' → QuasiCompact j' → IsFinite e → j' ≫ e = e₀ ≫ j → IsFinite p → Etale p → i ≫ p = e₀ ≫ j → Surjective e₀ → Etale e₀ → Mono i → Etale e ∧ Surjective e := by
  intro S S₀ Y Y₀ Z _ _ j j' e e₀ p i hS hY _ _ _ _ _ _ _ _ _ hj _ _ hi _ _ _
  have hYn := GlobalTheory.IsNormalScheme.of_pred hY
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian p
  have : GlobalTheory.IsNormalScheme Z := (isNormalScheme_iff Z).mpr
    (forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth p
      ((isNormalScheme_iff S).mp (GlobalTheory.IsNormalScheme.of_pred hS)))
  obtain ⟨g, ⟨hg₁, hg₂⟩, -⟩ := existsUnique_lift_of_densePart Y Y₀ S Z j' hY ‹_› ‹_› ‹_› ‹_› p e i
    inferInstance (hi.trans hj.symm)
  have : IsFinite (g ≫ p) := hg₂ ▸ inferInstance
  have : IsFinite g := IsFinite.of_comp g p
  let k : Y₀ ⟶ pullback p j := pullback.lift i e₀ hi
  have hk₁ : k ≫ pullback.fst p j = i := pullback.lift_fst _ _ _
  have hk₂ : k ≫ pullback.snd p j = e₀ := pullback.lift_snd _ _ _
  have : Etale (k ≫ pullback.snd p j) := hk₂ ▸ inferInstance
  have : Etale k := Etale.of_comp k (pullback.snd p j)
  have : Mono (k ≫ pullback.fst p j) := hk₁ ▸ inferInstance
  have : Mono k := mono_of_mono k (pullback.fst p j)
  have : IsOpenImmersion k := IsOpenImmersion.of_flat_of_mono k
  have : Flat i := hk₁ ▸ inferInstance
  have : SurjectiveOnStalks i := hk₁ ▸ inferInstance
  constructor
  · have : IsZariskiLocalAtSource @Etale := HasRingHomProperty.instIsZariskiLocalAtSource
    rw [IsZariskiLocalAtSource.iff_of_iSup_eq_top (P := @Etale) _
      (GlobalTheory.IsNormalScheme.iSup_component Y)]
    intro W
    have : IsDominant (j' ∣_ GlobalTheory.IsNormalScheme.component W) :=
      IsZariskiLocalAtTarget.restrict (P := @IsDominant) ‹IsDominant j'› _
    have h : j' ∣_ GlobalTheory.IsNormalScheme.component W ≫ (GlobalTheory.IsNormalScheme.component W).ι ≫ g =
        (j' ⁻¹ᵁ GlobalTheory.IsNormalScheme.component W).ι ≫ i := by
      rw [morphismRestrict_ι_assoc, hg₁]
    have : Flat (j' ∣_ GlobalTheory.IsNormalScheme.component W ≫
        (GlobalTheory.IsNormalScheme.component W).ι ≫ g) := h ▸ inferInstance
    have : SurjectiveOnStalks (j' ∣_ GlobalTheory.IsNormalScheme.component W ≫
        (GlobalTheory.IsNormalScheme.component W).ι ≫ g) := h ▸ inferInstance
    have := isOpenImmersion_of_isFinite_of_densePart (j' ∣_ GlobalTheory.IsNormalScheme.component W)
      ((GlobalTheory.IsNormalScheme.component W).ι ≫ g)
    rw [← hg₂, ← Category.assoc]
    infer_instance
  · have : IsDominant (j' ≫ e) := hj ▸ inferInstance
    have : IsDominant e := IsDominant.of_comp j' e
    refine ⟨?_⟩
    rw [← Set.range_eq_univ, ← e.isClosedMap.isClosed_range.closure_eq]
    exact e.denseRange.closure_range

end GlobalTheory
