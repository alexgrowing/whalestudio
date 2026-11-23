import Mathlib
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoNormalizationPullbackOfToIntegralClosure
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueLiftSpecOfIsLocalizationAway
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FormallyUnramifiedOfCompOfEtaleOfSurjective
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocalC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AgreeOfCore
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DataRigidTorsionOfDataRigid
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GenericExt

universe u

theorem flat_fromSpecStalk (X : Scheme.{u}) (x : X) : Flat (X.fromSpecStalk x) := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  rw [← hU.fromSpecStalk_eq_fromSpecStalk hxU]
  change Flat (Spec.map (X.presheaf.germ U x hxU) ≫ hU.fromSpec)
  have : Flat (Spec.map (X.presheaf.germ U x hxU)) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    let := X.presheaf.algebra_section_stalk (⟨x, hxU⟩ : U)
    have := hU.isLocalization_stalk ⟨x, hxU⟩
    exact IsLocalization.flat (X.presheaf.stalk x) (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl
  have h₂ : IsOpenImmersion (IsAffineOpen.fromSpec hU) := IsAffineOpen.isOpenImmersion_fromSpec hU
  have h₃ : Flat (IsAffineOpen.fromSpec hU) := inferInstance
  exact MorphismProperty.comp_mem @Flat _ _ this h₃

theorem exists_hom_specStalk {W Y T X : Scheme.{u}} (j : W ⟶ Y) [IsSchemeTheoreticallyDominant j]
    [QuasiCompact j] [X.IsSeparated] (F : W ⟶ X) (g' : T ⟶ Y) [Flat g'] (g : T ⟶ X)
    (H : ∀ (Z : Scheme.{u}) (ρ : Z ⟶ T) (r : Z ⟶ W), r ≫ j = ρ ≫ g' → r ≫ F = ρ ≫ g) (p : T) :
    ∃ φ : Spec (Y.presheaf.stalk (g' p)) ⟶ X, ∀ (Z : Scheme.{u})
      (ρ : Z ⟶ Spec (Y.presheaf.stalk (g' p))) (r : Z ⟶ W),
      r ≫ j = ρ ≫ Y.fromSpecStalk (g' p) → r ≫ F = ρ ≫ φ := by
  let h := Spec.map (g'.stalkMap p)
  obtain ⟨h₁, h₂⟩ : Flat h ∧ Surjective h :=
    (flat_and_surjective_SpecMap_iff _).2 (faithfullyFlat_stalkMap_of_flat g' p)
  have hh : h ≫ Y.fromSpecStalk (g' p) = T.fromSpecStalk p ≫ g' :=
    Scheme.SpecMap_stalkMap_fromSpecStalk g'
  have := flat_fromSpecStalk Y (g' p)
  have key : pullback.fst h h ≫ T.fromSpecStalk p ≫ g = pullback.snd h h ≫ T.fromSpecStalk p ≫ g := by
    let q := pullback.fst h h ≫ h ≫ Y.fromSpecStalk (g' p)
    have hq : Flat q := inferInstance
    refine hom_ext_of_isSchemeTheoreticallyDominant (pullback.fst q j) (terminal.from X) ?_
      (terminal.hom_ext _ _)
    have e₁ := H _ (pullback.fst q j ≫ pullback.fst h h ≫ T.fromSpecStalk p) (pullback.snd q j) (by
      rw [← pullback.condition]; simp only [q, Category.assoc, hh])
    have e₂ := H _ (pullback.fst q j ≫ pullback.snd h h ≫ T.fromSpecStalk p) (pullback.snd q j) (by
      rw [← pullback.condition]
      simp only [q, Category.assoc, ← hh, pullback.condition_assoc])
    simpa only [Category.assoc] using e₁.symm.trans e₂
  let φ := EffectiveEpi.desc h (T.fromSpecStalk p ≫ g) (fun a b hab => by
    have := congrArg (pullback.lift a b hab ≫ ·) key
    simpa only [pullback.lift_fst_assoc, pullback.lift_snd_assoc] using this)
  have hφ : h ≫ φ = T.fromSpecStalk p ≫ g := EffectiveEpi.fac _ _ _
  refine ⟨φ, fun Z ρ r hr => ?_⟩
  rw [← cancel_epi (pullback.fst ρ h), pullback.condition_assoc, hφ]
  have := H _ (pullback.snd ρ h ≫ T.fromSpecStalk p) (pullback.fst ρ h ≫ r) (by
    rw [Category.assoc, hr, pullback.condition_assoc, hh, Category.assoc])
  simpa only [Category.assoc] using this

theorem exists_extension {W Y X S : Scheme.{u}} (j : W ⟶ Y) [IsOpenImmersion j] [IsDominant j]
    [QuasiCompact j] [IsIntegral Y] [S.IsSeparated] (sY : Y ⟶ S) (sX : X ⟶ S) [IsSeparated sX]
    [LocallyOfFiniteType sX] (F : W ⟶ X) (hF : F ≫ sX = j ≫ sY)
    (H : ∀ y : Y, y ∉ Set.range j → ∃ (T : Scheme.{u}) (g' : T ⟶ Y) (g : T ⟶ X), Flat g' ∧ y ∈ Set.range g' ∧
      ∀ (Z : Scheme.{u}) (ρ : Z ⟶ T) (r : Z ⟶ W), r ≫ j = ρ ≫ g' → r ≫ F = ρ ≫ g) :
    ∃ ψ : Y ⟶ X, j ≫ ψ = F ∧ ψ ≫ sX = sY := by
  have hX : X.IsSeparated := ⟨by rw [← terminal.comp_from sX]; infer_instance⟩
  have : IsSchemeTheoreticallyDominant j := .of_isDominant j
  let e₀ := Y.fromSpecStalk (genericPoint Y)
  have : IsDominant e₀ := isDominant_fromSpecStalk_genericPoint Y
  have hr : Set.range e₀ ⊆ Set.range j := by
    rw [Scheme.range_fromSpecStalk]
    intro z hz
    have hg : genericPoint Y ∈ Set.range j :=
      (genericPoint_spec Y).mem_open_set_iff j.isOpenEmbedding.isOpen_range |>.2
        (by simpa [Set.range_nonempty_iff_nonempty] using j.denseRange.nonempty)
    exact Specializes.mem_open hz j.isOpenEmbedding.isOpen_range hg
  let e := IsOpenImmersion.lift j e₀ hr
  have he : e ≫ j = e₀ := IsOpenImmersion.lift_fac _ _ _
  have loc : ∀ y : Y, ∃ (U : Scheme.{u}) (k : U ⟶ Y) (_ : IsOpenImmersion k) (ψ : U ⟶ X)
      (l : Spec (Y.presheaf.stalk (genericPoint Y)) ⟶ U),
      y ∈ Set.range k ∧ l ≫ k = e₀ ∧ l ≫ ψ = e ≫ F := by
    intro y
    by_cases hy : y ∈ Set.range j
    · exact ⟨W, j, inferInstance, F, e, hy, he, rfl⟩
    obtain ⟨T, g', g, hg', ⟨p, rfl⟩, hT⟩ := H y hy
    obtain ⟨φ, hφ⟩ := exists_hom_specStalk j F g' g hT p
    have := flat_fromSpecStalk Y (g' p)
    have hover : φ ≫ sX = Y.fromSpecStalk (g' p) ≫ sY := by
      refine hom_ext_of_isSchemeTheoreticallyDominant (pullback.fst (Y.fromSpecStalk (g' p)) j)
        (terminal.from S) ?_ (terminal.hom_ext _ _)
      rw [← reassoc_of% (hφ _ _ _ pullback.condition.symm), hF, pullback.condition_assoc]
    obtain ⟨U, hU, ψ, h₁, -⟩ := spread_out_of_isGermInjective' sY sX φ hover
    let m := Spec.map (Y.presheaf.stalkSpecializes (genericPoint_specializes (g' p)))
    have hm : m ≫ Y.fromSpecStalk (g' p) = e₀ := Scheme.SpecMap_stalkSpecializes_fromSpecStalk _
    refine ⟨U, U.ι, inferInstance, ψ, m ≫ U.fromSpecStalkOfMem _ hU, ⟨⟨_, hU⟩, rfl⟩, ?_, ?_⟩
    · rw [Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι, hm]
    · rw [Category.assoc, ← h₁]
      exact (hφ _ m e (he.trans hm.symm)).symm
  choose U k hk ψ l hy hl hψ using loc
  let 𝒰 : Y.OpenCover := Scheme.Cover.mkOfCovers Y U k (fun y => ⟨y, hy y⟩) hk
  have hc : ∀ a b : Y, pullback.fst (k a) (k b) ≫ ψ a = pullback.snd (k a) (k b) ≫ ψ b := by
    intro a b
    let m := pullback.lift (l a) (l b) ((hl a).trans (hl b).symm)
    have : IsReduced (pullback (k a) (k b)) := isReduced_of_isOpenImmersion (pullback.fst _ _ ≫ k a)
    have : IsDominant (m ≫ pullback.fst _ _ ≫ k a) := by
      rw [pullback.lift_fst_assoc, hl]
      infer_instance
    have : IsDominant m := .of_comp_of_isOpenImmersion m (pullback.fst _ _ ≫ k a)
    refine ext_of_isDominant m ?_
    rw [pullback.lift_fst_assoc, pullback.lift_snd_assoc, hψ, hψ]
  have hι : ∀ a : Y, k a ≫ 𝒰.glueMorphisms ψ hc = ψ a := fun a => 𝒰.ι_glueMorphisms ψ hc a
  have h1 : j ≫ 𝒰.glueMorphisms ψ hc = F := by
    have : IsReduced W := isReduced_of_isOpenImmersion j
    have : IsDominant (e ≫ j) := by rw [he]; infer_instance
    have : IsDominant e := .of_comp_of_isOpenImmersion e j
    refine ext_of_isDominant e ?_
    rw [reassoc_of% he, ← hl (genericPoint Y), Category.assoc, hι, hψ]
  refine ⟨_, h1, ext_of_isDominant j ?_⟩
  rw [reassoc_of% h1, hF]

theorem isOpenImmersion_jK (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] :
    IsOpenImmersion (jK R) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have : IsLocalization.Away ϖ (FractionRing R) := by
    refine (IsLocalization.iff_of_le_of_exists_dvd (Submonoid.powers ϖ)
      (nonZeroDivisors R) (powers_le_nonZeroDivisors_of_noZeroDivisors hϖ.ne_zero)
      fun a ha => ?_).2 inferInstance
    obtain ⟨n, hn⟩ := IsDiscreteValuationRing.associated_pow_irreducible (nonZeroDivisors.ne_zero ha) hϖ
    exact ⟨ϖ ^ n, ⟨n, rfl⟩, hn.dvd⟩
  exact IsOpenImmersion.of_isLocalization ϖ

theorem eq_closedPoint_of_not_mem_range (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (s : Spec (CommRingCat.of R)) (hs : s ∉ Set.range (jK R)) : s = IsLocalRing.closedPoint R := by
  by_cases h : s.asIdeal = ⊥
  · refine (hs ⟨⟨⊥, Ideal.isPrime_bot⟩, PrimeSpectrum.ext ?_⟩).elim
    rw [h]
    exact Ideal.comap_bot_of_injective (algebraMap R (FractionRing R)) (IsFractionRing.injective R _)
  · exact PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal (s.isPrime.isMaximal h))

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (X' X : Over (Spec (CommRingCat.of R))) [Flat X'.hom] [IsIntegral X'.left] [IsSeparated X.hom] [LocallyOfFiniteType X.hom] (f : (Over.pullback (jK R)).obj X' ⟶ (Over.pullback (jK R)).obj X), (∀ x : X'.left, X'.hom x = IsLocalRing.closedPoint R → ∃ (T : Scheme.{0}) (g' : T ⟶ X'.left) (g : T ⟶ X.left), Flat g' ∧ x ∈ Set.range g' ∧ ∀ (Z : Scheme.{0}) (ρ : Z ⟶ T) (r : Z ⟶ ((Over.pullback (jK R)).obj X').left), r ≫ pullback.fst X'.hom (jK R) = ρ ≫ g' → r ≫ f.left ≫ pullback.fst X.hom (jK R) = ρ ≫ g) → ∃ ψ : X' ⟶ X, (Over.pullback (jK R)).map ψ = f := by
  intro R _ _ _ X' X _ _ _ _ f H
  have := isOpenImmersion_jK R
  have : IsDominant (jK R) := DVR.isDominant_jK
  have := IsSchemeTheoreticallyDominant.of_isDominant (jK R)
  have : IsDominant (pullback.fst X'.hom (jK R)) := inferInstance
  have hf : f.left ≫ pullback.snd X.hom (jK R) = pullback.snd X'.hom (jK R) := Over.w f
  obtain ⟨ψ, h₁, h₂⟩ := exists_extension (pullback.fst X'.hom (jK R)) X'.hom X.hom
    (f.left ≫ pullback.fst X.hom (jK R))
    (by rw [Category.assoc, pullback.condition, pullback.condition, ← Category.assoc]; congr 1)
    (fun y hy => H y (eq_closedPoint_of_not_mem_range R _ fun h => hy (by
      rw [Scheme.Pullback.range_fst]; exact h)))
  refine ⟨Over.homMk ψ h₂, Over.OverMorphism.ext (pullback.hom_ext ?_ ?_)⟩
  · exact (pullback.lift_fst _ _ _).trans h₁
  · exact (Over.w _).trans hf.symm

end GlobalTheory.GenericExt
