import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CentreAtOfIsAt
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLogMult
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocModelLocRingAndExistsTrBasis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecializesOfPointLocalRingLeSeparatedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasRationalResidueFieldPointLocalRingClosedPointStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep GlobalTheory.FieldPair

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ResMap

def stalkEquiv {X : Scheme.{0}} [IsIntegral X] (x : X) : X.presheaf.stalk x ≃+* locRing x :=
  RingEquiv.ofBijective (algebraMap (X.presheaf.stalk x) X.functionField).rangeRestrict
    ⟨fun _ _ e => IsFractionRing.injective _ X.functionField (congrArg Subtype.val e),
      RingHom.rangeRestrict_surjective _⟩

theorem residueMap : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ), IsProjOver p → ∀ (z : X) (k : ℕ),
  topologicalKrullDim (closure ({z} : Set X)) = k →
  ∃ (κ : Type) (_ : Field κ) (_ : Algebra ℂ κ) (π₀ : locRing z →+* κ),
    Function.Surjective π₀ ∧ (∀ r : locRing z, π₀ r = 0 ↔ ZeroAt z (r : X.functionField)) ∧
    (∀ a (h : Cartier.constFn p a ∈ locRing z), π₀ ⟨Cartier.constFn p a, h⟩ = algebraMap ℂ κ a) ∧
    (∃ w : Fin k → κ, TrBasis (algebraMap ℂ κ) w) ∧
    ∀ (x : X) (h : locRing x ≤ locRing z), IsLocModel (algebraMap ℂ κ) (π₀.comp (Subring.inclusion h)).range ∧
      (∀ f : κ, ∃ a b : locRing x, π₀ (Subring.inclusion h b) ≠ 0 ∧ f * π₀ (Subring.inclusion h b) = π₀ (Subring.inclusion h a)) ∧
      (IsClosed ({x} : Set X) → RatRes (algebraMap ℂ κ) (π₀.comp (Subring.inclusion h)).range) := by
  intro X _ _ p hp z k hk
  have hprop : IsProper p := by
    obtain ⟨N, j, hj, rfl⟩ := hp
    have := isProper_str ℂ N
    infer_instance
  have hsep : X.IsSeparated := ⟨by rw [← Limits.terminal.comp_from p]; infer_instance⟩
  obtain ⟨Z, i, hi, hZ, rfl⟩ := GlobalTheory.exists_isClosedImmersion_genericPoint z
  let q := i ≫ p
  have hrange : Set.range i = closure ({i (genericPoint Z)} : Set X) := by
    have h₁ := (genericPoint_spec Z).image i.continuous
    rw [Set.image_univ, i.isClosedEmbedding.isClosed_range.closure_eq] at h₁
    exact (isGenericPoint_def.mp h₁).symm
  have hdim : topologicalKrullDim Z = k := by
    rw [← GlobalTheory.topologicalKrullDim_eq_of_isEmbedding i.isClosedEmbedding.isEmbedding hrange]
    exact hk
  obtain ⟨-, w, hw⟩ := isLocModel_locRing_and_exists_trBasis Z q k (genericPoint Z) hdim
  letI alg : Algebra ℂ Z.functionField := (Cartier.constFn q).toAlgebra
  let π₀ : locRing (i (genericPoint Z)) →+* Z.functionField :=
    (i.stalkMap (genericPoint Z)).hom.comp (stalkEquiv (i (genericPoint Z))).symm.toRingHom
  refine ⟨Z.functionField, inferInstance, alg, π₀, ?_, ?_, ?_, ⟨w, hw⟩, ?_⟩
  · exact (i.stalkMap_surjective _).comp (stalkEquiv _).symm.surjective
  · intro r
    obtain ⟨a, rfl⟩ := (stalkEquiv _).surjective r
    have e1 : π₀ (stalkEquiv _ a) = (i.stalkMap (genericPoint Z)).hom a := by
      show (i.stalkMap (genericPoint Z)).hom ((stalkEquiv _).symm (stalkEquiv _ a)) = _
      rw [RingEquiv.symm_apply_apply]
    have e2 : ((stalkEquiv _ a : locRing _) : X.functionField) = algebraMap _ _ a := rfl
    rw [e1, e2]
    constructor
    · intro h0
      refine ⟨a, ?_, rfl⟩
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      have := hu.map (i.stalkMap (genericPoint Z)).hom
      rw [h0] at this
      exact not_isUnit_zero this
    · rintro ⟨b, hb, e⟩
      obtain rfl := IsFractionRing.injective _ X.functionField e
      by_contra hne
      have hu : IsUnit ((i.stalkMap (genericPoint Z)).hom b) := isUnit_iff_ne_zero.2 hne
      exact (IsLocalRing.mem_maximalIdeal _).1 hb ((isUnit_map_iff _ _).1 hu)
  · intro a ha
    have hg := (algebraMap_germ (X := X) (x := i (genericPoint Z)) (U := ⊤) trivial (algX p ⊤ a)).trans
      (RingHom.congr_fun (fnOf_comp_algX p ⊤ (gen_mem (x := i (genericPoint Z)) trivial)) a)
    have hr : (⟨Cartier.constFn p a, ha⟩ : locRing _) =
        stalkEquiv _ (X.presheaf.germ ⊤ _ trivial (algX p ⊤ a)) := Subtype.ext hg.symm
    rw [hr]
    show (i.stalkMap (genericPoint Z)).hom ((stalkEquiv _).symm (stalkEquiv _ _)) = _
    rw [RingEquiv.symm_apply_apply]
    erw [Scheme.Hom.germ_stalkMap_apply i ⊤ (genericPoint Z) trivial (algX p ⊤ a)]
    have hc : (i.app ⊤).hom (algX p ⊤ a) = algX q (i ⁻¹ᵁ ⊤) a := by
      have e : (i ≫ p).appLE ⊤ (i ⁻¹ᵁ ⊤) (le_top.trans (Scheme.Hom.preimage_top _).ge) =
          p.appLE ⊤ ⊤ (le_top.trans (Scheme.Hom.preimage_top _).ge) ≫ i.appLE ⊤ (i ⁻¹ᵁ ⊤) le_rfl := by
        first
          | rw [Scheme.Hom.appLE_comp_appLE]
          | (simp only [Scheme.Hom.comp_appLE, Scheme.Hom.appLE, Category.assoc,
              Scheme.Hom.naturality_assoc]; rfl)
      simp only [algX, q, RingHom.comp_apply]
      rw [Scheme.Hom.app_eq_appLE, e, CommRingCat.comp_apply]
    rw [hc]
    exact RingHom.congr_fun (fnOf_comp_algX q (i ⁻¹ᵁ ⊤) (gen_mem (x := genericPoint Z) trivial)) a
  · intro x h
    have hs : i (genericPoint Z) ⤳ x := GlobalTheory.T.specializes_of_pointLocalRing_le_separated X x _ h
    obtain ⟨y, rfl⟩ : x ∈ Set.range i := by
      rw [hrange]; exact specializes_iff_mem_closure.mp hs
    have key : ∀ a : X.presheaf.stalk (i y),
        π₀ (Subring.inclusion h ⟨algebraMap _ X.functionField a, a, rfl⟩) =
          algebraMap (Z.presheaf.stalk y) Z.functionField ((i.stalkMap y).hom a) := by
      intro a
      have e : (Subring.inclusion h ⟨algebraMap _ X.functionField a, a, rfl⟩ : locRing _) =
          stalkEquiv _ ((X.presheaf.stalkSpecializes hs).hom a) := by
        apply Subtype.ext
        show algebraMap _ X.functionField a =
          algebraMap _ X.functionField ((X.presheaf.stalkSpecializes hs).hom a)
        simp only [RingHom.algebraMap_toAlgebra]
        rw [← CommRingCat.comp_apply, TopCat.Presheaf.stalkSpecializes_comp]
      rw [e]
      show (i.stalkMap (genericPoint Z)).hom ((stalkEquiv _).symm (stalkEquiv _ _)) = _
      rw [RingEquiv.symm_apply_apply]
      exact Scheme.Hom.stalkSpecializes_stalkMap_apply i (genericPoint Z) y
        ((genericPoint_spec Z).specializes trivial) a
    have hR : (π₀.comp (Subring.inclusion h)).range = locRing y := by
      ext f
      constructor
      · rintro ⟨⟨r, a, rfl⟩, rfl⟩
        exact ⟨(i.stalkMap y).hom a, (key a).symm⟩
      · rintro ⟨b, rfl⟩
        obtain ⟨a, rfl⟩ := i.stalkMap_surjective y b
        exact ⟨⟨_, a, rfl⟩, key a⟩
    have hloc : IsLocModel (Cartier.constFn q) (locRing y) := isLocModel_locRing y
    rw [hR]
    refine ⟨hloc, fun f => ?_, fun hx => ?_⟩
    · obtain ⟨a', ha', b', hb', hb0, e⟩ := hloc.frac f
      rw [← hR] at ha' hb'
      obtain ⟨a, rfl⟩ := ha'
      obtain ⟨b, rfl⟩ := hb'
      exact ⟨a, b, hb0, e⟩
    · have hy : IsClosed ({y} : Set Z) := by
        have hpre : (i : Z → X) ⁻¹' {i y} = {y} := by
          ext t
          simp only [Set.mem_preimage, Set.mem_singleton_iff]
          exact i.isClosedEmbedding.injective.eq_iff
        rw [← hpre]
        exact hx.preimage i.continuous
      exact GlobalTheory.T.hasRationalResidueField_pointLocalRing_closedPoint Z q y hy

end GlobalTheory.ResMap
