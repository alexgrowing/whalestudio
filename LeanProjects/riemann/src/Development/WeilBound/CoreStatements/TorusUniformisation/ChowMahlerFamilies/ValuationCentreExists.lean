import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LevelSectionsExactKernelLocusOpen
open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

theorem PositivityTheory.Xgn.valuation_centre_exists : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (O : Type) [CommRing O] [IsDomain O] [Algebra O Ω] (s : X ⟶ Spec (CommRingCat.of O)) [IsProper s], ξ ≫ s = Spec.map (CommRingCat.ofHom (algebraMap O Ω)) → ∀ V : ValuationSubring Ω, (∀ o : O, algebraMap O Ω o ∈ V) → ∃ p : Cpt ξ, regAt ξ p ≤ V.toSubring ∧ ∀ a ∈ regAt ξ p, a ≠ 0 → a⁻¹ ∈ V → ∃ g : X.presheaf.stalk p.1, IsUnit g ∧ genMap ξ p g = a := by
  intro X Ω _ ξ O _ _ _ s _ hξ V hV
  let φ : O →+* V := (algebraMap O Ω).codRestrict V hV
  have hcomp : CommRingCat.ofHom (algebraMap O Ω) =
      CommRingCat.ofHom φ ≫ CommRingCat.ofHom (algebraMap V Ω) := by
    ext x
    rfl
  have hsq : ξ ≫ s = Spec.map (CommRingCat.ofHom (algebraMap V Ω)) ≫ Spec.map (CommRingCat.ofHom φ) := by
    rw [hξ, hcomp, Spec.map_comp]
  have hE : ValuativeCriterion.Existence s := by
    have h : (ValuativeCriterion.Existence ⊓ @QuasiCompact) s := by
      rw [← UniversallyClosed.eq_valuativeCriterion]
      infer_instance
    exact h.1
  obtain ⟨l, hl⟩ : ∃ l : Spec (CommRingCat.of V) ⟶ X,
      Spec.map (CommRingCat.ofHom (algebraMap V Ω)) ≫ l = ξ := by
    obtain ⟨⟨l, hl, -⟩⟩ := (hE ⟨↥V, Ω, ξ, Spec.map (CommRingCat.ofHom φ), ⟨hsq⟩⟩).exists_lift
    exact ⟨l, hl⟩
  subst hl
  have hspec : (Spec.map (CommRingCat.ofHom (algebraMap V Ω)) ≫ l)
      (IsLocalRing.closedPoint (CommRingCat.of Ω)) ⤳ l (IsLocalRing.closedPoint (CommRingCat.of V)) :=
    (IsLocalRing.specializes_closedPoint
      ((Spec.map (CommRingCat.ofHom (algebraMap V Ω))) (IsLocalRing.closedPoint (CommRingCat.of Ω)))).map
        l.continuous
  have h : TopCat.Presheaf.stalkSpecializes X.presheaf hspec ≫
        Scheme.stalkClosedPointTo (Spec.map (CommRingCat.ofHom (algebraMap V Ω)) ≫ l) =
      Scheme.stalkClosedPointTo l ≫ CommRingCat.ofHom (algebraMap V Ω) := by
    apply Spec.map_injective
    rw [← cancel_mono (X.fromSpecStalk (l (IsLocalRing.closedPoint (CommRingCat.of V))))]
    rw [Spec.map_comp, Spec.map_comp, Category.assoc, Category.assoc,
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk, Scheme.Spec_stalkClosedPointTo_fromSpecStalk,
      Scheme.Spec_stalkClosedPointTo_fromSpecStalk]
  have key : ∀ g, GlobalTheory.CompanionTheory.Ar.genMap (Spec.map (CommRingCat.ofHom (algebraMap V Ω)) ≫ l)
      ⟨l (IsLocalRing.closedPoint (CommRingCat.of V)), hspec⟩ g =
        ((Scheme.stalkClosedPointTo l).hom g : Ω) := by
    intro g
    exact congrArg (fun ψ => ψ.hom g) h
  refine ⟨⟨l (IsLocalRing.closedPoint (CommRingCat.of V)), hspec⟩, ?_, ?_⟩
  · intro a ha
    obtain ⟨g, rfl⟩ := RingHom.mem_range.mp ha
    rw [key g]
    exact ((Scheme.stalkClosedPointTo l).hom g).2
  · intro a ha ha0 hinv
    obtain ⟨g, rfl⟩ := RingHom.mem_range.mp ha
    refine ⟨g, ?_, rfl⟩
    have hloc := Scheme.isLocalHom_stalkClosedPointTo' l
    apply (isUnit_map_iff (Scheme.stalkClosedPointTo l).hom g).mp
    rw [key g] at ha0 hinv
    refine IsUnit.of_mul_eq_one (⟨_, hinv⟩ : V) ?_
    apply Subtype.ext
    exact mul_inv_cancel₀ ha0
