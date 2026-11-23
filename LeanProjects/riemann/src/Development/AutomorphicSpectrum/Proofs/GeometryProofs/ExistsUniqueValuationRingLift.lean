import Mathlib

open AlgebraicGeometry CategoryTheory Limits

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem existsUnique_valuationRing_lift : ∀ (O V C : Type) [CommRing O] [CommRing V] [IsDomain V] [ValuationRing V] [Field C] [Algebra V C] [IsFractionRing V C] (b : O →+* V) (Z : Scheme.{0}) (s : Z ⟶ Spec (CommRingCat.of O)) [IsProper s] (y : Spec (CommRingCat.of C) ⟶ Z), y ≫ s = Spec.map (CommRingCat.ofHom ((algebraMap V C).comp b)) → ∃! y' : Spec (CommRingCat.of V) ⟶ Z, Spec.map (CommRingCat.ofHom (algebraMap V C)) ≫ y' = y ∧ y' ≫ s = Spec.map (CommRingCat.ofHom b) := by
  intro O V C _ _ _ _ _ _ _ b Z s hs y hy
  have hv : ValuativeCriterion s := by
    have h : (@IsProper : MorphismProperty Scheme.{0}) s := hs
    rw [IsProper.eq_valuativeCriterion] at h
    exact h.1.1.1
  have hc : CommSq y (Spec.map (CommRingCat.ofHom (algebraMap V C))) s
      (Spec.map (CommRingCat.ofHom b)) := ⟨by
    rw [hy, ← Spec.map_comp]; rfl⟩
  let S : ValuativeCommSq s :=
    { R := V, K := C, i₁ := y, i₂ := Spec.map (CommRingCat.ofHom b), commSq := hc }
  obtain ⟨u⟩ := hv S
  refine ⟨u.default.l, ⟨u.default.fac_left, u.default.fac_right⟩, ?_⟩
  rintro y' ⟨h1, h2⟩
  have := u.uniq ⟨y', h1, h2⟩
  exact congrArg CommSq.LiftStruct.l this

end GlobalTheory.CompanionTheory.Ar.Flat
