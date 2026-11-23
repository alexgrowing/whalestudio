import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.RootOnFund

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.GenIso

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

theorem genMap_bijective_of_eq {X : Scheme.{0}} {K : Type} [Field K] (η : Spec (CommRingCat.of K) ⟶ X)
    (hη : IsCptGen η) (y : X) (hy : genPt η ⤳ y) (hyq : y = genPt η) :
    Function.Bijective (genMap η ⟨y, hy⟩) := by
  subst hyq
  have : genMap η ⟨genPt η, hy⟩ = (Scheme.stalkClosedPointTo η).hom := by
    simp [genMap, TopCat.Presheaf.stalkSpecializes_refl]
    rfl
  rw [this]
  exact hη.bij

theorem genMap_comp {X : Scheme.{0}} {K : Type} [Field K] (η : Spec (CommRingCat.of K) ⟶ X) (y : X)
    (hy : genPt η ⤳ y) : spMap (genMap η ⟨y, hy⟩) ≫ X.fromSpecStalk y = η := by
  have hy' : η (IsLocalRing.closedPoint (CommRingCat.of K)) ⤳ y := hy
  change Spec.map (X.presheaf.stalkSpecializes hy' ≫ Scheme.stalkClosedPointTo η) ≫ _ = _
  rw [Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
  exact Scheme.Spec_stalkClosedPointTo_fromSpecStalk η

theorem exists_iso_of_genPt_eq : ∀ (X : Scheme.{0}) (Ω Ω' : Type) [Field Ω] [Field Ω']
    (ξ : Spec (CommRingCat.of Ω) ⟶ X) (ξ' : Spec (CommRingCat.of Ω') ⟶ X),
    IsCptGen ξ → IsCptGen ξ' → genPt ξ = genPt ξ' → ∃ ψ : Ω' ≃+* Ω, spMap ψ.toRingHom ≫ ξ' = ξ := by
  intro X Ω Ω' _ _ ξ ξ' h h' hq
  have hs : genPt ξ ⤳ genPt ξ' := hq ▸ specializes_rfl
  let p : Cpt ξ := ⟨genPt ξ', hs⟩
  let p' : Cpt ξ' := ⟨genPt ξ', specializes_rfl⟩
  let e := RingEquiv.ofBijective (genMap ξ p) (genMap_bijective_of_eq ξ h _ hs hq.symm)
  let e' := RingEquiv.ofBijective (genMap ξ' p') (genMap_bijective_of_eq ξ' h' _ specializes_rfl rfl)
  refine ⟨e'.symm.trans e, ?_⟩
  have c1 : spMap (genMap ξ p) ≫ X.fromSpecStalk (genPt ξ') = ξ := genMap_comp ξ _ hs
  have c2 : spMap (genMap ξ' p') ≫ X.fromSpecStalk (genPt ξ') = ξ' := genMap_comp ξ' _ specializes_rfl
  calc spMap (e'.symm.trans e).toRingHom ≫ ξ'
      = spMap (e'.symm.trans e).toRingHom ≫ (spMap (genMap ξ' p') ≫ X.fromSpecStalk (genPt ξ')) := by
        rw [c2]
    _ = spMap (genMap ξ p) ≫ X.fromSpecStalk (genPt ξ') := by
        rw [← Category.assoc]
        congr 1
        rw [spMap, spMap, spMap, ← Spec.map_comp]
        congr 1
        ext x
        simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply]
        change e (e'.symm (genMap ξ' p' x)) = genMap ξ p x
        rw [show e'.symm (genMap ξ' p' x) = x from e'.symm_apply_apply x]
        rfl
    _ = ξ := c1

end GlobalTheory.CompanionTheory.Ar.GenIso
