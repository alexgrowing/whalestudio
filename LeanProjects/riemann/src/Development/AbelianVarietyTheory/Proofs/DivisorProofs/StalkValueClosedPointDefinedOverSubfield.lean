import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SepAtBIff
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep

namespace GlobalTheory.USep

theorem stalkClosedPointTo_comp_stalkMap_spec (X : Scheme.{0}) {R W : Type} [CommRing R] [IsLocalRing R]
    [CommRing W] [IsLocalRing W] (ξ : Sp R ⟶ X) (g : R →+* W)
    (hs : (spMap g ≫ ξ) (closedPoint W) ⤳ ξ (closedPoint R)) (a : X.presheaf.stalk (ξ (closedPoint R))) :
    (Scheme.stalkClosedPointTo (spMap g ≫ ξ)).hom ((X.presheaf.stalkSpecializes hs).hom a) =
      g ((Scheme.stalkClosedPointTo ξ).hom a) := by
  have key : X.presheaf.stalkSpecializes hs ≫ Scheme.stalkClosedPointTo (spMap g ≫ ξ) =
      Scheme.stalkClosedPointTo ξ ≫ CommRingCat.ofHom g := by
    apply Spec.map_injective
    rw [← cancel_mono (X.fromSpecStalk (ξ (closedPoint R))), Spec.map_comp, Category.assoc,
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk, Scheme.Spec_stalkClosedPointTo_fromSpecStalk,
      Spec.map_comp, Category.assoc, Scheme.Spec_stalkClosedPointTo_fromSpecStalk]
  exact congrArg (fun q => q.hom a) key

theorem bijective_stalkSpecializes_of_eq {X : Scheme.{0}} {x y : X} (h : x ⤳ y) (e : x = y) :
    Function.Bijective (X.presheaf.stalkSpecializes h).hom := by
  subst e
  rw [TopCat.Presheaf.stalkSpecializes_refl]
  exact Function.bijective_id

theorem isLocalHom_stalkSpecializes_of_eq {X : Scheme.{0}} {x y : X} (h : x ⤳ y) (e : x = y) :
    IsLocalHom (X.presheaf.stalkSpecializes h).hom := by
  subst e
  rw [TopCat.Presheaf.stalkSpecializes_refl]
  exact ⟨fun a ha => ha⟩

theorem stalkClosedPointTo_mem_subfield_of_definedOver {X : Scheme.{0}} {K : Type} [Field K] (k₀ : Subfield K) (Q : Sp K ⟶ X)
    (hQ : GlobalTheory.UChart.DefOver k₀ Q) (b : X.presheaf.stalk (Q (closedPoint K))) :
    (Scheme.stalkClosedPointTo Q).hom b ∈ k₀ := by
  obtain ⟨P₀, rfl⟩ := hQ
  have e : (spMap k₀.subtype ≫ P₀) (closedPoint K) = P₀ (closedPoint k₀) := by
    change P₀ ((spMap k₀.subtype) (closedPoint K)) = _
    congr 1
    exact Subsingleton.elim _ _
  have hs : (spMap k₀.subtype ≫ P₀) (closedPoint K) ⤳ P₀ (closedPoint k₀) := e ▸ specializes_refl _
  obtain ⟨a, rfl⟩ := (bijective_stalkSpecializes_of_eq hs e).2 b
  rw [stalkClosedPointTo_comp_stalkMap_spec X P₀ k₀.subtype hs a]
  exact SetLike.coe_mem _

theorem stalkVal_closedPoint : ∀ (X : Scheme.{0}) (R : Type) [CommRing R] [IsLocalRing R] (ξ₁ : Sp R ⟶ X) (K : Type) [Field K] (ev₁ : R →+* K) (k₀ : Subfield K), (∀ p, (spMap ev₁ ≫ ξ₁) p = ξ₁ (closedPoint R)) → GlobalTheory.UChart.DefOver k₀ (spMap ev₁ ≫ ξ₁) → ∀ h ∈ (Scheme.stalkClosedPointTo ξ₁).hom.range, ev₁ h ∈ k₀ ∧ (h ∈ maximalIdeal R → ev₁ h = 0) := by
  intro X R _ _ ξ₁ K _ ev₁ k₀ hpt hdef h hh
  obtain ⟨a, rfl⟩ := hh
  have e := hpt (closedPoint K)
  have hs : (spMap ev₁ ≫ ξ₁) (closedPoint K) ⤳ ξ₁ (closedPoint R) := e ▸ specializes_refl _
  have hv := stalkClosedPointTo_comp_stalkMap_spec X ξ₁ ev₁ hs a
  refine ⟨?_, fun hm => ?_⟩
  · rw [← hv]
    exact stalkClosedPointTo_mem_subfield_of_definedOver k₀ _ hdef _
  · by_contra hne
    have hl := isLocalHom_stalkSpecializes_of_eq hs e
    have hu : IsUnit ((Scheme.stalkClosedPointTo (spMap ev₁ ≫ ξ₁)).hom
        ((X.presheaf.stalkSpecializes hs).hom a)) := by
      rw [hv]; exact Ne.isUnit hne
    have ha : IsUnit a := isUnit_of_map_unit _ _ (isUnit_of_map_unit _ _ hu)
    exact (mem_maximalIdeal _).1 hm (ha.map _)

end GlobalTheory.USep
