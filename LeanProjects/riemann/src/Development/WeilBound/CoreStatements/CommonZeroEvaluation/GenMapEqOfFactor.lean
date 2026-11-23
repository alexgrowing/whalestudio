import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieLatticeEvalFractionField

open AlgebraicGeometry CategoryTheory
open GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace ModelDimension

theorem genMap_eq_of_factor {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    {R : Type} [CommRing R] [IsLocalRing R] (φ : R →+* Ω) (z : Spec (CommRingCat.of R) ⟶ X)
    (hz : Spec.map (CommRingCat.ofHom φ) ≫ z = ξ) (hc : genPt ξ ⤳ centre z) :
    genMap ξ ⟨centre z, hc⟩ = φ.comp (Scheme.stalkClosedPointTo z).hom := by
  subst hz
  have hs : (Spec.map (CommRingCat.ofHom φ)) (IsLocalRing.closedPoint Ω) ⤳ IsLocalRing.closedPoint R :=
    IsLocalRing.specializes_closedPoint _
  have key : (Spec (CommRingCat.of R)).presheaf.stalkSpecializes hs ≫
      Scheme.stalkClosedPointTo (Spec.map (CommRingCat.ofHom φ)) =
      (stalkClosedPointIso (CommRingCat.of R)).hom ≫ CommRingCat.ofHom φ := by
    refine TopCat.Presheaf.stalk_hom_ext _ fun U hU ↦ ?_
    obtain rfl : U = ⊤ := IsLocalRing.closed_point_mem_iff.mp hU
    erw [TopCat.Presheaf.germ_stalkSpecializes_assoc, Scheme.germ_stalkClosedPointTo_Spec,
      germ_stalkClosedPointIso_hom_assoc]
  change (X.presheaf.stalkSpecializes (z.base.hom.map_specializes hs) ≫
      Scheme.stalkClosedPointTo (Spec.map (CommRingCat.ofHom φ) ≫ z)).hom = _
  erw [Scheme.stalkClosedPointTo_comp, Scheme.Hom.stalkSpecializes_stalkMap_assoc, key,
    ← Category.assoc]
  · rfl
  · exact hs

theorem genMap_germ' {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} (V : X.Opens)
    (hgV : genPt ξ ∈ V) (f : Γ(X, V)) (p : Cpt ξ) (hp : p.1 ∈ V) :
    genMap ξ p (X.presheaf.germ V p.1 hp f) =
      (X.presheaf.germ V (genPt ξ) hgV ≫ Scheme.stalkClosedPointTo ξ).hom f := by
  change (X.presheaf.germ V p.1 hp ≫ X.presheaf.stalkSpecializes p.2 ≫
      Scheme.stalkClosedPointTo ξ).hom f = _
  erw [TopCat.Presheaf.germ_stalkSpecializes_assoc]

end ModelDimension
