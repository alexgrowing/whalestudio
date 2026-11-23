import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocRatio
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GrGenOfIsFlagVBOn
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.RootHt GroundTheory.Heights₂.Heights

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.RootHt.PullCoords

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {L L' : Type} [Field L] [Field L']

theorem centre_field (ψ : L →+* L') (z : Sp L ⟶ X) : centre (spMap ψ ≫ z) = centre z := by
  show z (Spec.map (CommRingCat.ofHom ψ) (IsLocalRing.closedPoint L')) = z (IsLocalRing.closedPoint L)
  exact congrArg z (Subsingleton.elim _ _)

theorem centre_specializes (ψ : L →+* L') (z : Sp L ⟶ X) : centre (spMap ψ ≫ z) ⤳ centre z :=
  specializes_of_eq (centre_field ψ z)

set_option backward.isDefEq.respectTransparency false in

theorem stalk_comp (ψ : L →+* L') (z : Sp L ⟶ X) :
    X.presheaf.stalkSpecializes (centre_specializes ψ z) ≫ Scheme.stalkClosedPointTo (spMap ψ ≫ z) =
      Scheme.stalkClosedPointTo z ≫ CommRingCat.ofHom ψ := by
  apply Spec.map_injective
  rw [← cancel_mono (X.fromSpecStalk (centre z)), Spec.map_comp, Spec.map_comp, Category.assoc, Category.assoc,
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
  exact (Scheme.Spec_stalkClosedPointTo_fromSpecStalk _).trans
    (congrArg (spMap ψ ≫ ·) (Scheme.Spec_stalkClosedPointTo_fromSpecStalk z).symm)

theorem valAt_field {ξ : Sp Ω ⟶ X} (ψ : L →+* L') {z : Sp L ⟶ X} {a : Ω} {r : L}
    (h : ValAt ξ z a r) : ValAt ξ (spMap ψ ≫ z) a (ψ r) := by
  obtain ⟨h1, s, rfl, rfl⟩ := h
  have h' : genPt ξ ⤳ centre (spMap ψ ≫ z) := by rw [centre_field]; exact h1
  refine ⟨h', (X.presheaf.stalkSpecializes (centre_specializes ψ z)).hom s, ?_, ?_⟩
  · have e := TopCat.Presheaf.stalkSpecializes_comp X.presheaf h' (centre_specializes ψ z)
    have e2 := congrArg (fun q => (q ≫ Scheme.stalkClosedPointTo ξ).hom s) e
    exact e2
  · exact congrArg (fun q => q.hom s) (stalk_comp ψ z)

theorem coordsAt_field {ξ : Sp Ω ⟶ X} {K : Type} {J : K → Type} {y : (Σ k, J k) → Ω} (ψ : L →+* L')
    {z : Sp L ⟶ X} {w : (Σ k, J k) → L} (h : CoordsAt ξ y z w) :
    CoordsAt ξ y (spMap ψ ≫ z) fun p => ψ (w p) := by
  refine ⟨fun k => (h.1 k).imp fun c hc => hc.map ψ, fun k c hc => ?_⟩
  have hc' : IsUnit (w ⟨k, c⟩) := by
    rw [isUnit_iff_ne_zero] at hc ⊢
    exact fun h0 => hc (by simp [h0])
  refine ⟨(h.2 k c hc').1, fun i => ?_⟩
  obtain ⟨r, hr, e⟩ := (h.2 k c hc').2 i
  exact ⟨ψ r, valAt_field ψ hr, by simp only [e, map_mul]⟩

theorem coordsAt_embedding : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (K : Type) (J : K → Type)
    (y : (Σ k, J k) → Ω) (L : Type) [Field L] [NumberField L] (w : (Σ k, J k) → L) (z : Sp (𝓞 L) ⟶ X) (σ : L →+* ℂ),
    CoordsAt ξ y (spMap (algebraMap (𝓞 L) L) ≫ z) w →
    CoordsAt ξ y (spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ z) (fun p => σ (w p)) := by
  intro X Ω _ ξ K J y L _ _ w z σ h
  have e : spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ z = spMap σ ≫ spMap (algebraMap (𝓞 L) L) ≫ z := by
    rw [← Category.assoc, ← Spec.map_comp]
    rfl
  rw [e]
  exact coordsAt_field σ h

end GlobalTheory.CompanionTheory.Ar.RootHt.PullCoords
