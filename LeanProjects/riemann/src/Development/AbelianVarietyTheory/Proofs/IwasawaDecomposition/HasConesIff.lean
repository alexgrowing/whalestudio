import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ToroidalChartsForFan

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

namespace GlobalTheory.GenFan

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l}
  {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

def ConeAt (Cn : ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] (m : ℕ),
      (Fin m → LinearMap.BilinForm ℤ X) → Prop) (Z : Model Xo c β) (z : Z.X) : Prop :=
  ∃ (R : Type) (_ : CommRing R) (_ : IsDomain R) (_ : IsLocalRing R) (ξ : Sp R ⟶ Z.X) (t : SAB H (Sp R))
    (_ : SABMap t Z.t ξ) (P : PELUnif (maximalIdeal R) t) (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X),
    IsCN R ∧ ξ (closedPoint R) = z ∧ IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom ∧
    ((residue R).comp (Scheme.stalkClosedPointTo ξ).hom).FormallyUnramified ∧ P.TorsionIso ∧
    Cn P.D.toPre.X m γ ∧ InCone P.D.toPre γ

theorem hasCones_iff (Cn : ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] (m : ℕ),
      (Fin m → LinearMap.BilinForm ℤ X) → Prop) (Z : Model Xo c β) : HasCones Cn Z ↔ ∀ z, ConeAt Cn Z z :=
  Iff.rfl

theorem exists_of_id (Y : Model Xo c (RingHom.id c.F)) (z : Y.X) :
    (∃ x ∈ genBd Y, genι Y x = z) ∨ z ∈ Set.range Y.j := by
  have : IsIso (spMap (RingHom.id c.F)) := by
    show IsIso (Spec.map (CommRingCat.ofHom (RingHom.id c.F)))
    rw [show CommRingCat.ofHom (RingHom.id c.F) = 𝟙 (CommRingCat.of c.F) from rfl, Spec.map_id]
    infer_instance
  have : IsIso (genι Y) := inferInstance
  set x := inv (genι Y) z with hx
  have hz : genι Y x = z := by rw [hx, ← Scheme.Hom.comp_apply, IsIso.inv_hom_id]; rfl
  by_cases h : x ∈ genBd Y
  · exact Or.inl ⟨x, h, hz⟩
  · obtain ⟨w, hw⟩ := not_not.1 h
    exact Or.inr ⟨w, by rw [← hz, ← hw]; rfl⟩

end GlobalTheory.GenFan
