import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InRealConeSelf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PhiDivisorArcBlowup
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMonomialLevelFormDvr
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

theorem GlobalTheory.fromSpecStalk_comp_eq_spMap_germ (T : Scheme.{0}) (R : Type) [CommRing R] (h : T ⟶ Sp R) (v : T) :
    T.fromSpecStalk v ≫ h = spMap ((T.presheaf.germ ⊤ v trivial).hom.comp
      (h.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)) := by
  have e : CommRingCat.ofHom ((T.presheaf.germ ⊤ v trivial).hom.comp
      (h.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)) =
      (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ h.appTop ≫ T.presheaf.germ ⊤ v trivial := rfl
  simp only [spMap]
  rw [e, Spec.map_comp, Spec.map_comp, ← Scheme.fromSpecStalk_toSpecΓ_assoc, Category.assoc, Category.assoc,
    ← Scheme.toSpecΓ_naturality_assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
