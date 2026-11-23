import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SncToroidalGenericBoundaryOfSncBoundary
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

namespace GlobalTheory.TorRef

theorem snc_genBdIdeal_of_iso : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H)
    (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (Z : GMod Xo c)
    (e : gen Y ≅ gen Z), Y.jQ ≫ e.hom = Z.jQ → FinalTheorems.Snc (genBdIdeal Y) → FinalTheorems.Snc (genBdIdeal Z) := by
  intro E _ _ _ H D l Xo c Y Z e he h
  refine GlobalTheory.SncIso.snc_vanishingIdeal_of_isIso e.inv (genBd Y) (genBd Z) (fun x => ?_) h
  rw [mem_genBd, mem_genBd, not_iff_not, ← he]
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨a, by rw [Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, e.hom_inv_id]; rfl⟩
  · rintro ⟨a, ha⟩
    exact ⟨a, by rw [Scheme.Hom.comp_apply, ha, ← Scheme.Hom.comp_apply, e.inv_hom_id]; rfl⟩

end GlobalTheory.TorRef
