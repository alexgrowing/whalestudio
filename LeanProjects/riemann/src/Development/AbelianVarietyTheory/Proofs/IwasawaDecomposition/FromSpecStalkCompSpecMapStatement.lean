import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FromSpecStalkCompSpecMap
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InRealConeSelf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PhiDivisorArcBlowup
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMonomialLevelFormDvr
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fromSpecStalk_comp_spec_map : ∀ (T : Scheme.{0}) (R : Type) [CommRing R] (h : T ⟶ Sp R) (v : T), T.fromSpecStalk v ≫ h = spMap ((T.presheaf.germ ⊤ v trivial).hom.comp (h.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)) := by
  first | exact @GlobalTheory.fromSpecStalk_comp_eq_spMap_germ | exact GlobalTheory.fromSpecStalk_comp_eq_spMap_germ | (intros; apply GlobalTheory.fromSpecStalk_comp_eq_spMap_germ <;> assumption)
