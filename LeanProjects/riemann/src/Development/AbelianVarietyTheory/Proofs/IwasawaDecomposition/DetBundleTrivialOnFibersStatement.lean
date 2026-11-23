import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DetBundleTrivialOnFibers
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.det_bundle_trivial_on_fibers : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (X : GMod Xo c) (Y : Model Xo c (RingHom.id c.F)) (ρ : gen Y ⟶ gen X)
    (hY : (GlobalTheory.FlagMod.detOm Y).IsLB), Y.jQ ≫ ρ = X.jQ →
    ∀ (W : Scheme.{0}) (K : Type) [Field K] (g : W ⟶ gen Y) (a : W ⟶ Sp K) (y0 : Sp K ⟶ gen X), g ≫ ρ = a ≫ y0 →
    GlobalTheory.CechPic.pull (g ≫ genι Y) (GlobalTheory.CechPic.cls _ hY) = 0 := by
  first | exact @GlobalTheory.DetTriv.detOm_trivial_of_point | exact GlobalTheory.DetTriv.detOm_trivial_of_point | (intros; apply GlobalTheory.DetTriv.detOm_trivial_of_point <;> assumption)
