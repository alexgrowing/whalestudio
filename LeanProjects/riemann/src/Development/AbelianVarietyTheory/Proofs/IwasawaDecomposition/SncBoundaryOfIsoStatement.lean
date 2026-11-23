import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SncBoundaryOfIso
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.snc_boundary_of_iso : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (Z : GMod Xo c) (e : gen Y ≅ gen Z), Y.jQ ≫ e.hom = Z.jQ → FinalTheorems.Snc (genBdIdeal Y) → FinalTheorems.Snc (genBdIdeal Z) := by
  first | exact @GlobalTheory.TorRef.snc_genBdIdeal_of_iso | exact GlobalTheory.TorRef.snc_genBdIdeal_of_iso | (intros; apply GlobalTheory.TorRef.snc_genBdIdeal_of_iso <;> assumption)
