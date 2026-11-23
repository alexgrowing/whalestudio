import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HodgeMetricsSmooth
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ToroidalCompactificationData
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.ShFam
open Formalism.DegreeFormula Formalism.MJ GlobalTheory.HodgeDomain GlobalTheory.TrueCx
open scoped ComplexOrder ContDiff

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_metrics_smooth : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (L : CmList A) (k : s.Comp) (x : ToroidalCompactificationData s) (t : D.what₂.Tau), (∀ a b, HodgeDomain.SmoothOn fun z : Pt D.what₂.Tau j (N - j) => x.metW L k z t a b) ∧ ∀ a b, HodgeDomain.SmoothOn fun z : Pt D.what₂.Tau j (N - j) => x.metOm L k z t a b := by
  first | exact @GlobalTheory.MetSmooth.metsmooth | exact GlobalTheory.MetSmooth.metsmooth | (intros; apply GlobalTheory.MetSmooth.metsmooth <;> assumption)
