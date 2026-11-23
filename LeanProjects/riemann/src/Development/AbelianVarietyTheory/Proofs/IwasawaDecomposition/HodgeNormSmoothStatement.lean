import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HodgeNormSmooth
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ToroidalCompactificationData
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.ShFam
open Formalism.DegreeFormula Formalism.MJ GlobalTheory.HodgeDomain GlobalTheory.TrueCx
open scoped ComplexOrder ContDiff

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_norm_smooth : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (L : CmList A) (k : s.Comp) (x : ToroidalCompactificationData s) (i : Fin x.m), HodgeDomain.SmoothOn fun z : Pt D.what₂.Tau j (N - j) => (x.nrm κ.σ₀ i (s.toCpt L k z) : ℂ) := by
  first | exact @GlobalTheory.ShFam.smoothOn_nrm_toCpt | exact GlobalTheory.ShFam.smoothOn_nrm_toCpt | (intros; apply GlobalTheory.ShFam.smoothOn_nrm_toCpt <;> assumption)
