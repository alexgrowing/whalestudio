import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DifferentiableOnLogChart
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsHodgeFrameIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsExponentialChartAtPointStatement
open AlgebraicGeometry CategoryTheory Limits NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.GradedNorm GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor
open scoped Topology ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.differentiableOn_log_chart : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (σ : κ.c.F →+* ℂ) (n g r k : ℕ) (ch : OpenPartialHomeomorph (CxPts (genStr s.T.Z) σ) (Fin n → ℂ)) (ex : ExpMaps s.T.Z σ g) (lam : (Fin n → ℂ) → Fin r → Fin g → ℂ) (ρ : Fin g → Fin r → ℂ), IsLogChart k ch ex lam ρ → DifferentiableOn ℂ lam (logDom n k) := by
  first | exact @GlobalTheory.ShFam.Hor.LogCh.differentiableOn_lam_of_isLogChart | exact GlobalTheory.ShFam.Hor.LogCh.differentiableOn_lam_of_isLogChart | (intros; apply GlobalTheory.ShFam.Hor.LogCh.differentiableOn_lam_of_isLogChart <;> assumption)
