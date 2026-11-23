import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodChartLatticeInvariance
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsTateZero
open CategoryTheory AlgebraicGeometry Set Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.ArInt GlobalTheory.TorsionForm GlobalTheory.ThetaRR
open GlobalTheory.LB (toMod)
open GlobalTheory.LieVB (omega)
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe (Fl Pt stdLat symMat tauU siegel symPart ChernIsFlat IsMetric InducesPolarisation cov)
open ReciprocityTheory.L2DbarEstimates (V)
open Filter Topology
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.period_chart_lattice_invariance : ∀ (k : Type) [CommRing k] (S : Scheme.{0}) (p : S ⟶ Sp k) (P : PPAS S) (h : VMetric p (omega P.A) P.g) (σ : k →+* ℂ) (c : AlgChart p σ 1) (τ : V 1 → Matrix (Fin P.g) (Fin P.g) ℂ) (ex : Pt (V 1) P.g → CxPts (P.A.hom ≫ p) σ), IsPeriodChart h c τ ex → ∀ l ∈ stdLat P.g, ∀ Q ∈ cov c.e.target P.g, ex (GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe.transl τ l Q) = ex Q := by
  first | exact @GlobalTheory.PeriodChartLattice.ex_transl_eq | exact GlobalTheory.PeriodChartLattice.ex_transl_eq | (intros; apply GlobalTheory.PeriodChartLattice.ex_transl_eq <;> assumption)
