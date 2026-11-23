import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodChartFramedTheta
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
theorem _root_.GlobalTheory.T.period_chart_framed_theta : ∀ (k : Type) [CommRing k] (S : Scheme.{0}) (p : S ⟶ Sp k), IsRegSurf p → ∀ (P : PPAS S) (h : VMetric p (omega P.A) P.g), P.IsDualRiemann (1 / 2) h → ∀ L : HermLB (P.A.hom ≫ p), IsTheta P L.B → ∀ (σ : k →+* ℂ) (c : AlgChart p σ 1) (τ : V 1 → Matrix (Fin P.g) (Fin P.g) ℂ) (ex : Pt (V 1) P.g → CxPts (P.A.hom ≫ p) σ) (j : Fl P.g → Pt (V 1) P.g → ℂ) (m : Pt (V 1) P.g → ℝ), IsPeriodChart h c τ ex → IsFramed L c.e.target τ ex j m → IsDatum c.e.target τ (stdLat P.g) j m → InducesPolarisation c.e.target τ (stdLat P.g) j := by
  first | exact @GlobalTheory.ThetaPol.inducesPolarisation | exact GlobalTheory.ThetaPol.inducesPolarisation | (intros; apply GlobalTheory.ThetaPol.inducesPolarisation <;> assumption)
