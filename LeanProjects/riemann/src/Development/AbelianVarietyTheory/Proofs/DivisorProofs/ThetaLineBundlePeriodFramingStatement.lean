import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLineBundlePeriodFraming
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
theorem _root_.GlobalTheory.T.theta_line_bundle_period_framing : ∀ (k : Type) [CommRing k] (S : Scheme.{0}) (p : S ⟶ Sp k), IsRegSurf p → ∀ (P : PPAS S), IsArithVar (P.A.hom ≫ p) (P.g + 1) → ∀ (h : VMetric p (omega P.A) P.g) (L : HermLB (P.A.hom ≫ p)), IsTheta P L.B → ∀ (σ : k →+* ℂ) (c : AlgChart p σ 1) (τ : V 1 → Matrix (Fin P.g) (Fin P.g) ℂ) (ex : Pt (V 1) P.g → CxPts (P.A.hom ≫ p) σ) (j : Fl P.g → Pt (V 1) P.g → ℂ) (m : Pt (V 1) P.g → ℝ), IsPeriodChart h c τ ex → IsFramed L c.e.target τ ex j m → IsDatum c.e.target τ (stdLat P.g) j m → ∀ v ∈ c.e.target, ∃ B' ⊆ c.e.target, IsOpen B' ∧ v ∈ B' ∧ ∃ ι, GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe.IsBundleIso B' τ (stdLat P.g) (GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe.mulPullFactor (-1) j) j ι := by
  first | exact @GlobalTheory.SymChart.exists_isBundleIso_neg | exact GlobalTheory.SymChart.exists_isBundleIso_neg | (intros; apply GlobalTheory.SymChart.exists_isBundleIso_neg <;> assumption)
