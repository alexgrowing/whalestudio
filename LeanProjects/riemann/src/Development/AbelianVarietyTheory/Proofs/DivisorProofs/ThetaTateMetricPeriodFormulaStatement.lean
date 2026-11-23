import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTateMetricPeriodFormula
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
theorem _root_.GlobalTheory.T.theta_tate_metric_period_formula : ∀ (k : Type) [CommRing k] (S : Scheme.{0}) (p : S ⟶ Sp k), IsRegSurf p → ∀ (P : PPAS S), IsArithVar (P.A.hom ≫ p) (P.g + 1) → ∀ (h : VMetric p (omega P.A) P.g) (L : HermLB (P.A.hom ≫ p)), IsTheta P L.B → ∀ (w : LB.Iso (L.pull (dbl P) (dbl_comp P p)).B (L.pow 4).B), w.IsGen → ∀ u : ∀ σ : k →+* ℂ, CxPts (P.A.hom ≫ p) σ → ℝ, IsTate (dbl P) (dbl_comp P p) L w u → ∀ (σ : k →+* ℂ) (c : AlgChart p σ 1) (τ : V 1 → Matrix (Fin P.g) (Fin P.g) ℂ) (ex : Pt (V 1) P.g → CxPts (P.A.hom ≫ p) σ) (j : Fl P.g → Pt (V 1) P.g → ℂ) (m : Pt (V 1) P.g → ℝ), IsPeriodChart h c τ ex → IsFramed L c.e.target τ ex j m → IsDatum c.e.target τ (stdLat P.g) j m → ∀ v ∈ c.e.target, ∃ B' ⊆ c.e.target, IsOpen B' ∧ v ∈ B' ∧ ∃ φ, GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe.IsBundleIso B' τ (stdLat P.g) (GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe.mulPullFactor 2 j) (fun l Q => j l Q ^ 4) φ ∧ ∀ Q ∈ cov B' P.g, m (GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe.mulN 2 Q) * Real.exp (-u σ (ex (GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe.mulN 2 Q))) = (m Q * Real.exp (-u σ (ex Q))) ^ 4 * ‖φ Q‖ ^ 2 := by
  first | exact @GlobalTheory.ThetaDoubling.exists_bundleIso_doubling | exact GlobalTheory.ThetaDoubling.exists_bundleIso_doubling | (intros; apply GlobalTheory.ThetaDoubling.exists_bundleIso_doubling <;> assumption)
