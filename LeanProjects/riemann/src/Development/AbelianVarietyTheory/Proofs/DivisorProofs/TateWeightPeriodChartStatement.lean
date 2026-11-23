import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateWeightPeriodChart
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
theorem _root_.GlobalTheory.T.tate_weight_period_chart : ∀ (k : Type) [CommRing k] (S : Scheme.{0}) (p : S ⟶ Sp k), IsRegSurf p → ∀ (P : PPAS S), IsArithVar (P.A.hom ≫ p) (P.g + 1) → ∀ (h : VMetric p (omega P.A) P.g) (L : HermLB (P.A.hom ≫ p)), IsTheta P L.B → ∀ (w : LB.Iso (L.pull (dbl P) (dbl_comp P p)).B (L.pow 4).B), w.IsGen → ∀ u : ∀ σ : k →+* ℂ, CxPts (P.A.hom ≫ p) σ → ℝ, (∀ σ, Continuous (u σ)) → IsTate (dbl P) (dbl_comp P p) L w u → ∀ (σ : k →+* ℂ) (c : AlgChart p σ 1) (τ : V 1 → Matrix (Fin P.g) (Fin P.g) ℂ) (ex : Pt (V 1) P.g → CxPts (P.A.hom ≫ p) σ) (j : Fl P.g → Pt (V 1) P.g → ℂ) (m : Pt (V 1) P.g → ℝ), IsPeriodChart h c τ ex → IsFramed L c.e.target τ ex j m → IsDatum c.e.target τ (stdLat P.g) j m → InducesPolarisation c.e.target τ (stdLat P.g) j → IsMetric c.e.target τ (stdLat P.g) j (fun Q => m Q * Real.exp (-u σ (ex Q))) ∧ ChernIsFlat c.e.target τ (fun Q => m Q * Real.exp (-u σ (ex Q))) := by
  first | exact @GlobalTheory.TateChart.isMetric_chernIsFlat_of_isTate | exact GlobalTheory.TateChart.isMetric_chernIsFlat_of_isTate | (intros; apply GlobalTheory.TateChart.isMetric_chernIsFlat_of_isTate <;> assumption)
