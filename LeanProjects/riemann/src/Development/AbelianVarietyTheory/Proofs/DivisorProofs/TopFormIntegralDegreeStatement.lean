import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopFormIntegralDegree
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
theorem _root_.GlobalTheory.T.top_form_integral_degree : ∀ (k : Type) [CommRing k] (S : Scheme.{0}) (p : S ⟶ Sp k), IsRegSurf p → ∀ (N : HermLB p) (ρ : ∀ σ : k →+* ℂ, AlgChart p σ 1 → CxPts p σ → ℝ) (I l : ℝ), IsTopForm ρ I → (∀ (σ : k →+* ℂ) (y : CxPts p σ), ∃ c : AlgChart p σ 1, y ∈ c.e.source ∧ ρ σ c y = l * c.chernDens (N.φ σ) y) → I = l * gdeg N 1 := by
  first | exact @GlobalTheory.ThetaTop.topForm_eq_mul_gdeg | exact GlobalTheory.ThetaTop.topForm_eq_mul_gdeg | (intros; apply GlobalTheory.ThetaTop.topForm_eq_mul_gdeg <;> assumption)
