import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaPushforwardMetricWeights
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
theorem _root_.GlobalTheory.T.theta_pushforward_metric_weights : ∀ (k : Type) [CommRing k] (S : Scheme.{0}) (p : S ⟶ Sp k), IsRegSurf p → ∀ (P : PPAS S) (h : VMetric p (omega P.A) P.g), P.IsDualRiemann (1 / 2) h → ∀ L : HermLB (P.A.hom ≫ p), IsTheta P L.B → ∀ (M : LB S) (hM : M.IsLB) (ψ : toMod M ≅ (Scheme.Modules.pushforward P.A.hom).obj (toMod L.B)), ∃ (φ : ∀ σ : k →+* ℂ, Weight p σ M) (h₁ : ∀ σ, (φ σ).IsCInf) (h₂ : ∀ σ σ', (φ σ).IsConj (φ σ')), ∀ (σ : k →+* ℂ) (y : CxPts p σ), ∃ (c : AlgChart p σ 1) (τ : V 1 → Matrix (Fin P.g) (Fin P.g) ℂ) (ex : Pt (V 1) P.g → CxPts (P.A.hom ≫ p) σ), y ∈ c.e.source ∧ IsPeriodChart h c τ ex ∧ IsL2OnDiagonal L ⟨M, hM, φ, h₁, h₂⟩ ψ c τ ex := by
  first | exact @GlobalTheory.ThetaSquareIntegrable.exists_l2Weight | exact GlobalTheory.ThetaSquareIntegrable.exists_l2Weight | (intros; apply GlobalTheory.ThetaSquareIntegrable.exists_l2Weight <;> assumption)
