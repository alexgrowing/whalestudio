import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FamilyMetricsSmooth
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsHodgeFrameIff
open AlgebraicGeometry CategoryTheory Limits NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.GradedNorm GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam GlobalTheory.ShFam.Pad
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.family_metrics_smooth : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (x : ToroidalCompactificationData s) (Φ : s.Flag) (k : s.Comp) (σ : D.what₂.LL →+* ℂ) (n : Pad.Letter S.Dw → ℤ), (∀ R : ℝ, 2 ≤ R → (cxSt D.what₂.LL).mSmooth _ σ _ (metsOf x Φ k (some R) σ n)) ∧ (cxSt D.what₂.LL).mSmooth _ σ _ (refMet x Φ k σ n) ∧ Var.Met.SmoothOn (metsOf x Φ k none σ n) {p | (Φ.C k).π (Var.base p) ∉ genBd s.T.Z} := by
  first | exact @GlobalTheory.metsOf_smooth | exact GlobalTheory.metsOf_smooth | (intros; apply GlobalTheory.metsOf_smooth <;> assumption)
