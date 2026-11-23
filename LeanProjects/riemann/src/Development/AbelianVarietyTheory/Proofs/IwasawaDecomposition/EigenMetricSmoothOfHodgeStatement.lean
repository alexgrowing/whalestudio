import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EigenMetricSmoothOfHodge
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsHodgeFrameIff
open AlgebraicGeometry CategoryTheory Limits NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.GradedNorm GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam GlobalTheory.ShFam.Pad
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eigen_metric_smooth_of_hodge : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (x : ToroidalCompactificationData s) (σ : κ.c.F →+* ℂ) (R : ℝ), 2 ≤ R → (x.hodge σ).SmoothOn (manifold s.T.Z σ) {y | ¬ LiesIn y (genBd s.T.Z)} → (x.eigMetAt σ (some R)).SmoothOn (manifold s.T.Z σ) Set.univ := by
  first | exact @GlobalTheory.ShFam.ToroidalCompactificationData.smoothOn_eigMetAt_some | exact GlobalTheory.ShFam.ToroidalCompactificationData.smoothOn_eigMetAt_some | (intros; apply GlobalTheory.ShFam.ToroidalCompactificationData.smoothOn_eigMetAt_some <;> assumption)
