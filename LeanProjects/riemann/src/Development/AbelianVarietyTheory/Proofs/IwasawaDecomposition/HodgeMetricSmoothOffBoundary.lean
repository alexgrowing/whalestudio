import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsHodgeFrameIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EigenMetricOnSetStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HodgeSmoothConjStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EigenframeGramNearPointStatement
open AlgebraicGeometry CategoryTheory Limits NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.GradedNorm GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam GlobalTheory.ShFam.Pad

set_option autoImplicit false

theorem GlobalTheory.ShFam.ToroidalCompactificationData.hodge_smoothOn : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (x : ToroidalCompactificationData s) (σ : κ.c.F →+* ℂ), (x.hodge σ).SmoothOn (manifold s.T.Z σ) {y | ¬ LiesIn y (genBd s.T.Z)} := by
  intro D A N j S κ s x σ
  have good : ∀ σ, Formalism.L2.PjFree.GoodEmb κ.c σ →
      (x.hodge σ).SmoothOn (manifold s.T.Z σ) {y | ¬ LiesIn y (genBd s.T.Z)} :=
    fun σ hσ => GlobalTheory.T.eigen_metric_on_set (x.hodge σ) _ fun V φ F τ a b hV y₀ hy₀ hV₀ =>
      GlobalTheory.T.eigenframe_gram_near_point D A N j S κ s x σ hσ V φ F τ a b hV y₀ hy₀ hV₀
  by_cases hσ : Formalism.L2.PjFree.GoodEmb κ.c σ
  · exact good σ hσ
  · have h1 : Formalism.L2.PjFree.GoodEmb κ.c ((starRingEnd ℂ).comp σ) := by
      simpa only [Formalism.L2.PjFree.goodOf, if_neg hσ] using Formalism.L2.PjFree.goodEmb_goodOf κ.c σ
    exact GlobalTheory.T.hodge_smooth_conj D A N j S κ s x σ _ (RingHom.ext fun _ => (Complex.conj_conj _).symm) (good _ h1)
