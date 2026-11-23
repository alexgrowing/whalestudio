import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ToroidalCompactificationData
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPositiveHermitianFormDomainStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KaehlerPotentialComparisonDomainStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MetricPullbackGramAndInvarianceStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HodgeMetricsSmoothStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HodgeNormSmoothStatement
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.ShFam
open Formalism.DegreeFormula Formalism.MJ GlobalTheory.HodgeDomain GlobalTheory.TrueCx
open scoped ComplexOrder ContDiff

theorem GlobalTheory.ToroidalCompactificationData.exists_isBdOf : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (L : CmList A) (x : ToroidalCompactificationData s), ∃ B, IsBdOf x L B := by
  intro D A N j S κ s L x
  choose a h1 h2 h3 h4 using fun k => GlobalTheory.T.exists_positive_hermitian_form_domain D A N j S κ s L k x
  refine ⟨fun k => ⟨x.m, fun i z => x.nrm κ.σ₀ i (s.toCpt L k z), fun i z _ => x.nrm_pos (s.not_liesIn_toCpt L k z) i,
    fun i z _ => ((x.nrm_div _ i).1 _).2, GlobalTheory.T.hodge_norm_smooth D A N j S κ s L k x, fun i g hg z hz => by rw [s.toCpt_moeb L k hg hz],
    a k, h1 k, h2 k, h3 k, (GlobalTheory.T.kaehler_potential_comparison_domain D A N j S κ s L k x (a k) (h1 k) (h4 k)).1, x.cst, x.cst_pos,
    (GlobalTheory.T.kaehler_potential_comparison_domain D A N j S κ s L k x (a k) (h1 k) (h4 k)).2, x.metW L k, x.metOm L k,
    fun z _ t => (x.met_posDef L k z t).1, fun z _ t => (x.met_posDef L k z t).2,
    fun t => (GlobalTheory.T.hodge_metrics_smooth D A N j S κ s L k x t).1, fun t => (GlobalTheory.T.hodge_metrics_smooth D A N j S κ s L k x t).2,
    fun g hg z hz t => ((GlobalTheory.T.metric_pullback_gram_and_invariance D A N j S κ s L k x).2 g hg z hz t).1,
    fun g hg z hz t => ((GlobalTheory.T.metric_pullback_gram_and_invariance D A N j S κ s L k x).2 g hg z hz t).2⟩,
    fun _ => rfl, fun _ _ _ _ => rfl, h4, fun _ => rfl, fun k f t => ((GlobalTheory.T.metric_pullback_gram_and_invariance D A N j S κ s L k x).1 f t).1,
    fun k f t => ((GlobalTheory.T.metric_pullback_gram_and_invariance D A N j S κ s L k x).1 f t).2⟩
