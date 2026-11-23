import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeEqChernFormIntegralOfComplexCaseStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernTopFormSignedMeasureEqAtlasPartStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFormEvalRealPolyChernFormsFlaggedMetricStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleFibreIntegralPullbackMulFibreClassStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFlaggedBundleMetricPullGramRefinementStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernFormsPullbackMetricFlagRefinementStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackRealPolynomialEvenFormFieldsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralChernFormsEqEsymmGradedFormsFlagStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagGradedMetricsWeightsOnLineBundlesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralChernFormPolyEqIntersectionNumberStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolAtlasTopFormIntegralFiniteAdditiveHomogeneousStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.IsMetricFrOfIsMetricOn
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ChernDegreeComplex
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

theorem GlobalTheory.ChernCalc.chernWeilNumbers_of_chernDegreeComplex :
    GlobalTheory.Published.ChernDegreeComplex → GlobalTheory.Published.ChernWeilNumbers := by
  intro h F _ σ X Y ι _ m E E' φ f gr hR hG H hH R
  have hD : GlobalTheory.Published.ChernDegree := GlobalTheory.T.degreeEqChernFormIntegral_of_complex_case h
  have hf : f ≫ X.str = Y.str := hR.hom.inducedModelMorphism_comp_structureMap
  have hform := GlobalTheory.T.isForm_evalRealPoly_chernForms_flaggedMetric F σ X ι m 0 E H (isMetricFr_of_isMetricOn hH) R
  have hM := GlobalTheory.T.isFlaggedBundleMetric_pullGram_refinement F σ X Y ι m E E' φ f hf hR H hH
  have hu : ptsIn X.str σ ⊤ = Set.univ := Set.eq_univ_of_forall fun _ => mem_ptsIn_top
  choose L r ψ h1 h2 h3 using GlobalTheory.T.flag_graded_metrics_weights_on_line_bundles F σ Y ι m E' _ gr hG hM
  have e : grF E' (pullGram E H φ f hf) = fun x => c1W (ψ x) := funext fun x => (h3 x).symm
  unfold HasChernIntegral
  rw [hu]
  simp only [GlobalTheory.T.chernTopFormSignedMeasure_eq_atlas_part F σ X ι m E H R]
  refine ⟨fun ε => ?_, ?_⟩
  · have := (GlobalTheory.T.holAtlas_topFormIntegral_finite_additive_homogeneous _ _ (atlas X σ)).1 _ hform ε
    exact measure_ne_top _ _
  · refine (GlobalTheory.T.flagBundle_fibreIntegral_pullback_mul_fibreClass F σ X Y ι m E E' φ f hf hR H hH _ hform).symm.trans ?_
    rw [GlobalTheory.T.pullback_real_polynomial_even_form_fields _ _ _ _ _ _ _ _ _ _ (GlobalTheory.T.chernForms_pullback_metric_flag_refinement F σ X Y ι m E E' φ f hf hR H hH) R,
      GlobalTheory.T.integral_chernForms_eq_esymm_gradedForms_flag F σ Y ι m E' _ hM, e]
    exact GlobalTheory.T.integral_chernFormPoly_eq_intersectionNumber hD F σ Y _ gr L r ψ (fun a => ⟨h1 a, h2 a⟩) _
