import Mathlib
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import Development.AbelianVarietyTheory.Definitions.RegularCharts.SCharts
import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsFiniteIntegralChartCoverFlagSpaceStatement
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsRefinedCoveringChartFamilyStatement
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsNormalChartsOfCoveringChartsStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

namespace GlobalTheory.Reg

theorem isDiscreteValuationRing_valuationSubring_place {K : Type} [Field K] [NumberField K]
    (la : HeightOneSpectrum (𝓞 K)) : IsDiscreteValuationRing (la.valuation K).valuationSubring :=
  (la.valuation K).valuationSubring_isDiscreteValuationRing

theorem exists_sCharts : ReciprocityTheory.ChartRestriction.G.Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), EvLaws Xo c → IntDiagUnit Xo c → ∀ la : HeightOneSpectrum (𝓞 c.F), ModelAt Xo c la → (∃ S : SCharts Xo c la, S.CovQ) ∧ ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n m : ℕ) (ws : Fin m → Rul Xo c), (∀ i, ws i ∈ sec Xo c a n) → Formalism.L2.PjFree.NoCommonZero Xo c ws → ∃ S : SCharts Xo c la, S.FamW ws ∧ S.CovQ := by
  intro hST E _ _ _ H Dw l Xo c hEv hDiag la hM
  obtain ⟨Y, hY⟩ := hM
  have := isDiscreteValuationRing_valuationSubring_place la

  obtain ⟨J, hJ, P, hP⟩ := GlobalTheory.T.exists_finite_integral_chart_cover_flagSpace hST E H Dw l Xo c hEv.bc (la.valuation c.F).valuationSubring Y hY
  have := hJ
  obtain ⟨S, hS, -⟩ := GlobalTheory.T.exists_normal_charts_of_covering_charts E H Dw l Xo c hEv hDiag la J P hP
  refine ⟨⟨S, hS⟩, fun a n m ws hws hnz => ?_⟩

  obtain ⟨J', hJ', P', hP', hF⟩ := GlobalTheory.T.exists_refined_covering_chart_family E H Dw l Xo c hEv _ _ J P hP a n m ws hws hnz
  have := hJ'
  obtain ⟨S', hS', hW⟩ := GlobalTheory.T.exists_normal_charts_of_covering_charts E H Dw l Xo c hEv hDiag la J' P' hP'
  exact ⟨S', hW m ws hF, hS'⟩

end GlobalTheory.Reg
