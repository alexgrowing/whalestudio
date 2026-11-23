import Mathlib
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsNormalChartsOfCoveringCharts
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import Development.AbelianVarietyTheory.Definitions.RegularCharts.SCharts
import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_normal_charts_of_covering_charts : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), EvLaws Xo c → IntDiagUnit Xo c → ∀ (la : HeightOneSpectrum (𝓞 c.F)) (J : Type) [Finite J] (P : J → PChart Xo c (la.valuation c.F).valuationSubring.subtype), Covers P → ∃ S : SCharts Xo c la, S.CovQ ∧ ∀ (m : ℕ) (ws : Fin m → Rul Xo c), (∀ j, (P j).Fam ws) → S.FamW ws := by
  first | exact @GlobalTheory.Reg.exists_scharts_of_covers | exact GlobalTheory.Reg.exists_scharts_of_covers | (intros; apply GlobalTheory.Reg.exists_scharts_of_covers <;> assumption)
