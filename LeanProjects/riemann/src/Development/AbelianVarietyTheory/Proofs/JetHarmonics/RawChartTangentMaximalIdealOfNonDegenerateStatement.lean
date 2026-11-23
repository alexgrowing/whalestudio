import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.RawChartTangentMaximalIdealOfNonDegenerate
import Development.AbelianVarietyTheory.Definitions.Jets.IsSelfOf
import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces
open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rawChart_tangent_maximalIdeal_of_nonDegenerate : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (κ : Type) [Fintype κ] (X : RawChart C d I κ), RLaw X V → HasProj X V → NonDeg X V → ∀ H : ∀ g, X.CartHyp V g, RawChart.RankMaximalCondition H := by
  first | exact @GlobalTheory.RowAt.GoodInj.tangent_mm_of_nonDeg | exact GlobalTheory.RowAt.GoodInj.tangent_mm_of_nonDeg | (intros; apply GlobalTheory.RowAt.GoodInj.tangent_mm_of_nonDeg <;> assumption)
