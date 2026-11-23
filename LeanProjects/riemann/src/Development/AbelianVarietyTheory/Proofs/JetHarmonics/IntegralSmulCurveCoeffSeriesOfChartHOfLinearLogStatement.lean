import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IntegralSmulCurveCoeffSeriesOfChartHOfLinearLog
import Development.AbelianVarietyTheory.Definitions.Jets.IsSelfOf
import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces
open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_smul_curveCoeffSeriesOfChartH_of_linear_log : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (κ : Type) [Fintype κ] (X : RawChart C d I κ), RLaw X V → ∀ γ : κ → PowerSeries C, IsCv V γ → (∀ i n, 2 ≤ n → n < V.l ^ 2 → PowerSeries.coeff n (alongCv γ (X.lg i)) = 0) → IntS V ((V.l : C) • hCoef X γ V.l) ∧ ((∀ v : κ → C, (∀ i, V.Ge 0 (v i)) → V.MM ((V.l : C) * PowerSeries.coeff V.l (alongCv γ (X.sg v)))) → ∀ i μ, V.MM (MvPowerSeries.coeff μ (MvPowerSeries.pderiv C i ((V.l : C) • hCoef X γ V.l)))) := by
  first | exact @GlobalTheory.GaugeCoef.main | exact GlobalTheory.GaugeCoef.main | (intros; apply GlobalTheory.GaugeCoef.main <;> assumption)
