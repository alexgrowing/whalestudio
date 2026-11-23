import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieAlgebraMetricConjEmbeddingEqConj
import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lieAlgebraMetric_conjEmbedding_eq_conj : ∀ (K : Type) [Field K] [NumberField K] (P : ReciprocityTheory.ChartRestriction.G.Out.PolAV (Sp (𝓞 K))) (F : GlobalTheory.CM.GenFib P) (h : ReciprocityTheory.GeometryOfNumbersTheory.HermFam K (Fin F.P₀.g → K)), F.IsHerm h → ∀ (σ : K →+* ℂ) (a b : Fin F.P₀.g → K), h.form ((starRingEnd ℂ).comp σ) a b = starRingEnd ℂ (h.form σ a b) := by
  first | exact @GlobalTheory.CM.LieMetricConj.form_conj | exact GlobalTheory.CM.LieMetricConj.form_conj | (intros; apply GlobalTheory.CM.LieMetricConj.form_conj <;> assumption)
