import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInducedMetricApproximation
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsCompModel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopologicalKrullDimEqSucc
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open MvPolynomial Formalism.DegreeFormula Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.FlagPoly GlobalTheory.FlagAr
open CategoryTheory AlgebraicGeometry GlobalTheory GlobalTheory.TrueGeo GlobalTheory.ArInt ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.ProjVar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_induced_metric_approximation : Hypotheses2 → HypothesesH → ∀ (D : D7) (O : Setup D), O.Core → 2 < D.R.f * (O.N - 1) →
    ∀ (A : SlopeTestRemainingChoices O.Y) (T : Real0 O.Y) (H : Ht O.Y), O.Reads A T H → ∃ s₀ : ℝ, 0 < s₀ ∧ ∀ L ∈ approx A s₀, ∀ c : O.s.Comp,
      ∃ (M : TrueGeo.Model (O.var c)) (L' : HermLB M.p) (k : ℕ+) (cf : HeightOneSpectrum (𝓞 D.what₂.LL) → ℝ),
        (L c).Induced M L' k cf := by
  first | exact @GlobalTheory.ApproxModel.approx_induced | exact GlobalTheory.ApproxModel.approx_induced | (intros; apply GlobalTheory.ApproxModel.approx_induced <;> assumption)
