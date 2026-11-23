import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TendstoArithmeticDegreeFlagHomogeneous
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsX
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tendsto_arithmetic_degree_flag_homogeneous : GlobalTheory.CovTop.HypothesesXH → Hypotheses2 → HypothesesH → GlobalTheory.Published.ScholzeWeinsteinB → OnObj fun D O A _ _ _ =>
    ∀ B : ℝ, 2 ≤ B → ∀ (τ : D.what₂.Tau) (Q : GlobalTheory.FlagPoly.Pol D.what₂.Tau O.Y.N),
      Q.IsHomogeneous (Formalism.MainNotions.WeightThresholdDefs.dimY O.Y) →
      Filter.Tendsto (fun R => O.Y.arDeg (GlobalTheory.FlagAr.setB O.Y B) R (GlobalTheory.FlagPoly.pSum τ 1 * Q) -
        ∑ c, O.Y.htDetT B c τ * (A.w c * Formalism.DegreeFormula.degFl D.what₂.Tau O.Y.N Q)) Filter.atTop (nhds 0) := by
  first | exact @GlobalTheory.FlatLimit.limVal | exact GlobalTheory.FlatLimit.limVal | (intros; apply GlobalTheory.FlatLimit.limVal <;> assumption)
