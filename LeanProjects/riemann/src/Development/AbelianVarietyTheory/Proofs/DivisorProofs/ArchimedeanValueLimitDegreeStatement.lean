import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanValueLimitDegree
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHtFunGenericIff
import Development.AbelianVarietyTheory.Definitions.Divisors.HypothesesX
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsX
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open GlobalTheory.CovTestDR GlobalTheory.VdmRec
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedean_value_limit_degree : GlobalTheory.CovTop.HypothesesXH → Hypotheses2 → HypothesesH → RegularAlteration → ∀ r : ℝ, Ch2Const r → OnObj fun _ O _ _ _ _ => ∀ c (M : DRBase O c) (I : M.Emb) (z : M.B), I.Good z 0 → CharZero (M.B.residueField z) → Tendsto (fun R => M.val R z 0) atTop (𝓝 (r * (M.deg z 1 : ℝ))) := by
  first | exact @GlobalTheory.SurfLimit.tendsto_val | exact GlobalTheory.SurfLimit.tendsto_val | (intros; apply GlobalTheory.SurfLimit.tendsto_val <;> assumption)
