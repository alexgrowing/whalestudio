import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLinearSystemRatioOfDegreeOfGeneratesByRatios
import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
open NumberField GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.DegCmp GlobalTheory.DegVal GlobalTheory.CovTop ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open scoped ENNReal NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLinearSystemRatioOfDegree_of_generatesByRatios : ∀ (K V Ω : Type) [Field K] [AddCommGroup V] [Module K V] [Field Ω] [Algebra K Ω] (ev : V →ₗ[K] Ω), GenRatios ev → ∀ (τ : ℕ) (t : Ω), IsRatio ev τ t := by
  first | exact @GlobalTheory.DegVal.isRatio_of_genRatios | exact GlobalTheory.DegVal.isRatio_of_genRatios | (intros; apply GlobalTheory.DegVal.isRatio_of_genRatios <;> assumption)
