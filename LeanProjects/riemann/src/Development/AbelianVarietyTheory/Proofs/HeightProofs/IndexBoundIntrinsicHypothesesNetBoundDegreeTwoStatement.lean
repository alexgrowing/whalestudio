import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IndexBoundIntrinsicHypothesesNetBoundDegreeTwo
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.ConclOfInputs4
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NoCommonZeroSt
import Formalism.LocalToGlobal.ProjectiveLattices.DepthTie
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin GlobalTheory.RunIn GlobalTheory.FinalJoin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.indexBoundIntrinsicHypotheses_netBound_degreeTwo : ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (large₂ : SizeData₂ D) (CL : ℝ) (H : KHyp) (Ch Ah Cq Aq C2 A2 CR CT : ℝ) (S : Scal B) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ) (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ), InputsR large₂ X (kR CL) H Ch Ah Cq Aq C2 A2 CR CT S ka wL wF Tn nP nW h0 nus → InputsR large₂ X (k4 large₂ CL) H Ch Ah Cq Aq C2 A2 CR CT S ka wL wF Tn nP nW h0 nus := by
  first | exact @GlobalTheory.FinalJoin.inputsR_deg_two | exact GlobalTheory.FinalJoin.inputsR_deg_two | (intros; apply GlobalTheory.FinalJoin.inputsR_deg_two <;> assumption)
