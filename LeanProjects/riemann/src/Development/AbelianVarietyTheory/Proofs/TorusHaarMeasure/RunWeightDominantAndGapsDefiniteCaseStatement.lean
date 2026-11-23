import Mathlib
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.RunWeightDominantAndGapsDefiniteCase
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Generic
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.TheoremZeroOfReducedInputs
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LiftIndexPowFourLeDegree
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.AdmissibleModuleIffLatticeQuotients
import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.MaximalCuspKernels.KerExistsStatement
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SupBoundPageRows
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LocalUnfoldBStatementHolds
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.RunIn GlobalTheory.Shares
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.runWeight_dominant_and_gaps_definiteCase : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CR CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ), FamilyHypotheses.HypPage large₂ (recPJ h j hj) H C2 A2 CR CT ka wL wF Tn nP nW h0 → j = D.R.m → 8 ≤ D.R.r → ∀ k : (T.U j T.σ₀).Comp, ((T.U j T.σ₀).X k).p0 = 0 ∧ IsStrictDom ((T.U j T.σ₀).X k) (laR T j wL k) ∧ ∀ (τ : ((T.U j T.σ₀).X k).Ψ) (a b : Fin D.R.r), (b : ℕ) = a + 1 → (laR T j wF k - kapW ((T.U j T.σ₀).X k) - WeightFamilies.dimY D j • laR T j wL k) τ b + 2 * (laR T j wL k τ a - laR T j wL k τ b) ≤ (laR T j wF k - kapW ((T.U j T.σ₀).X k) - WeightFamilies.dimY D j • laR T j wL k) τ a := by
  first | exact @GlobalTheory.RunWeightDomDef.run_weight_dom_definite | exact GlobalTheory.RunWeightDomDef.run_weight_dom_definite | (intros; apply GlobalTheory.RunWeightDomDef.run_weight_dom_definite <;> assumption)
