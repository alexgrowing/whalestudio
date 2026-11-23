import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.EmbShortThLeThetaPlain
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ThetaLeMsupOfSetC
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.WeightedPrimeSumBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LatOfLamSt
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.EntriesOfGaps
open NumberField IsDedekindDomain AlgebraicGeometry CategoryTheory Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.FormTies
open scoped TensorProduct

namespace GlobalTheory.RunDepth

theorem run_weights_sum : ∀ (D : D7) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (j : ℕ), InR D j → WeightAlgebra.IsF' (kaR Tp hK j) (lR Tp hK j) (fR Tp hK j) Tp.TO (fR Tp hK j).n ∧ (kaR Tp hK j).n = (fR Tp hK j).n + Tp.TO * (lR Tp hK j).n ∧ WeightFamilies.dimY D j ≤ Tp.TO ∧ D.R.r ≤ (fR Tp hK j).n := by
  intro D L Pm Tp hK j hj
  have hP : (fR Tp hK j).n = Tp.nP := rfl
  have hW : (lR Tp hK j).n = Tp.nWn := rfl
  refine ⟨GlobalTheory.RunWeightTest.isF'_fWt _ _ _ _ _ _, ?_, ?_, ?_⟩
  · rw [hP, hW, ← Tp.split]; exact kaWt_n D hK _ j
  · rw [GlobalTheory.DepthBoundTest.dimY_eq_flag hj, ← Tp.Dp_eq]
    have := Tp.TO_40
    omega
  · rw [hP, Tp.nP_eq]
    have hf : 1 ≤ D.R.f := by unfold Ranks.f Ranks.n; have := And.intro (Nat.one_le_two_pow (n := D.R.e)) (show 0 < D.R.ord by positivity); omega
    nlinarith

end GlobalTheory.RunDepth
