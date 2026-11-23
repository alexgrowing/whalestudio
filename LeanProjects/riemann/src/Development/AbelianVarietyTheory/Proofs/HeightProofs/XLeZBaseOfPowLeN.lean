import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DisjointExceptional
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.NormComparisonConstants
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NoCommonZeroSt
import Formalism.LocalToGlobal.ProjectiveLattices.DepthTie
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowNumAt
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsStdLarge

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FinalJoin2

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin GlobalTheory.RunIn GlobalTheory.FinalJoin GlobalTheory.FinalJoin2
open GlobalTheory.EX

theorem x_le_zBase_of_pow_le_n {D : D7} (L : SizeData₂ D) (hn : L.sc.x ^ (2 + 8 * L.sc.eps) ≤ (D.R.n : ℝ)) :
    L.sc.x ≤ zBase L := by
  have hx : 1 < L.sc.x := L.sc.one_lt_alt
  have he := L.sc.eps_pos
  have hL : 1 ≤ L.sc.L := by
    unfold Scale.L; exact Real.one_le_rpow hx.le he.le
  have h1 : L.sc.x ≤ L.sc.x ^ (2 + 8 * L.sc.eps) := by
    calc L.sc.x = L.sc.x ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hx.le (by linarith)
  have hf : (D.R.n : ℝ) ≤ D.R.f := by
    unfold Ranks.f; exact_mod_cast (by omega : D.R.n ≤ 2 * D.R.n)
  have hr : (1 : ℝ) ≤ D.R.r := by
    have h1 := D.R.two_le_m
    have h2 := D.R.m_add_three_le_k
    exact_mod_cast (by unfold Ranks.r; omega : 1 ≤ D.R.r)
  have hxf : L.sc.x ≤ (D.R.f : ℝ) := h1.trans (hn.trans hf)
  have hf0 : (0 : ℝ) ≤ D.R.f := by positivity
  unfold zBase
  calc L.sc.x ≤ (D.R.f : ℝ) * 1 * 1 := by linarith
    _ ≤ _ := by gcongr

end GlobalTheory.FinalJoin2

end
