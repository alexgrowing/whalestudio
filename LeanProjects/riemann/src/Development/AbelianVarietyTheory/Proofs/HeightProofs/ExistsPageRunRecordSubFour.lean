import Mathlib
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.ConclOfInputs4
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NoCommonZeroSt
import Formalism.LocalToGlobal.ProjectiveLattices.DepthTie
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsPageRunRecord

set_option autoImplicit false

namespace GlobalTheory.FinalJoin.RecordRun

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin GlobalTheory.RunIn GlobalTheory.FinalJoin

theorem exists_pageRun_record_sub_four : ∃ CK : ℝ, ∀ (D : D7) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm) (hK : DV.KapDef D), SizesAt L → Pm.CnW = 10 → (∀ i, Real.log (D.host.g i) ≤ 9 * L.sc.L + 1) → (10 : ℝ) ^ 60 ≤ L.sc.x → 1000 ≤ Tp.CP → Tp.CP ^ 20 ≤ zBase L → ∀ (B : WeightFamilies.Prov D) (Q : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B Q j), InR D j → OPO L B → PageRun L X ⟨CK, 20, Tp.CP, Tp.eP, Tp.CP, Tp.eP, 7⟩ Tp.CP Tp.eP L.Ct (kaR Tp hK j) (lR Tp hK j) (fR Tp hK j) Tp.TO Tp.nP Tp.nWn (LevelStarExponents.h0 L - 4) :=
  ⟨10, fun _ _ _ T hK S hCnW hg hx hC hCZ B Q _ X hj hO =>
    pageRun_record T hK S hCnW hg hx hC hCZ B Q hj.1 hj.2 X hO⟩

end GlobalTheory.FinalJoin.RecordRun
