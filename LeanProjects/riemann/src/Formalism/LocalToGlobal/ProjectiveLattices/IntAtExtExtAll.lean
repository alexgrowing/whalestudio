import Formalism.LocalToGlobal.ProjectiveLattices.RecPJThAllNeBot
import Formalism.LocalToGlobal.ProjectiveLattices.ExtendedPointBaseChange

noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions

variable {D : D7} {T : Top D} (h : LawsP T) (j : ℕ) (hj : InR D j)

def extAll : PtExt (recPJ h j hj) where
  Pt' la := valSet (T.Q.Xo j) T.Q.c (trivialClassCondition (T.Q.Xo j) T.Q.c) la
  extendedPointBaseChange la _ := (T.G.P.ex (T.G.dat j) (WeightAlgebra.resCh la)).yEta
    (Classical.choice ((T.G.P.ex (T.G.dat j) (WeightAlgebra.resCh la)).genNe _))
  vAt' _ y := vG y.1
  vAt'_zero la y := vG_zero (isVal_valSet la y.1 y.2).zero
  vAt'_ne_bot la y := vG_ne_bot (isVal_valSet la y.1 y.2).zero (isVal_valSet la y.1 y.2).ne_bot
  vAt'_add la y := vG_add (isVal_valSet la y.1 y.2).add
  vAt'_smul la y a F ha := vG_smul (fun r => (isVal_valSet la y.1 y.2).smul a r ha) F
  vAt'_mul la y := vG_mul deg (cutR T.C j) (isVal_valSet la y.1 y.2).zero (isVal_valSet la y.1 y.2).mul

theorem extAll_vAt_inc (la : HeightOneSpectrum (𝓞 T.Q.c.F)) (y : (extAll h j hj).Pt' la) (w : WeightFamilies.Wt D j)
    (F : (recB h.toLawsCore).Cusp j w) : (extAll h j hj).vAt' la y ((recPJ h j hj).inc w F) = y.1 F.1 := by

  have hinc : ∀ m, ((recPJ h j hj).inc w F).coeff m = if deg w = m then F.1 else 0 := by
    intro m
    show (AddMonoidAlgebra.single (deg w) _).coeff m = _
    rw [AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
  have h0 : y.1 0 = ⊤ := by
    first
      | exact (isVal_valSet la y.1 y.2).zero
      | simpa using (isVal_valSet la y.1 y.2).zero
  show vG y.1 ((recPJ h j hj).inc w F) = y.1 F.1
  unfold vG
  simp only [hinc]
  apply le_antisymm
  · exact iInf_le_of_le (deg w) (by simp)
  · refine le_iInf fun m => ?_
    split_ifs with hm
    · exact le_rfl
    · rw [h0]
      exact le_top

theorem intAtExt_extAll : IntAtExt _ (extAll h j hj) := by
  intro w F hF la y
  rw [extAll_vAt_inc]
  exact (h.reg j hj).int (dom_wtA w) (cutR_le T.C j w F.2) hF la y.1 y.2

def recPlus : WeightAlgebra.PJ D (recB h.toLawsCore) T.G.P j := xplus (recPJ h j hj) (extAll h j hj) (intAtExt_extAll h j hj)

end Formalism.L2.Pj
