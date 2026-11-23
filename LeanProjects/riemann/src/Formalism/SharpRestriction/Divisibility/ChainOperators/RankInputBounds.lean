import Formalism.SharpRestriction.Divisibility.ModuliIntegralCharts
import Formalism.SharpRestriction.Divisibility.ChainOperators.RankInputOfDualBound

namespace Formalism.MainNotions.DIV.RankInputBounds

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts

theorem dPle_of_sig (D : D7) {nch : NChoice D} (X : LiftErrorLocal.Loc D nch)
    (h : ∀ d, min (X.P6.jj d) (X.P6.rk d - X.P6.jj d) ≤ D.R.m) : ConditionalKappaBounds.Rk.DPle D X :=
  fun d i _ y => X.P6.dP_le_of (h d) (D.host.g i) y

theorem rank_input_of_signature (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) {nch : NChoice D} (X : LiftErrorLocal.Loc D nch)
    (h : ∀ d, min (X.P6.jj d) (X.P6.rk d - X.P6.jj d) ≤ D.R.m) (CRd : ℝ) (hC : 6 ≤ CRd) : ThetaNormsAndLinks.CharacterRankDiscriminant D X CRd :=
  Formalism.MainNotions.DIV.CutRk.rank_input_of_dual_bound D L P X (dPle_of_sig D X h) CRd hC

theorem rank_input_holds (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) {nch : NChoice D} (X : LiftErrorLocal.Loc D nch) (CRd : ℝ) (hC : 6 ≤ CRd) :
    ThetaNormsAndLinks.CharacterRankDiscriminant D X CRd :=
  rank_input_of_signature D L P X X.sig_le CRd hC

end Formalism.MainNotions.DIV.RankInputBounds
