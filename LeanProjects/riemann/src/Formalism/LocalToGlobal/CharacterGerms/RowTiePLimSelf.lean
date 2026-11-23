import Formalism.LocalToGlobal.CharacterGerms.RowTiePPTSelf
import Formalism.LocalToGlobal.CharacterGerms.RowTiePCartSelfSt
import Formalism.LocalToGlobal.CharacterGerms.RowTiePLimTy

noncomputable section

namespace Formalism.L2.FormalSeriesBounds

theorem limSelf_holds : LimSelfSt := by
  unfold LimSelfSt AllSelf
  intro C _ _ V O _ _ dd Y d _ I0 _ p g x x' hx hlim
  exact LimTy.lim_mem (Y.rawSelf p) V.l_prime.two_le
    (fun i => FBChart.self_chart_log_constantCoeff (Y := Y) (p := p) i)
    (fun i => FBChart.self_chart_exp_constantCoeff (Y := Y) (p := p) i)
    (fun i => FBChart.rawSelf_lgex (Y := Y) (p := p) i)
    (fun i => FBChart.rawSelf_exlg (Y := Y) (p := p) i)
    g x x' hx hlim

end Formalism.L2.FormalSeriesBounds
