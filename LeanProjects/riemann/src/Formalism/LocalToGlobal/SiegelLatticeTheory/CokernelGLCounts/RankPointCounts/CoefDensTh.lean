import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DensCongClose

noncomputable section

namespace Formalism.L2.SG.Pf.Coef

open Formalism.MainNotions.S.LocalSplitGroups

theorem densTh_of_ga {D : Formalism.BasicNotions.D7} {M : ∀ p : PlF D, Formalism.MainNotions.S.Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep}
    {δ : ∀ p : PlF D, (D.s.atP p).Fp} {L : Formalism.L2.SG.CntLocal.LocSp D M} {u u' : D.what₂.Word}
    (hG : GaPlusTh M δ u u') : FCount.DensTh M δ L u u' :=
  densTh_of Formalism.L2.SG.Pf.density_congruence_holds hG

end Formalism.L2.SG.Pf.Coef
