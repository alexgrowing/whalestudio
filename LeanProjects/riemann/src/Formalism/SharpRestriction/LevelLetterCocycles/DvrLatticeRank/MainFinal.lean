import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.MainPf
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.U1linkPf

noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules

theorem integrality_from_metric_of_large_constant :
    ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
      (CA CB CK C : ℝ), 160 ≤ C → FontExAll D HW F → DdRFull D → DiRank D HW F Cm →
        IntegralityFromMetric D HW F Cm CA CB CK C :=
  lifting_theorem_of_uniform_link u1link_pf

end Formalism.MainNotions.N.Ln34

end
