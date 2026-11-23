import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.TupOnto
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.GlobMoveOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MemDdSPow

noncomputable section

namespace Formalism.L2.SG.Pf.TupFinal

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG

theorem repAtTup_of_stab {D : D7} (Zd : TermLoc.LocDat D) (u u' : D.what₂.Word)
    (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)) (what₂ : Finset (Submodule (NumberField.RingOfIntegers D.host.E) (VS D).V))
    (hS : Pf.TupGlob.StabApprox Zd u u') : Pf.FibPart.RepAtTup Zd.M Zd.δ u u' F0 what₂ :=
  Pf.TupOnto.repAtTup_of_glob Zd.M Zd.δ u u' F0 what₂ (Pf.TupGlob.globMove_of u u' hS (Pf.FibD.dict_holds Zd))

end Formalism.L2.SG.Pf.TupFinal
