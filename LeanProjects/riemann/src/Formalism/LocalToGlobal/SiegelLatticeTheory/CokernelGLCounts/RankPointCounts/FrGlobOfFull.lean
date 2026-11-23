import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocEqOfLocFEq

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.TermLoc

namespace Formalism.L2.SG.Pf.FrameGlobalPatching

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (NumberField.RingOfIntegers D.host.E) (VS D).V)}

theorem patchC_of_full (hL : LocFullC Zd u u' F0 what₂) : PatchC Zd u u' F0 what₂ :=
  patchC_of Formalism.L2.SG.Pf.LocalDenominators.latPatch_holds hL

end Formalism.L2.SG.Pf.FrameGlobalPatching
