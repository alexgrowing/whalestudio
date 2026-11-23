import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.RefNMapKapL
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcRealXCR

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions
open scoped ENNReal

namespace Formalism.L2.SG.Pf.NcReal.JX

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.L2.SG.RealObj.InfCut Formalism.MainNotions.S

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def FrameRow : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (u w : D.what₂.Word) (v : InfinitePlace X.B.I.F),
    ∃ L : (LsNc5.CIdx D.R.rS D.R.k → ℝ) →ₗ[ℝ] (LsNc5.CIdx D.R.rS D.R.k → ℝ),
      (∀ s : X.B.I.Ginf, (fun i => LsNc5.kapV X w v s i) = L (fun i => LsNc5.kapV X u v s i)) ∧
      |LinearMap.det L| = (Tw w / Tw u) ^ D.R.rS

end Formalism.L2.SG.Pf.NcReal.JX
