import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarBetaIC

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.Pf.ScalarFramePf

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (D : Formalism.BasicNotions.D7)

def SpanOm : Prop :=
  ∀ {T T' : D.host.E} (F : FlagG (VS D) D.R.rS T) (F' : FlagG (VS D) D.R.rS T'),
    (Zhat F F').det ≠ 0 → Gflag F F' ≠ 0 →
    ∀ m ∈ orth (VS D) F'.X, ∃ x' ∈ F'.X, ∃ w ∈ orth (VS D) (F.Xplus ⊔ F'.Xplus), ∃ a b : D.host.E,
      m = x' + w + a • F'.z + b • Gom F.fvec F'.fvec

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
