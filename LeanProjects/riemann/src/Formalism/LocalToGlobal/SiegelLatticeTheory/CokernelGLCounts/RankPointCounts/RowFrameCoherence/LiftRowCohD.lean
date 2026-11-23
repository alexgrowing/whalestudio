import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RowFrameCoherence.LiftRowCohF
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NilradicalLatticeZMemSpan
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.ConcreteLevelAdelicSubset

noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.RowForm

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def IotaDictIff : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Y : Formalism.L2.SG.Full.Full X) (u u' : D.what₂.Word)
    (s₁ s₂ : GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u')),
    s₁.G ≠ 0 → s₂.G ≠ 0 → s₁.generic → s₂.generic → s₁.lam = s₂.lam → s₁.lam' = s₂.lam' →
      (iotaOf Y.TR (Y.cs u) (Y.cs u') s₁ = iotaOf Y.TR (Y.cs u) (Y.cs u') s₂ ↔
        IotaCompat s₁.lam (lf D (X.Fu u)) s₁.frame s₂.frame (s₂.lin * s₁.lin⁻¹) (gS D))

variable {D : D7} (X : HidaSetting D) (Y : Formalism.L2.SG.Full.Full X) (u u' : D.what₂.Word)

theorem iotaDictNeed_of_iff (hD : IotaDictIff) : IotaDictNeed X Y u u' :=
  fun s₁ s₂ h1 h2 g1 g2 hl hl' hc => (hD D X Y u u' s₁ s₂ h1 h2 g1 g2 hl hl').2 hc

theorem ratPtNeed_holds : RatPtNeed X := fun n hn => ratPt_holds D X n hn

theorem liftRowCohC_of_dict (hD : IotaDictIff) : LiftRowCohC X Y u u' :=
  liftRowCohC_of_frameFix X Y u u' (ratPtNeed_holds X)
    (toTermRel_holds (X := X) (u := u) (u' := u') (F0 := X.Fu u) (F0' := X.Fu u'))
    (frameCorrection_holds X Y u u') (iotaDictNeed_of_iff X Y u u' hD)

end Formalism.L2.SG.Pf.RowForm
