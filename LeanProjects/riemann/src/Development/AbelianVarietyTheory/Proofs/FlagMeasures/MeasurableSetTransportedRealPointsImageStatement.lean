import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableSetTransportedRealPointsImage
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Direct
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareInHH
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.PoincareInHH.PoincareSetting GlobalTheory.CovDom
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.measurableSet_transported_real_points_image : ∀ (D : D7) (X : HidaSetting D) (θ : ℝ) (C : Choice X θ) (S : Set X.B.I.Ginf), MeasurableSet S → MeasurableSet (Gm D '' (trX X C '' S)) := by
  first | exact @GlobalTheory.CovDom.measurableSet_Gm_trX_image | exact GlobalTheory.CovDom.measurableSet_Gm_trX_image | (intros; apply GlobalTheory.CovDom.measurableSet_Gm_trX_image <;> assumption)
