import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsExtraFurther
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.OfPowRealises
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ZpowMemSubringOfInvMem
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

theorem ModelTwistMulSecs.of_modelMulSecs (h : ModelMulSecs.Statement) : ModelTwistMulSecs.Statement :=
  fun F _ K _ _ ι _ Ω _ _ y k₀ N e hmod β Q hQ p m => h F K ι Ω y k₀ N e hmod β Q hQ p m

theorem ModelTwistMulSecs.proof (hT : TensorRealises.Statement) : ModelTwistMulSecs.Statement :=
  ModelTwistMulSecs.of_modelMulSecs (ModelMulSecs.proof hT BaseRealises.proof)

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
