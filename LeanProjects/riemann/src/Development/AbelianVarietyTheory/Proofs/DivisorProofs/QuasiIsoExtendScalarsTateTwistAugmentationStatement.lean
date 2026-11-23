import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiIsoExtendScalarsTateTwistAugmentation
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendScalarsUliftHomAdditive
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quasiIso_extendScalars_tateTwist_augmentation : ∀ (Q q : ℕ) [NeZero Q] (hq : q ∣ Q) (i : ℤ), QuasiIso (extAug (ZMod.castHom hq (ZMod q)) (tw Q i)) := by
  first | exact @GlobalTheory.EtC.ExtQis.quasiIso_extAug | exact GlobalTheory.EtC.ExtQis.quasiIso_extAug | (intros; apply GlobalTheory.EtC.ExtQis.quasiIso_extAug <;> assumption)
