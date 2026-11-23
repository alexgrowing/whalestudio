import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DetEqNormMulOfSelfDualSameSignature
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
open NumberField Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.L2.GlobalTheoryTheory.GenusMassVolumes
attribute [local instance] IsCMField.starRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.det_eq_norm_mul_of_selfDual_same_signature : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Formalism.HermitianLatticesTheory.IsCMUnram E → ∀ W₁ W₂ : HSpace E, W₁.SigOK → W₂.SigOK → W₁.rank = W₂.rank → (∀ τ, W₁.sig τ = W₂.sig τ) → ∃ z : E, W₂.gram.det = z * star z * W₁.gram.det := by
  first | exact @GlobalTheory.SelfDualDet.det_eq_norm_mul | exact GlobalTheory.SelfDualDet.det_eq_norm_mul | (intros; apply GlobalTheory.SelfDualDet.det_eq_norm_mul <;> assumption)
