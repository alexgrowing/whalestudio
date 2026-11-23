import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorInvolutionAlgebraProperties
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_localization_membership : ∀ (B D : Type) [CommRing B] [CommRing D] [Algebra B D] [Module.Flat B D] (Q : Ideal D) [Q.IsPrime] (f b : B), algebraMap B (Localization.AtPrime Q) b ∈ Ideal.span {algebraMap B (Localization.AtPrime Q) f} → ∃ s : B, s ∉ Q.comap (algebraMap B D) ∧ s * b ∈ Ideal.span {f} := by
  first | (exact @GlobalTheory.localFlat_dvd_descends) | (exact GlobalTheory.localFlat_dvd_descends) | (intros; apply GlobalTheory.localFlat_dvd_descends <;> assumption)
