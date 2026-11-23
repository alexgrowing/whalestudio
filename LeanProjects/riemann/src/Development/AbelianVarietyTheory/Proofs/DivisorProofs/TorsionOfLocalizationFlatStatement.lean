import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionOfLocalizationFlat
import Mathlib
open TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_of_localization_flat : ∀ (A : Type) [CommRing A] (f : A) (M : Type) [AddCommGroup M] [Module A M],
  Module.Flat (Localization.Away f) (LocalizedModule (Submonoid.powers f) M) →
  ∀ (I : Ideal A) (y : TensorProduct A I M), I.subtype.rTensor M y = 0 → ∃ k : ℕ, f ^ k • y = 0 := by
  first | exact @GlobalTheory.kernel_rTensor_subtype_powers_torsion | exact GlobalTheory.kernel_rTensor_subtype_powers_torsion | (intros; apply GlobalTheory.kernel_rTensor_subtype_powers_torsion <;> assumption)
