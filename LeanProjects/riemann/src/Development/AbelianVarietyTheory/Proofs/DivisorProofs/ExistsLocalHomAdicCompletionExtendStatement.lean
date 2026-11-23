import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalHomAdicCompletionExtend
import Mathlib
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isLocalHom_adicCompletion_extension_comp : ∀ (A R : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [CommRing R] [IsLocalRing R], IsAdicComplete (maximalIdeal R) R → ∀ (φ : A →+* R), IsLocalHom φ → ∃ ψ : AdicCompletion (maximalIdeal A) A →+* R, IsLocalHom ψ ∧ ψ.comp (algebraMap A (AdicCompletion (maximalIdeal A) A)) = φ := by
  first | exact @GlobalTheory.LocalCompletion.exists_localHom_adicCompletion_extend | exact GlobalTheory.LocalCompletion.exists_localHom_adicCompletion_extend | (intros; apply GlobalTheory.LocalCompletion.exists_localHom_adicCompletion_extend <;> assumption)
