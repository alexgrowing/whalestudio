import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAdicCompletionLift
import Mathlib
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_adic_completion_lift : ∀ {A R : Type} [CommRing A] [IsLocalRing A] [CommRing R] [IsLocalRing R] (φ : A →+* R), IsAdicComplete (maximalIdeal R) R → (maximalIdeal A).map φ = maximalIdeal R → ∃ ψ : AdicCompletion (maximalIdeal A) A →+* R, ψ.comp (algebraMap A (AdicCompletion (maximalIdeal A) A)) = φ := by
  first | exact @GlobalTheory.exists_maximalIdeal_adicCompletion_lift | exact GlobalTheory.exists_maximalIdeal_adicCompletion_lift | (intros; apply GlobalTheory.exists_maximalIdeal_adicCompletion_lift <;> assumption)
