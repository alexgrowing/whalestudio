import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdicCompletionNoetherianFlatComplete
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_adicCompletion_noetherian_flat_complete : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] (I : Ideal B), ∃ (C : Type) (_ : CommRing C) (φ : B →+* C), IsNoetherianRing C ∧ φ.Flat ∧ IsAdicComplete (I.map φ) C ∧ ∀ (m : ℕ) (a : Ideal B), I ^ m ≤ a → (a.map φ).comap φ = a := by
  first | exact @GlobalTheory.AdicPackage.adicCompletion_package | exact GlobalTheory.AdicPackage.adicCompletion_package | (intros; apply GlobalTheory.AdicPackage.adicCompletion_package <;> assumption)
