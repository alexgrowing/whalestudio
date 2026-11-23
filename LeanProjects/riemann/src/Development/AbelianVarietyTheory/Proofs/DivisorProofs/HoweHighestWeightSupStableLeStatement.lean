import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HoweHighestWeightSupStableLe
import Development.AbelianVarietyTheory.Definitions.Divisors.ActAtApply
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.howeHighestWeight_sup_stable_le : ∀ (p q : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (act : Mat p q →ₗ[ℂ] Module.End ℂ V), Good act → ∀ N N' : Submodule ℂ V, KStable act N → KStable act N' → ∀ μ : Ix p q → ℚ, (N ⊔ N') ⊓ hwSub act μ ≤ (N ⊓ hwSub act μ) ⊔ (N' ⊓ hwSub act μ) := by
  first | exact @GlobalTheory.HoweR.hw_sup_le | exact GlobalTheory.HoweR.hw_sup_le | (intros; apply GlobalTheory.HoweR.hw_sup_le <;> assumption)
