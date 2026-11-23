import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankEqZeroOfDualKilledByTensor
import Mathlib
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_eq_zero_of_dual_killed_by_tensor : ∀ (F : Type) [Field F] [NumberField F] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (ρ : 𝓞 F →+* Module.End ℤ X) (k : Type) [Field k] (ι : Type) [Fintype ι] (b : Module.Basis ι ℤ (𝓞 F)) (w : ι → k), w ≠ 0 → (∀ (l : X →+ k) (χ : X), ∑ i, w i * l (ρ (b i) χ) = 0) → Module.finrank ℤ X = 0 := by
  first | exact @GlobalTheory.finrank_eq_zero_of_dual_killed | exact GlobalTheory.finrank_eq_zero_of_dual_killed | (intros; apply GlobalTheory.finrank_eq_zero_of_dual_killed <;> assumption)
