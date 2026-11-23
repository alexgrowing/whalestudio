import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AinfCoefficientPsiProperty
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IotaScalarOne
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ainf_coefficient_psi_property : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [Algebra ℤ_[p] Λ] [Module.Finite ℤ_[p] Λ] [FaithfulSMul ℤ_[p] Λ], ∀ (ψ : RL p O Λ →+* RL p O Λ), IsPsi ψ → ∀ m : Ainf p O, m.coeff 0 ≠ 0 → ∀ z w : RL p O Λ, z * ψ (inA m) = inA m * w * ψ z → (inA m : RL p O Λ) ∣ z := by
  first | exact @GlobalTheory.LemYR.lemY_tensor | exact GlobalTheory.LemYR.lemY_tensor | (intros; apply GlobalTheory.LemYR.lemY_tensor <;> assumption)
