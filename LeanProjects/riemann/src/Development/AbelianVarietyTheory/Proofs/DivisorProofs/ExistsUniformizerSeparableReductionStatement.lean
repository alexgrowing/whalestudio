import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformizerSeparableReduction
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TensorProductAction
open scoped TensorProduct nonZeroDivisors
open Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_uniformizer_separable_reduction : ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O],
    ∃ (e : ℕ) (π a : O) (u : Oˣ) (h : ℤ_[l][X]), 0 < e ∧ (l : O) = π ^ e * u ∧ h.Monic ∧
      aeval a h ∈ Ideal.span {π} ∧ e * h.natDegree = Module.finrank ℤ_[l] O ∧
      ∀ (κ : Type) [Field κ] [CharP κ l] (ψ : ℤ_[l] →+* κ), (h.map ψ).Separable ∧
        (LinearMap.charpoly (LinearMap.mulLeft ℤ_[l] a)).map ψ = (h.map ψ) ^ e := by
  first | exact @GlobalTheory.UnramifiedGenerator.exists_ramification_and_generator | exact GlobalTheory.UnramifiedGenerator.exists_ramification_and_generator | (intros; apply GlobalTheory.UnramifiedGenerator.exists_ramification_and_generator <;> assumption)
