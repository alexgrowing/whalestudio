import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SandwichKernelRangeExact
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsBasisOfBot
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sandwich_kernel_range_exact : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (ε : PreTilt O p), IsPrimitiveRoot (root ε).untilt p → ∀ (Γ : Type) [CommRing Γ] [Algebra ℤ_[p] Γ] (h : ℕ) (D : Datum ε h Γ), LinearMap.ker (bC C D) = LinearMap.range (alC C D) ∧ LinearMap.ker (alC C D) = LinearMap.range (bC C D) := by
  first | exact @GlobalTheory.DetInv.ker_bC_eq_range_alC_and_ker_alC_eq_range_bC | exact GlobalTheory.DetInv.ker_bC_eq_range_alC_and_ker_alC_eq_range_bC | (intros; apply GlobalTheory.DetInv.ker_bC_eq_range_alC_and_ker_alC_eq_range_bC <;> assumption)
