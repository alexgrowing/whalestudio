import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPosNatSmulMemOfSpanningNumberFieldLattice
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pos_nat_smul_mem_of_spanning_numberField_lattice : ∀ (E : Type) [Field E] [NumberField E] (r : ℕ) (Λ : Submodule (NumberField.RingOfIntegers E) (Fin r → E)), Submodule.span E (Λ : Set (Fin r → E)) = ⊤ → ∀ v : Fin r → E, ∃ q : ℕ, 0 < q ∧ (q : E) • v ∈ Λ := by
  first | exact @GlobalTheory.exists_pos_nat_smul_mem_of_span_eq_top | exact GlobalTheory.exists_pos_nat_smul_mem_of_span_eq_top | (intros; apply GlobalTheory.exists_pos_nat_smul_mem_of_span_eq_top <;> assumption)
