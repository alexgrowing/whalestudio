import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCosetRepresentativesOfFiniteSubgroupPadicI
import Mathlib
open PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_coset_reps_finite_subgroup_padicInt_units : ∀ {l : ℕ} [Fact l.Prime] (Δ : Subgroup ℤ_[l]ˣ) [Finite Δ], l ≠ 2 → ∃ (e : ℕ) (a : Fin e → ℕ), e * Nat.card Δ = l - 1 ∧ (∀ τ, ¬ l ∣ a τ) ∧ (∀ τ τ', τ ≠ τ' → (a τ : ZMod l) ^ Nat.card Δ ≠ (a τ' : ZMod l) ^ Nat.card Δ) ∧ ∀ x : ZMod l, x ≠ 0 → ∃! p : Fin e × Δ, x = (a p.1 : ZMod l) * PadicInt.toZMod ((p.2 : ℤ_[l]ˣ) : ℤ_[l]) := by
  first | exact @GlobalTheory.exists_coset_representatives_of_finite_subgroup_padicInt_units | exact GlobalTheory.exists_coset_representatives_of_finite_subgroup_padicInt_units | (intros; apply GlobalTheory.exists_coset_representatives_of_finite_subgroup_padicInt_units <;> assumption)
