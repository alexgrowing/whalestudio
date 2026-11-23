import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitSumsOverConjugacyClasses

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orbit_sum_conj_classes : ∀ {Γ Y : Type} [Group Γ] [MulAction Γ Y] (F : Y → Γ → ℂ), (∀ (η : Γ) (y : Y) (γ : Γ), F (η • y) (η * γ * η⁻¹) = F y γ) → (∀ y : Y, (Function.support (F y)).Finite) → {o : MulAction.orbitRel.Quotient Γ Y | ∃ γ, F (Quotient.out o) γ ≠ 0}.Finite → ∑ᶠ o : MulAction.orbitRel.Quotient Γ Y, ((Nat.card (MulAction.stabilizer Γ (Quotient.out o)) : ℕ) : ℂ)⁻¹ * ∑ᶠ γ : Γ, F (Quotient.out o) γ = ∑ᶠ c : ConjClasses Γ, ∑ᶠ o : MulAction.orbitRel.Quotient (Subgroup.centralizer {Quotient.out c}) Y, ((Nat.card (MulAction.stabilizer Γ (Quotient.out o) ⊓ Subgroup.centralizer {Quotient.out c} : Subgroup Γ) : ℕ) : ℂ)⁻¹ * F (Quotient.out o) (Quotient.out c) := by
  first | (exact @GlobalTheory.OrbitUnfold.finsum_orbits_eq_finsum_conjClasses_of_any_stabilizer) | (exact GlobalTheory.OrbitUnfold.finsum_orbits_eq_finsum_conjClasses_of_any_stabilizer) | (intros; apply GlobalTheory.OrbitUnfold.finsum_orbits_eq_finsum_conjClasses_of_any_stabilizer  <;> assumption)
