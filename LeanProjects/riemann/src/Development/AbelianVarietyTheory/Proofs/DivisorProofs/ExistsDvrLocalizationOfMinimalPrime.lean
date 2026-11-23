import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDivOfCenterHeightLeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsMoreTail
open Polynomial

namespace GlobalTheory

theorem exists_dvr_localization_of_minimal_prime : ∀ {κ : Type} [Field κ] (R : Subring κ)
    [IsNoetherianRing R] [IsIntegrallyClosed R] [IsFractionRing R κ] (Q : Ideal R) [Q.IsPrime],
    Q ≠ ⊥ → (∀ p : Ideal R, p.IsPrime → p ≠ ⊥ → p ≤ Q → p = Q) →
    ∃ W : ValuationSubring κ, IsDiscreteValuationRing W ∧ (∀ r : R, (r : κ) ∈ W) ∧
      (∀ r : R, r ∉ Q → (r : κ)⁻¹ ∈ W) ∧ (∀ r : R, r ∈ Q → r ≠ 0 → (r : κ)⁻¹ ∉ W) ∧
      (∀ w ∈ W, ∃ b s : R, s ∉ Q ∧ w = b / s) := by
  first
  | exact @_root_.GlobalTheory.AuxiliaryLemmaSecond.main
  | exact _root_.GlobalTheory.AuxiliaryLemmaSecond.main
  | (apply _root_.GlobalTheory.AuxiliaryLemmaSecond.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.AuxiliaryLemmaSecond.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.AuxiliaryLemmaSecond.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.AuxiliaryLemmaSecond.main ..)

end GlobalTheory
