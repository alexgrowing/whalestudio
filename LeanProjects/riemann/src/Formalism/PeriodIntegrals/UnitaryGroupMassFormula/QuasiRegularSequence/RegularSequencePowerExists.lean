import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.QuasiRegularSequence.StepPowMem

universe u

namespace PI.RSQR

open MvPolynomial

section SlopeTestRemainingChoices

variable {R : Type u} [CommRing R] {n : ℕ}

def lowSet (n i : ℕ) : Set (Fin n) := {j | (j : ℕ) < i}

theorem isHom_iff {σ : Type*} {F : MvPolynomial σ R} {k : ℕ} :
    F.IsHomogeneous k ↔ ∀ d, F.coeff d ≠ 0 → Finsupp.degree d = k := by
  rw [Finsupp.degree_eq_weight_one]; rfl

theorem C_mem_sup {σ : Type*} {s : Set σ} (c : R) : (C c : MvPolynomial σ R) ∈ supported R s := by
  rw [← MvPolynomial.algebraMap_eq]; exact (supported R s).algebraMap_mem c

def T (x : Fin n → R) (s : Set (Fin n)) (k : ℕ) (J : Ideal R) : Ideal R where
  carrier := {a | ∃ F : MvPolynomial (Fin n) R, F.IsHomogeneous k ∧ F ∈ supported R s ∧
    (∀ m, F.coeff m ∈ J) ∧ eval x F = a}
  add_mem' := by
    rintro a b ⟨F, h1, h2, h3, rfl⟩ ⟨G, g1, g2, g3, rfl⟩
    exact ⟨F + G, h1.add g1, add_mem h2 g2,
      fun m => by rw [coeff_add]; exact add_mem (h3 m) (g3 m), by simp⟩
  zero_mem' := ⟨0, isHom_iff.2 (fun d hd => by simp at hd), zero_mem _, fun m => by simp, by simp⟩
  smul_mem' := by
    rintro c a ⟨F, h1, h2, h3, rfl⟩
    exact ⟨C c * F, h1.C_mul c, mul_mem (C_mem_sup c) h2,
      fun m => by rw [coeff_C_mul]; exact J.mul_mem_left c (h3 m), by simp⟩

end SlopeTestRemainingChoices

end PI.RSQR
