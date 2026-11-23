import Mathlib

noncomputable section

namespace PI.LocMassTypW

open Matrix

def WCore : Prop :=
  ∀ (O : Type) [CommRing O] [IsLocalRing O] (n m : ℕ) (A0 A B0 B : Matrix (Fin n) (Fin m) O),
    (∃ L : Matrix (Fin m) (Fin n) O, L * A0 = 1) → (∃ L : Matrix (Fin m) (Fin n) O, L * A = 1) →
    (∃ L : Matrix (Fin m) (Fin n) O, L * B0 = 1) → (∃ L : Matrix (Fin m) (Fin n) O, L * B = 1) →
    A0ᵀ * B0 = Aᵀ * B →
    ∃ k : Matrix (Fin n) (Fin n) O, IsUnit k ∧ k * A0 = A ∧ kᵀ * B = B0

end PI.LocMassTypW
