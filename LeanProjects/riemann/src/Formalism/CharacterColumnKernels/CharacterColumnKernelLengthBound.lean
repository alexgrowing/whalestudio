import Formalism.CharacterColumnKernels.Statement

noncomputable section

namespace Formalism.NG

def characterColumnKernelLengthBound : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (s₀ : ℕ), 1 ≤ s₀ → (l = 2 → 2 ≤ s₀) →
    ∀ (x : ℤ), (l : ℤ) ^ s₀ ∣ x - 1 → ¬ (l : ℤ) ^ (s₀ + 1) ∣ x - 1 →
    ∀ a b : ℕ, a < b → padicValInt l (x ^ b - x ^ a) = s₀ + padicValNat l (b - a)

def characterColumnKernelBlockBound : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (s₀ : ℕ), 1 ≤ s₀ → (l = 2 → 2 ≤ s₀) →
    ∀ (x : ℤ), (l : ℤ) ^ s₀ ∣ x - 1 → ¬ (l : ℤ) ^ (s₀ + 1) ∣ x - 1 →
    ∀ (u : ℤ), ¬ (l : ℤ) ∣ u → ∀ (w t : ℕ),
      padicValInt l (delta (fun i : Fin (t + 1) => u * x ^ (w + (i : ℕ)))) =
        t * s₀ + padicValNat l t.factorial

def characterColumnKernelLengthEquality : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (s₀ : ℕ), 1 ≤ s₀ → (l = 2 → 2 ≤ s₀) →
    ∀ (x : ℤ), (l : ℤ) ^ s₀ ∣ x - 1 → ¬ (l : ℤ) ^ (s₀ + 1) ∣ x - 1 →
    ∀ (u : ℤ), ¬ (l : ℤ) ∣ u → ∀ (w t : ℕ),
      padicValInt l (delta (fun i : Fin (t + 1) => u * x ^ (w + t - (i : ℕ)))) =
        t * s₀ + padicValNat l t.factorial

end Formalism.NG
