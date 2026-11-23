import Mathlib

namespace Formalism.SL.NC

open Finset

def NormCount : Prop :=
  ∀ (K L : Type) [Field K] [Fintype K] [DecidableEq K] [Field L] [Fintype L] [Algebra K L],
    Module.finrank K L = 2 →
    ∀ (n : ℕ) (c : K),
      |((univ.filter (fun y : Fin n → L => ∑ i, Algebra.norm K (y i) = c)).card : ℝ)
          - (Fintype.card L : ℝ) ^ n / (Fintype.card K : ℝ)|
        ≤ (1 - 1 / (Fintype.card K : ℝ)) * (Fintype.card K : ℝ) ^ n

def NormCharMean : Prop :=
  ∀ (K L : Type) [Field K] [Fintype K] [DecidableEq K] [Field L] [Fintype L] [Algebra K L],
    Module.finrank K L = 2 →
    ∀ (ψ : AddChar K ℂ), (∃ c, ψ c ≠ 1) →
    ∀ (n : ℕ) (ℓ : Fin n → L), ℓ ≠ 0 →
      ‖∑ y ∈ univ.filter (fun y : Fin n → L => ∑ i, Algebra.norm K (y i) = 0),
          ψ (∑ i, Algebra.trace K L (ℓ i * y i))‖
        ≤ (1 - 1 / (Fintype.card K : ℝ)) * (Fintype.card K : ℝ) ^ n

end Formalism.SL.NC
