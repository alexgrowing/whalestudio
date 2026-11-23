import Formalism.StatementOC

open Finset

noncomputable section

namespace Formalism

def IsCMType {l : ℕ} (Φ : Finset (ZMod l)ˣ) : Prop := ∀ g : (ZMod l)ˣ, g ∈ Φ ↔ -g ∉ Φ

def dualType {l : ℕ} (Φ : Finset (ZMod l)ˣ) : Finset (ZMod l)ˣ :=
  insert 1 ((Φ.erase 1).image (fun g => -g))

def counts {l : ℕ} (Φ : Finset (ZMod l)ˣ) (σ : (ZMod l)ˣ) : Prop := σ ∉ Φ ∧ σ ≠ -1

def TwoTypes : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], 3 ≤ l → ∀ Φ : Finset (ZMod l)ˣ, IsCMType Φ → 1 ∈ Φ →
    IsCMType (dualType Φ) ∧ 1 ∈ dualType Φ ∧
    ∀ σ : (ZMod l)ˣ, σ ≠ 1 → σ ≠ -1 → (counts Φ σ ↔ ¬ counts (dualType Φ) σ)

open Classical in
def HalfTypes : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], 3 ≤ l → ∀ σ : (ZMod l)ˣ, σ ≠ 1 → σ ≠ -1 →
    2 * ((Finset.univ.filter (fun Φ : Finset (ZMod l)ˣ => IsCMType Φ ∧ 1 ∈ Φ ∧ counts Φ σ)).card)
      = (Finset.univ.filter (fun Φ : Finset (ZMod l)ˣ => IsCMType Φ ∧ 1 ∈ Φ)).card

open ArithmeticFunction Classical in

def WeightedVonMangoldtSumInClasses (l : ℕ) (Φ : Finset (ZMod l)ˣ) (a b : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 ⌊a / b⌋₊,
    if h : IsUnit (n : ZMod l) then
      (if counts Φ h.unit then Λ n * (a / n - b) else 0)
    else 0

def ForcedSumCM : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], 3 ≤ l → ∀ Φ : Finset (ZMod l)ˣ, IsCMType Φ → 1 ∈ Φ →
  ∀ a b : ℝ, 0 < a → 0 < b → b ≤ a →
    let R := b * Sz (a / b) - (WeightedVonMangoldtSumInClasses l Φ a b + WeightedVonMangoldtSumInClasses l (dualType Φ) a b)
    0 ≤ R ∧ R ≤ 3 * a / l * Real.log (a / b) * (1 + Real.log (a / b)) + a * Real.log l / (l - 1)

def ForcedSumIdentity : Prop :=
  ∀ a b : ℝ, 0 < b →
    b * Sz (a / b) = a * (Real.log (a / b) - 1 - Real.eulerMascheroniConstant) + b * Gz (a / b)

end Formalism
