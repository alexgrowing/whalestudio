import Mathlib
import Formalism.PadicSubsetSums.CentralIdempotents.EigenbasisOfDistinctRoots

open Finset

noncomputable section

namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

def StretchedExponentialDominance : Prop :=
  ∀ C ε : ℝ, 0 < ε → ∀ᶠ x : ℝ in Filter.atTop,
    x ^ C * Real.exp (-x ^ (ε / 6)) ≤ 1 / 20 * Real.exp (-x ^ (ε / 7))

def SubsetSumCountReformulated : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (deg : ι → ℕ) (i : ℕ), (∀ c, 1 ≤ deg c) →
    ((Finset.univ : Finset ι).powerset.filter (fun I => ∑ c ∈ I, deg c = i)).card
      ≤ (∑ c, deg c).choose i

def TorusCountBounds : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (deg : ι → ℕ) (g k : ℕ) (c : ℕ → ℝ) (n : ℝ),
    (∀ x, 1 ≤ deg x) → 1 ≤ g → 1 ≤ k →
    (∀ i, c i = (((Finset.univ : Finset ι).powerset.filter
      (fun I => ∑ x ∈ I, deg x = i)).card : ℝ)) →
    n = (∑ i ∈ Finset.range k, c i * ((g : ℝ) ^ (k - i) - (g : ℝ) ^ (k - i - 1))) + c k →
    (g : ℝ) ^ k - (g : ℝ) ^ (k - 1) ≤ n ∧
      n ≤ (g : ℝ) ^ k * (1 + 1 / (g : ℝ)) ^ (∑ x, deg x)

def TorusWeightArithmetic : Prop :=
  ∀ (d : Multiset ℕ) (g k : ℕ) (n : ℝ), (∀ x ∈ d, 1 ≤ x) → 2 ≤ g → 1 ≤ k → k + 1 ≤ d.sum →
    2 * d.sum ≤ g → (g : ℝ) ^ k - (g : ℝ) ^ (k - 1) ≤ n →
    n ≤ (g : ℝ) ^ k * (1 + 1 / (g : ℝ)) ^ d.sum →
    (1 - 1 / (g : ℝ)) / (g : ℝ) ^ d.sum ≤
        n / ((g : ℝ) ^ k * (d.map (fun x => (g : ℝ) ^ x - 1)).prod) ∧
      n / ((g : ℝ) ^ k * (d.map (fun x => (g : ℝ) ^ x - 1)).prod) ≤
        (1 + 6 * (d.sum : ℝ) / g) / (g : ℝ) ^ d.sum

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
