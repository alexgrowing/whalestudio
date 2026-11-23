import Mathlib
import Formalism.RankGapBounds.CloudMinFalse

noncomputable section

open Finset

namespace Formalism.CohomologicalDescent

def lamOf (N : ℕ) (U : ℕ → ℤ) (i : ℕ) : ℤ := U i - ((N : ℤ) - 1 - (i : ℤ))

def CrossTerm : Prop :=
  ∀ (l N h a : ℕ) (U : ℕ → ℤ), l.Prime → (∀ i j, i < j → j < N → U j < U i) →
    (∀ i < N, 0 ≤ U i ∧ U i ≤ (h : ℤ)) → a ≤ N →
    ∑ i ∈ Finset.range a, ∑ j ∈ Finset.Ico a N,
      (Nat.log l (((j : ℤ) - (i : ℤ) + lamOf N U 0 - lamOf N U (N - 1)).toNat) -
        padicValInt l (lamOf N U i - lamOf N U j + (j : ℤ) - (i : ℤ))) ≤
      a * (N - a) * Nat.log l (2 * h + N)

def ExpStopH : Prop :=
  ∀ (l N h : ℕ) (U : Fin N → ℤ), l.Prime → StrictAnti U → (∀ i, 0 ≤ U i ∧ U i ≤ (h : ℤ)) →
    h < l → Formalism.RankGapBounds.JumpSetsAlt.eExp U l = 0

def ParamsWindow : Prop :=
  ∀ (b h l t : ℕ) (lstar h0 η : ℝ), 1 ≤ lstar → (h : ℝ) ≤ 2 * b → lstar < (l : ℝ) →
    12 * b / lstar + 2 * t + 8 ≤ h0 → 2 * η + t + 8 * b / lstar + 7 < lstar → 0 ≤ η →
    ((h / (l - 1) : ℕ) : ℝ) ≤ h0 / 4 - t / 2 - 2 ∧ η + t + ((h / (l - 1) : ℕ) : ℝ) < l ∧
      0 < h0 / 2 - 1 - t / 2 - ((h / (l - 1) : ℕ) : ℝ)

end Formalism.CohomologicalDescent
