import Mathlib
import Formalism.SubspaceCounting.GoodOrbitIntervalTileCondition

noncomputable section

open Finset

namespace UpperTheory.BernoulliSumsFrobeniusOrbits

def pw {α : Type} [Fintype α] [DecidableEq α] (p : α → ℝ) (T : Finset α) : ℝ :=
  (∏ a ∈ T, p a) * ∏ a ∈ univ \ T, (1 - p a)

def exP (p : ℕ → ℝ) (S : Finset ℕ) (f : Finset ℕ → ℝ) : ℝ :=
  ∑ T ∈ S.powerset, (∏ a ∈ T, p a) * (∏ a ∈ S \ T, (1 - p a)) * f T

open Classical in

def ind (q : Prop) : ℝ := if q then 1 else 0

def markedLow (δ : ℝ) (r u : ℕ) : ℝ :=
  ((1 - δ) ^ u) ^ (3 * r + 1) * (((u / 2 : ℕ) : ℝ) * (3 / 4 * δ) * (1 - δ) ^ (u - 1)) ^ (3 * r)

def hE (eps : ℝ) : ℝ := 2 + 8 * eps

def KE (eps : ℝ) : ℕ := ⌈8 * (hE eps + 2) / eps⌉₊

def rE (eps : ℝ) : ℕ := KE eps + 1

def dE (eps x : ℝ) : ℝ := x ^ (-(eps / 8))

end UpperTheory.BernoulliSumsFrobeniusOrbits

end
