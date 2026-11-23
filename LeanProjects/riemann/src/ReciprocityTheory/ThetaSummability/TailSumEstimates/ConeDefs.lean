import Mathlib

namespace ReciprocityTheory.ThetaSummability.Est

open Finset

def gap {r : ℕ} (x : Fin r → ℝ) (k : Fin r) : ℝ :=
  x k - (if h : k.val + 1 < r then x ⟨k.val + 1, h⟩ else 0)

def tailSum {r : ℕ} (y : Fin r → ℝ) (k : Fin r) : ℝ :=
  ∑ j ∈ univ.filter (fun j : Fin r => k ≤ j), y j

def partialSum {r : ℕ} (s : Fin r → ℝ) (k : Fin r) : ℝ :=
  ∑ i ∈ univ.filter (fun i : Fin r => i ≤ k), s i

def logCone (r : ℕ) (c : ℝ) : Set (Fin r → ℝ) :=
  {x | ∀ k, c ≤ gap x k}

def lowerBox (r : ℕ) (c : ℝ) : Set (Fin r → ℝ) :=
  Set.pi Set.univ (fun _ => Set.Ici c)

def multCone (r : ℕ) (c : ℝ) : Set (Fin r → ℝ) :=
  {t | ∀ k : Fin r, (if h : k.val + 1 < r then c * t ⟨k.val + 1, h⟩ else c) ≤ t k}

example : (![2, 1] : Fin 2 → ℝ) ∈ logCone 2 1 := by
  intro k
  fin_cases k <;> simp [gap] <;> norm_num

example : (![4, 2] : Fin 2 → ℝ) ∈ multCone 2 2 := by
  intro k
  fin_cases k <;> simp <;> norm_num

example : partialSum (![-1, -1] : Fin 2 → ℝ) 1 = -2 := by
  simp [partialSum, Finset.sum_filter, Fin.sum_univ_two]
  norm_num

end ReciprocityTheory.ThetaSummability.Est
