import Mathlib

namespace GlobalTheory

def chainEdge (k : ℕ) {r : ℕ} (i j : Fin r) : Prop := j.val = i.val + 1 ∧ i.val + 1 ≠ k

instance (k : ℕ) {r : ℕ} : DecidableRel (chainEdge k (r := r)) := fun i j =>
  inferInstanceAs (Decidable (j.val = i.val + 1 ∧ i.val + 1 ≠ k))

example : ¬ chainEdge 1 (0 : Fin 3) 1 ∧ chainEdge 1 (1 : Fin 3) 2 := by decide

end GlobalTheory
