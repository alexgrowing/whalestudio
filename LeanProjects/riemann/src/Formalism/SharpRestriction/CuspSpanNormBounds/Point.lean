import Mathlib

namespace Formalism.MainNotions.S

def ptEntry {K : Type*} [Zero K] : List (K × ℕ) → ℕ → ℕ → K
  | [], _, _ => 0
  | (t, s) :: bs, i, j =>
    if i < s ∧ j < s then (if i + j + 1 = s then t else 0)
    else if s ≤ i ∧ s ≤ j then ptEntry bs (i - s) (j - s) else 0

def Point (K : Type*) [Zero K] (i : ℕ) : Type _ :=
  {bs : List (K × ℕ) // (∀ b ∈ bs, b.1 ≠ 0 ∧ 1 ≤ b.2) ∧ (bs.map Prod.snd).sum = i}

def ptMat {K : Type*} [Zero K] {i : ℕ} (p : Point K i) : Matrix (Fin i) (Fin i) K :=
  fun a b => ptEntry p.1 a.val b.val

end Formalism.MainNotions.S
