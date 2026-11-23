import Mathlib

namespace PI.MirabIndex

def IsMirab {k : Type} [Field k] {n : ℕ} (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k) : Prop :=
  ∀ j, h (Fin.last n) j = if j = Fin.last n then 1 else 0

def IsUniU {k : Type} [Field k] {n : ℕ} (u : Matrix (Fin (n + 1)) (Fin (n + 1)) k) : Prop :=
  (∀ i, u i i = 1) ∧ ∀ i j, j < i → u i j = 0

def MirabIndex : Prop :=
  ∀ (k : Type) [Field k] [Fintype k] (n : ℕ),
    Nat.card {h : GL (Fin (n + 1)) k // IsMirab (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k)} =
      Nat.card {u : GL (Fin (n + 1)) k // IsUniU (u : Matrix (Fin (n + 1)) (Fin (n + 1)) k)} *
        ∏ i ∈ Finset.Ico 1 (n + 1), (Fintype.card k ^ i - 1)

end PI.MirabIndex
