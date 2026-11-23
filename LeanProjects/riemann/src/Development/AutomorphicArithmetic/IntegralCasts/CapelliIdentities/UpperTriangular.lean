import Mathlib

noncomputable def UpperTheory.Reformulated.B.UpperTriangular.UT :
    {L : Type} → [Field L] → {n : ℕ} → Matrix (Fin n) (Fin n) L → Prop :=
  fun {_} _ {n} A => (∀ i j : Fin n, j < i → A i j = 0) ∧ ∀ i : Fin n, A i i = 1
