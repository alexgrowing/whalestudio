import Formalism.SubspaceCounting.StatementB

namespace Formalism.G0

namespace QVandermondeP

theorem gb_zero_right (q n : ℕ) : gaussBinom q n 0 = 1 := by
  cases n <;> rfl

theorem gb_zero_succ (q k : ℕ) : gaussBinom q 0 (k + 1) = 0 := rfl

theorem gb_succ_succ (q n k : ℕ) :
    gaussBinom q (n + 1) (k + 1) = gaussBinom q n k + q ^ (k + 1) * gaussBinom q n (k + 1) :=
  rfl

theorem gb_eq_zero (q : ℕ) : ∀ n k : ℕ, n < k → gaussBinom q n k = 0
  | 0, 0, h => absurd h (lt_irrefl 0)
  | 0, _ + 1, _ => rfl
  | _ + 1, 0, h => absurd h (Nat.not_lt_zero _)
  | n + 1, k + 1, h => by
    rw [gb_succ_succ, gb_eq_zero q n k (by omega), gb_eq_zero q n (k + 1) (by omega)]
    simp

theorem form2 (q m : ℕ) : ∀ g n : ℕ, gaussBinom q (m + g) n =
    ∑ l ∈ Finset.range (n + 1),
      q ^ ((n - l) * (g - l)) * gaussBinom q m (n - l) * gaussBinom q g l := by
  intro g
  induction g with
  | zero =>
    intro n
    rw [Finset.sum_range_succ']
    simp [gb_zero_succ, gb_zero_right]
  | succ g ih =>
    intro n
    cases n with
    | zero => simp [gb_zero_right]
    | succ k =>
      show gaussBinom q ((m + g) + 1) (k + 1) = _
      rw [gb_succ_succ, ih k, ih (k + 1)]
      rw [Finset.sum_range_succ' _ (k + 1), Finset.sum_range_succ' _ (k + 1)]
      have h1 : ∀ l ∈ Finset.range (k + 1),
          q ^ ((k + 1 - (l + 1)) * (g + 1 - (l + 1))) * gaussBinom q m (k + 1 - (l + 1)) *
              gaussBinom q (g + 1) (l + 1) =
            q ^ ((k - l) * (g - l)) * gaussBinom q m (k - l) * gaussBinom q g l +
              q ^ (k + 1) * (q ^ ((k + 1 - (l + 1)) * (g - (l + 1))) *
                gaussBinom q m (k + 1 - (l + 1)) * gaussBinom q g (l + 1)) := by
        intro l hl
        have hl' : l ≤ k := by
          have := Finset.mem_range.mp hl
          omega
        rw [gb_succ_succ]
        simp only [Nat.add_sub_add_right]
        rcases Nat.lt_or_ge g (l + 1) with h | h
        · rw [gb_eq_zero q g (l + 1) h]
          ring
        · obtain ⟨a, rfl⟩ : ∃ a, k = l + a := ⟨k - l, by omega⟩
          obtain ⟨b, rfl⟩ : ∃ b, g = l + 1 + b := ⟨g - (l + 1), by omega⟩
          have e1 : l + a - l = a := by omega
          have e2 : l + 1 + b - l = b + 1 := by omega
          have e3 : l + 1 + b - (l + 1) = b := by omega
          rw [e1, e2, e3]
          ring
      rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib, mul_add, Finset.mul_sum]
      simp only [Nat.sub_zero, gb_zero_right]
      ring

theorem form1 (q m g n : ℕ) : gaussBinom q (m + g) n =
    ∑ l ∈ Finset.range (n + 1),
      q ^ (l * (m + l - n)) * gaussBinom q m (n - l) * gaussBinom q g l := by
  rw [Nat.add_comm m g, form2 q g m n]
  refine (Finset.sum_range_reflect _ _).symm.trans ?_
  apply Finset.sum_congr rfl
  intro l hl
  have hl' : l ≤ n := by
    have := Finset.mem_range.mp hl
    omega
  have e1 : n + 1 - 1 - l = n - l := by omega
  have e2 : n - (n - l) = l := by omega
  have e3 : m - (n - l) = m + l - n := by omega
  simp only [e1, e2, e3]
  ring

end QVandermondeP

theorem qVandermondeIdentity : QVandermonde := fun q m g n =>
  ⟨QVandermondeP.form1 q m g n, QVandermondeP.form2 q m g n⟩

end Formalism.G0
