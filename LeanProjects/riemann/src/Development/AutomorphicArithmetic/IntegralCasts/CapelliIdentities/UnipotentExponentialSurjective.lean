import Mathlib

private theorem exp_second_order {A : Type} [CommRing A] [Algebra ℚ A] {y : A}
    (hy : IsNilpotent y) : ∃ d : A, IsNilpotent.exp y = 1 + y + y ^ 2 * d := by
  obtain ⟨k, hk⟩ := hy
  have h2 : y ^ (k + 2) = 0 := by rw [pow_add, hk, zero_mul]
  refine ⟨∑ i ∈ Finset.range k, (((i + 2).factorial : ℚ)⁻¹) • y ^ i, ?_⟩
  rw [IsNilpotent.exp_eq_sum h2, Finset.sum_range_succ', Finset.sum_range_succ', Finset.mul_sum]
  have h : ∀ i ∈ Finset.range k, (((i + 1 + 1).factorial : ℚ)⁻¹) • y ^ (i + 1 + 1)
      = y ^ 2 * ((((i + 2).factorial : ℚ)⁻¹) • y ^ i) := by
    intro i _
    rw [mul_smul_comm, ← pow_add, add_comm 2 i]
  rw [Finset.sum_congr rfl h]
  simp only [zero_add, Nat.factorial_one, Nat.factorial_zero, Nat.cast_one, inv_one, one_smul,
    pow_one, pow_zero]
  ring

private theorem exp_approx {A : Type} [CommRing A] [Algebra ℚ A] {n : A}
    (hn : IsNilpotent n) (k : ℕ) :
    ∃ x c : A, IsNilpotent x ∧ IsNilpotent.exp x = 1 + n + n ^ (k + 1) * c := by
  induction k with
  | zero => exact ⟨0, -1, IsNilpotent.zero, by rw [IsNilpotent.exp_zero]; ring⟩
  | succ k ih =>
    obtain ⟨x, c, hx, he⟩ := ih
    have hy : IsNilpotent (n * (-(n ^ k * c))) :=
      (Commute.all _ _).isNilpotent_mul_right hn
    obtain ⟨d, hd⟩ := exp_second_order hy
    refine ⟨x + n * (-(n ^ k * c)),
      -c - n ^ k * c ^ 2 + (1 + n + n ^ (k + 1) * c) * (n ^ k * c ^ 2 * d),
      (Commute.all _ _).isNilpotent_add hx hy, ?_⟩
    rw [IsNilpotent.exp_add_of_commute (Commute.all _ _) hx hy, he, hd]
    ring

theorem UpperTheory.Reformulated.B.UnipotentExponentialSurjective.ul_exp_onto :
    ∀ {A : Type} [inst : CommRing A] [inst_1 : Algebra ℚ A] {n : A},
    IsNilpotent n → ∃ (x : A), IsNilpotent x ∧ IsNilpotent.exp x = (1 : A) + n := by
  intro A _ _ n hn
  obtain ⟨k, hk⟩ := id hn
  obtain ⟨x, c, hx, he⟩ := exp_approx hn k
  exact ⟨x, hx, by rw [he, pow_succ, hk, zero_mul, zero_mul, add_zero]⟩
