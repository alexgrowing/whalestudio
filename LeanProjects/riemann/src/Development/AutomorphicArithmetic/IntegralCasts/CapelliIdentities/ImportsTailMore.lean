import Mathlib

theorem UpperTheory.Reformulated.B.Yra8.main.{u_1, u_2} :
    ∀ {R : Type u_1} {ι : Type u_2} [inst : CommRing R] (s : Finset ι) (e : ι → ℕ) (g : ι → Polynomial R) (c : ι → R),
      (∀ (i : ι), (g i).natDegree ≤ (1 : ℕ)) →
        (∀ (i : ι), (g i).coeff (1 : ℕ) = c i) →
          (∏ i ∈ s, g i ^ e i).natDegree ≤ ∑ i ∈ s, e i ∧ (∏ i ∈ s, g i ^ e i).coeff (∑ i ∈ s, e i) = ∏ i ∈ s, c i ^ e i := by
  intro R ι _ s e g c hd hc
  classical
  have hp : ∀ i, (g i ^ e i).natDegree ≤ e i ∧ (g i ^ e i).coeff (e i) = c i ^ e i := by
    intro i
    refine ⟨?_, ?_⟩
    · calc (g i ^ e i).natDegree ≤ e i * (g i).natDegree := Polynomial.natDegree_pow_le
        _ ≤ e i * 1 := Nat.mul_le_mul_left _ (hd i)
        _ = e i := by simp
    · have := Polynomial.coeff_pow_of_natDegree_le (m := e i) (hd i)
      simpa [hc i] using this
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, Finset.prod_insert ha]
    refine ⟨?_, ?_⟩
    · exact (Polynomial.natDegree_mul_le).trans (Nat.add_le_add (hp a).1 ih.1)
    · rw [Polynomial.coeff_mul_add_eq_of_natDegree_le (hp a).1 ih.1, (hp a).2, ih.2]
