import Mathlib

noncomputable def UpperTheory.Reformulated.B.Qf21.degLE :
    {κ R : Type} → [inst : CommRing R] → Finset κ → ℕ → MvPolynomial κ R → Prop :=
    fun {κ R : Type} [CommRing R] (W : Finset κ) (n : ℕ) (F : MvPolynomial κ R) ↦
      ∀ (β : κ →₀ ℕ), MvPolynomial.coeff β F ≠ (0 : R) → ∑ k ∈ W, (β : κ → ℕ) k ≤ n

theorem UpperTheory.Reformulated.B.Qf21.degLE_sum.{u_1} :
    ∀ {κ R : Type} [inst : CommRing R] {α : Type u_1} {W : Finset κ} {n : ℕ} (s : Finset α) (F : α → MvPolynomial κ R),
      (∀ a ∈ s, UpperTheory.Reformulated.B.Qf21.degLE W n (F a)) → UpperTheory.Reformulated.B.Qf21.degLE W n (∑ a ∈ s, F a) := by
  intro κ R _ α W n s F h β hβ
  rw [MvPolynomial.coeff_sum] at hβ
  obtain ⟨a, ha, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hβ
  exact h a ha β hne
