import Mathlib

noncomputable def UpperTheory.Reformulated.B.Qf22.biHom :
    {K ι κ : Type} → [inst : Field K] → ℕ → MvPolynomial κ (MvPolynomial ι K) → Prop :=
    fun {K ι κ : Type} [Field K] (d : ℕ) (F : MvPolynomial κ (MvPolynomial ι K)) ↦
      ∀ (β : κ →₀ ℕ) (n : ι →₀ ℕ),
        MvPolynomial.coeff n (MvPolynomial.coeff β F) ≠ (0 : K) →
          (Finsupp.degree : (ι →₀ ℕ) → ℕ) n + (Finsupp.degree : (κ →₀ ℕ) → ℕ) β = d

theorem UpperTheory.Reformulated.B.Qf22.biHom_sum.{u_1} :
    ∀ {K ι κ : Type} [inst : Field K] [Fintype κ] {α : Type u_1} {d : ℕ} (s : Finset α)
      (F : α → MvPolynomial κ (MvPolynomial ι K)),
      (∀ a ∈ s, UpperTheory.Reformulated.B.Qf22.biHom d (F a)) → UpperTheory.Reformulated.B.Qf22.biHom d (∑ a ∈ s, F a) := by
  intro K ι κ _ _ α d s F h β n hne
  rw [MvPolynomial.coeff_sum, MvPolynomial.coeff_sum] at hne
  obtain ⟨a, ha, hna⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  exact h a ha β n hna
