import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.Splits
open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R

namespace GlobalTheory.CompanionTheory.DivPow

theorem exists_gamma {S : Type} [CommRing S] (I : Ideal S) (z : S)
    (h : ∀ k : ℕ, k ≠ 0 → ∃ y ∈ I, (k.factorial : S) * y = z ^ k) :
    ∃ γ : ℕ → S, (∀ i, i ≠ 0 → γ i ∈ I) ∧ ∀ i, (i.factorial : S) * γ i = z ^ i := by
  classical
  refine ⟨fun i => if hi : i = 0 then 1 else (h i hi).choose, ?_, ?_⟩
  · intro i hi
    simpa [hi] using (h i hi).choose_spec.1
  · intro i
    by_cases hi : i = 0
    · subst hi
      simp
    · simpa [hi] using (h i hi).choose_spec.2

theorem pdI_span : ∀ {S : Type} [CommRing S], TF S → ∀ s : Set S,
    (∀ x ∈ s, ∀ k : ℕ, k ≠ 0 → ∃ y ∈ Ideal.span s, (k.factorial : S) * y = x ^ k) →
    PdI (Ideal.span s) := by
  intro S _ _ s h x hx
  induction hx using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero =>
    intro k hk
    exact ⟨0, Ideal.zero_mem _, by simp [zero_pow hk]⟩
  | smul a x _ ih =>
    intro k hk
    obtain ⟨y, hy, e⟩ := ih k hk
    refine ⟨a ^ k * y, Ideal.mul_mem_left _ _ hy, ?_⟩
    rw [smul_eq_mul, mul_pow, ← e]
    ring
  | add x x' _ _ ih ih' =>
    intro k hk
    obtain ⟨γ, hγ, e⟩ := exists_gamma _ x ih
    obtain ⟨γ', hγ', e'⟩ := exists_gamma _ x' ih'
    refine ⟨∑ p ∈ Finset.HasAntidiagonal.antidiagonal k, γ p.1 * γ' p.2, ?_, ?_⟩
    · refine Ideal.sum_mem _ ?_
      rintro ⟨i, j⟩ hij
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hij
      by_cases hi : i = 0
      · have hj : j ≠ 0 := by
          rintro rfl
          exact hk (by omega)
        exact Ideal.mul_mem_left _ _ (hγ' j hj)
      · exact Ideal.mul_mem_right _ _ (hγ i hi)
    · rw [Finset.mul_sum, (Commute.all x x').add_pow']
      refine Finset.sum_congr rfl ?_
      rintro ⟨i, j⟩ hij
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hij
      subst hij
      rw [← e i, ← e' j, nsmul_eq_mul, Nat.choose_symm_add, ← Nat.add_choose_mul_factorial_mul_factorial i j]
      push_cast
      ring

end GlobalTheory.CompanionTheory.DivPow
