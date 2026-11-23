import Mathlib

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem exists_max_ratio_cleared :
    ∀ (ι : Type) [Fintype ι] [Nonempty ι] (n : ι → ℤ) (m : ι → ℕ), (∀ i, 0 < m i) →
      ∃ (M : ℕ) (a : ℤ) (i₀ : ι), 0 < M ∧ (∀ i, (M : ℤ) * n i ≤ a * m i) ∧
        (M : ℤ) * n i₀ = a * m i₀ := by
  intro ι _ _ n m hm
  obtain ⟨i₀, -, hi₀⟩ := Finset.exists_max_image Finset.univ (fun i => (n i : ℚ) / m i) Finset.univ_nonempty
  refine ⟨m i₀, n i₀, i₀, hm i₀, fun i => ?_, mul_comm _ _⟩
  have h := hi₀ i (Finset.mem_univ i)
  have hmi : (0 : ℚ) < m i := by exact_mod_cast hm i
  have hm0 : (0 : ℚ) < m i₀ := by exact_mod_cast hm i₀
  rw [div_le_div_iff₀ hmi hm0] at h
  have hq : (m i₀ : ℚ) * n i ≤ n i₀ * (m i : ℚ) := by linarith
  exact_mod_cast hq

end GlobalTheory.CompanionTheory.Ar.Flat
