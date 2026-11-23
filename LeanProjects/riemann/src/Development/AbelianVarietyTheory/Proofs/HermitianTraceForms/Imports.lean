import ReciprocityTheory.SemistableReduction.TorsionNonvanishStatement

namespace GlobalTheory.IntSmulIntegral

open NumberField

theorem exists_int_mul_integral {K : Type} [Field K] [NumberField K] (a : K) :
    ∃ (m : ℤ) (z : 𝓞 K), m ≠ 0 ∧ (z : K) = m • a := by
  have : Algebra.IsAlgebraic ℤ ℚ := IsLocalization.isAlgebraic ℚ (nonZeroDivisors ℤ)
  have : Algebra.IsAlgebraic ℚ K := Algebra.IsAlgebraic.of_finite ℚ K
  obtain ⟨m, hm, hint⟩ := ((Algebra.IsAlgebraic.isAlgebraic a : IsAlgebraic ℚ a).restrictScalars ℤ).exists_integral_multiple
  exact ⟨m, ⟨m • a, hint⟩, hm, rfl⟩

theorem exists_int_smul_mem {r : ℕ} {K : Type} [Field K] [NumberField K]
    {Λ : Submodule (𝓞 K) (Fin r → K)} (hΛ : ReciprocityTheory.MultiplicativeHeights.IsLattice Λ) (v : Fin r → K) :
    ∃ n : ℤ, n ≠ 0 ∧ n • v ∈ Λ := by
  have hv : v ∈ Submodule.span K (Λ : Set (Fin r → K)) := hΛ.2 ▸ Submodule.mem_top
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by rwa [one_smul]⟩
  | zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact Λ.zero_mem⟩
  | add x y _ _ hx hy =>
    obtain ⟨n₁, hn₁, h₁⟩ := hx
    obtain ⟨n₂, hn₂, h₂⟩ := hy
    refine ⟨n₁ * n₂, mul_ne_zero hn₁ hn₂, ?_⟩
    rw [smul_add, mul_comm, mul_smul, mul_comm, mul_smul]
    exact Λ.add_mem (Λ.toAddSubgroup.zsmul_mem h₁ n₂) (Λ.toAddSubgroup.zsmul_mem h₂ n₁)
  | smul c x _ hx =>
    obtain ⟨n, hn, h⟩ := hx
    obtain ⟨m, z, hm, hz⟩ := exists_int_mul_integral c
    refine ⟨n * m, mul_ne_zero hn hm, ?_⟩

    have e : (n * m) • (c • x) = z • (n • x) := by
      rw [mul_smul, ← smul_assoc m c x, ← hz, smul_comm]
      rfl
    rw [e]
    exact Λ.smul_mem z h

end GlobalTheory.IntSmulIntegral
