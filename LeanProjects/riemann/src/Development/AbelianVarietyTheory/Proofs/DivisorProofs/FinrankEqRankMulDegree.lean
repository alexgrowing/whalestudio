import Mathlib
open NumberField

namespace GlobalTheory

theorem smul_eq_zero_of_ringOfIntegers {F : Type} [Field F] [NumberField F] {M : Type}
    [AddCommGroup M] [Module (𝓞 F) M] [IsAddTorsionFree M] {a : 𝓞 F} (ha : a ≠ 0) {m : M}
    (h : a • m = 0) : m = 0 := by
  have hmem := Ideal.absNorm_mem (Ideal.span {a})
  rw [Ideal.mem_span_singleton] at hmem
  obtain ⟨b, hb⟩ := hmem
  have hn : Ideal.absNorm (Ideal.span {a}) ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact ha
  have h2 : (Ideal.absNorm (Ideal.span {a})) • m = 0 := by
    rw [← Nat.cast_smul_eq_nsmul (𝓞 F), hb, mul_comm, mul_smul, h, smul_zero]
  exact nsmul_right_injective hn (by simpa using h2)

theorem finrank_int_eq_of_span_smul (F : Type) [Field F] [NumberField F] (M : Type) [AddCommGroup M]
    [Module (𝓞 F) M] [Module.Finite ℤ M] [IsAddTorsionFree M] (r : ℕ) (x : Fin r → M)
    (hx : LinearIndependent (𝓞 F) x) (c : 𝓞 F) (hc : c ≠ 0)
    (hspan : ∀ m : M, c • m ∈ Submodule.span (𝓞 F) (Set.range x)) :
    Module.finrank ℤ M = r * Module.finrank ℚ F := by
  let φ : (Fin r → 𝓞 F) →ₗ[ℤ] M := (Fintype.linearCombination (𝓞 F) x).restrictScalars ℤ
  have hφ : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro g hg
    funext i
    exact Fintype.linearIndependent_iff.mp hx g (by simpa [φ, Fintype.linearCombination_apply] using hg) i
  have hdom : Module.finrank ℤ (Fin r → 𝓞 F) = r * Module.finrank ℚ F := by
    rw [Module.finrank_pi_fintype]
    simp [RingOfIntegers.rank]
  let ψ : M →ₗ[ℤ] M := (LinearMap.lsmul (𝓞 F) M c).restrictScalars ℤ
  have hψ : Function.Injective ψ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro m hm
    exact smul_eq_zero_of_ringOfIntegers hc (by simpa [ψ] using hm)
  have hrange : ∀ m, ψ m ∈ LinearMap.range φ := by
    intro m
    obtain ⟨g, hg⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 F)).mp (hspan m)
    exact ⟨g, by simpa [φ, ψ, Fintype.linearCombination_apply] using hg⟩
  let ψ' : M →ₗ[ℤ] LinearMap.range φ := ψ.codRestrict _ hrange
  have hψ' : Function.Injective ψ' := by
    intro a b hab
    apply hψ
    simpa [ψ'] using congrArg Subtype.val hab
  have h1 : Module.finrank ℤ (Fin r → 𝓞 F) ≤ Module.finrank ℤ M :=
    LinearMap.finrank_le_finrank_of_injective hφ
  have hfin : Module.Finite ℤ (LinearMap.range φ) := inferInstance
  have h2 : Module.finrank ℤ M ≤ Module.finrank ℤ (LinearMap.range φ) :=
    LinearMap.finrank_le_finrank_of_injective hψ'
  rw [LinearMap.finrank_range_of_inj hφ] at h2
  omega

end GlobalTheory
