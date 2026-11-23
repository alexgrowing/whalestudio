import Mathlib

namespace GroundTheory.Variant₂.N1

open NumberField

theorem exists_smul_mem_of_span_eq_top_alt {K : Type*} [Field K] [NumberField K] {n : ℕ}
    (Λ : Submodule (𝓞 K) (Fin n → K))
    (hΛ : Submodule.span K (Λ : Set (Fin n → K)) = ⊤) (v : Fin n → K) :
    ∃ a : 𝓞 K, a ≠ 0 ∧ a • v ∈ Λ := by
  have hv : v ∈ Submodule.span K (Λ : Set (Fin n → K)) := hΛ ▸ Submodule.mem_top
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨b, hb, hby⟩ := hy
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    rw [smul_add]
    refine Λ.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact Λ.smul_mem b hax
    · rw [mul_smul]; exact Λ.smul_mem a hby
  | smul c x _ hx =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨r, s, hs, rfl⟩ := IsFractionRing.div_surjective (𝓞 K) c
    have hs0 : s ≠ 0 := nonZeroDivisors.ne_zero hs
    have hsK : algebraMap (𝓞 K) K s ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr hs0
    refine ⟨s * a, mul_ne_zero hs0 ha, ?_⟩
    have e : (s * a) • ((algebraMap (𝓞 K) K r / algebraMap (𝓞 K) K s) • x) = r • (a • x) := by
      rw [← algebraMap_smul K (s * a), ← algebraMap_smul K r, ← algebraMap_smul K a,
        smul_smul, smul_smul, map_mul]
      congr 1
      field_simp
    rw [e]; exact Λ.smul_mem r hax

end GroundTheory.Variant₂.N1
