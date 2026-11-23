import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IndApplyOne
open GlobalTheory.BI GlobalTheory.BrauerZero

namespace GlobalTheory

theorem exists_lt_commutator_mem_of_ne_top {G : Type} [Group G] [Finite G] [Group.IsNilpotent G]
    (K : Subgroup G) (hK : K ≠ ⊤) :
    ∃ A : Subgroup G, K < A ∧ ∀ a ∈ A, ∀ b ∈ A, a * b * a⁻¹ * b⁻¹ ∈ K := by
  have hlt : K < Subgroup.normalizer (K : Set G) :=
    Group.normalizerCondition_of_isNilpotent K (lt_top_iff_ne_top.mpr hK)
  obtain ⟨x, hxN, hxK⟩ := SetLike.exists_of_lt hlt
  have hconj : ∀ i : ℤ, ∀ k ∈ K, x ^ i * k * (x ^ i)⁻¹ ∈ K := fun i k hk =>
    (Subgroup.mem_normalizer_iff.mp (Subgroup.zpow_mem _ hxN i) k).mp hk
  let A : Subgroup G :=
    { carrier := {g | ∃ k ∈ K, ∃ i : ℤ, g = k * x ^ i}
      one_mem' := ⟨1, K.one_mem, 0, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨k, hk, i, rfl⟩ ⟨k', hk', j, rfl⟩
        exact ⟨k * (x ^ i * k' * (x ^ i)⁻¹), K.mul_mem hk (hconj i k' hk'), i + j, by
          rw [zpow_add]; group⟩
      inv_mem' := by
        rintro _ ⟨k, hk, i, rfl⟩
        exact ⟨x ^ (-i) * k⁻¹ * (x ^ (-i))⁻¹, hconj (-i) _ (K.inv_mem hk), -i, by group⟩ }
  have hKA : K ≤ A := fun k hk => (⟨k, hk, 0, by simp⟩ : ∃ k' ∈ K, ∃ i : ℤ, k = k' * x ^ i)
  have hxA : x ∈ A := (⟨1, K.one_mem, 1, by simp⟩ : ∃ k ∈ K, ∃ i : ℤ, x = k * x ^ i)
  refine ⟨A, SetLike.lt_iff_le_and_exists.mpr ⟨hKA, x, hxA, hxK⟩, ?_⟩
  rintro _ ⟨k, hk, i, rfl⟩ _ ⟨k', hk', j, rfl⟩
  have h : k * x ^ i * (k' * x ^ j) * (k * x ^ i)⁻¹ * (k' * x ^ j)⁻¹ =
      k * (x ^ i * k' * (x ^ i)⁻¹) * (x ^ j * k⁻¹ * (x ^ j)⁻¹) * k'⁻¹ := by group
  rw [h]
  exact K.mul_mem (K.mul_mem (K.mul_mem hk (hconj i k' hk')) (hconj j _ (K.inv_mem hk)))
    (K.inv_mem hk')

end GlobalTheory
