import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.QuotientHighestWeightTensorStandard
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirAlgebra.KhwLowKSubRootEqZero

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK

theorem cone_norm_dot_root {n : ℕ} (l : Fin n → ℝ) (a b : Fin n) (c : ℝ) :
    ∑ i, l i * (c • root a b) i = c * (l a - l b) := by
  unfold root
  simp [Pi.single_apply, mul_sub, Finset.sum_sub_distrib]
  try ring

theorem cone_norm_dot_nonneg {n : ℕ} (l β : Fin n → ℝ) (hl : Antitone l) (hβ : InRootCone β) :
    0 ≤ dot l β := by
  unfold dot
  obtain ⟨m, rfl⟩ := hβ
  have hsw : ∑ i, l i * (∑ a, ∑ b, if a < b then (m a b : ℝ) • root a b else 0) i
      = ∑ a, ∑ b, ∑ i, l i * ((if a < b then (m a b : ℝ) • root a b else 0) i) := by
    simp only [Finset.sum_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
  rw [hsw]
  refine Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => ?_
  split_ifs with hab
  · rw [cone_norm_dot_root]
    exact mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr (hl hab.le))
  · simp

theorem cone_norm_eq_zero {n : ℕ} (β : Fin n → ℝ) (h : nsq β ≤ 0) : β = 0 := by
  unfold nsq dot at h
  have hnn : ∀ i ∈ Finset.univ, 0 ≤ β i * β i := fun i _ => mul_self_nonneg _
  have h0 := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp (le_antisymm h (Finset.sum_nonneg hnn))
  funext i
  exact mul_self_eq_zero.mp (h0 i (Finset.mem_univ _))

theorem cone_norm (n : ℕ) : ConeNormStatement n := by
  intro lam β hl hβ h
  apply cone_norm_eq_zero
  have hd := cone_norm_dot_nonneg lam β hl hβ
  have hexp : nsq (lam + β) = nsq lam + 2 * dot lam β + nsq β := by
    unfold nsq dot
    simp only [Pi.add_apply]
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  linarith

end ReciprocityTheory.ChartRestriction.DS.Lap.LemK
