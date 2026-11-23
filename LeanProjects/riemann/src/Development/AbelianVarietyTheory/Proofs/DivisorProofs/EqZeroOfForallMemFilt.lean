import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntDerApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivationTaylorPowerSeriesOfDerivationsKill
open IsLocalRing GlobalTheory.FormalOrigin

namespace GlobalTheory.FormalOrigin.Extend

def filt {σ R : Type} [CommRing R] (I : Ideal R) (k : ℕ) : Ideal (MvPowerSeries σ R) where
  carrier := {F | ∀ α, MvPowerSeries.coeff α F ∈ I ^ (k - α.degree)}
  add_mem' {F G} hF hG α := by simpa using Ideal.add_mem _ (hF α) (hG α)
  zero_mem' α := by simp
  smul_mem' c F hF α := by
    classical
    rw [smul_eq_mul, MvPowerSeries.coeff_mul]
    refine Ideal.sum_mem _ fun p hp => Ideal.mul_mem_left _ _ ?_
    have h := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
    have : p.2.degree ≤ α.degree := by rw [← h, map_add]; omega
    exact Ideal.pow_le_pow_right (by omega) (hF p.2)

theorem mem_filt {σ R : Type} [CommRing R] (I : Ideal R) (k : ℕ) (F : MvPowerSeries σ R) :
    F ∈ filt I k ↔ ∀ α, MvPowerSeries.coeff α F ∈ I ^ (k - α.degree) := Iff.rfl

theorem eq_zero_of_forall_mem_filt {σ R : Type} [CommRing R] (I : Ideal R) [IsHausdorff I R]
    (F : MvPowerSeries σ R) (h : ∀ k, F ∈ filt I k) : F = 0 := by
  ext α
  rw [map_zero]
  refine IsHausdorff.haus (I := I) inferInstance _ fun m => ?_
  have := h (m + α.degree) α
  rw [Nat.add_sub_cancel] at this
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
  exact this

end GlobalTheory.FormalOrigin.Extend
