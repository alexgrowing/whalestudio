import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ConjugateOrderData
open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical

namespace GlobalTheory

theorem val_vp_natCast_pow (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (K : Type) [Field K]
    [Algebra O K] [IsFractionRing O K] (l : ℕ) (hl : l ≠ 0) (h : (l : O) ∈ IsLocalRing.maximalIdeal O) (k : ℕ) :
    val_vp O l (algebraMap O K ((l : O) ^ k)) = ((k : ℚ) : WithTop ℚ) := by
  have h0 : (l : K) ≠ 0 := by
    rw [← map_natCast (algebraMap O K)]
    exact (map_ne_zero_iff _ (IsFractionRing.injective O K)).2 (Nat.cast_ne_zero.2 hl)
  have h1 : (IsDiscreteValuationRing.maximalIdeal O).valuation K (l : K) < 1 := by
    rw [← map_natCast (algebraMap O K), HeightOneSpectrum.valuation_lt_one_iff_mem]
    exact h
  have h2 : (IsDiscreteValuationRing.maximalIdeal O).valuation K (l : K) ≠ 0 := by simpa using h0
  have h3 : ord_vw O (l : K) ≠ 0 := by
    unfold ord_vw
    intro h4
    have := WithZero.exp_log h2
    rw [neg_eq_zero.1 h4, WithZero.exp_zero] at this
    exact h1.ne this.symm
  have hpow : algebraMap O K ((l : O) ^ k) = (l : K) ^ k := by simp
  have hk : ord_vw O ((l : K) ^ k) = k * ord_vw O (l : K) := by
    unfold ord_vw
    rw [map_pow, WithZero.log_pow, nsmul_eq_mul]
    ring
  rw [hpow, val_vp, if_neg (pow_ne_zero k h0), hk]
  congr 1
  push_cast
  field_simp

end GlobalTheory
