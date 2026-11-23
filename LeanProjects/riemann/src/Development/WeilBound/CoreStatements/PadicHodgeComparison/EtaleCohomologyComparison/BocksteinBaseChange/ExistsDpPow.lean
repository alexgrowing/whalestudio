import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ValuationSquareOfValuationMod

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TensorProduct

namespace CrystallineSemistableComparison

theorem exists_dp_pow {S : Type} [CommRing S] (l : ℕ) [hl : Fact l.Prime] (hu : ∀ u : ℕ, ¬ l ∣ u → IsUnit (u : S)) (m k : ℕ)
    (hm : m ≠ 0) (hk : k ≠ 0) (c : S) : ∃ y ∈ Ideal.span {(l : S) ^ m}, (k.factorial : S) * y = ((l : S) ^ m * c) ^ k := by
  obtain ⟨v, u, hlu, e⟩ := Nat.exists_eq_pow_mul_and_not_dvd k.factorial_ne_zero l hl.out.ne_one
  have hv : v < k := by
    have h1 : v ≤ padicValNat l k.factorial := (padicValNat_dvd_iff_le k.factorial_ne_zero).1 ⟨u, e⟩
    exact h1.trans_lt (padicValNat_factorial_lt_of_ne_zero l hk)
  obtain ⟨w, hw⟩ := (hu u hlu).exists_right_inv
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
  obtain ⟨d, hd⟩ : ∃ d, m * k = v + d := Nat.exists_eq_add_of_le (by
    have := Nat.le_mul_of_pos_left k (Nat.pos_of_ne_zero hm); omega)
  refine ⟨(l : S) ^ m * ((l : S) ^ d * w * c ^ (k + 1)), Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _), ?_⟩
  rw [e, mul_pow, ← pow_mul, Nat.mul_succ, hd, Nat.succ_eq_add_one]
  push_cast
  linear_combination ((l : S) ^ v * (l : S) ^ m * (l : S) ^ d * c ^ (k + 1)) * hw

theorem pdI_l {S : Type} [CommRing S] (l : ℕ) [hl : Fact l.Prime] (hu : ∀ u : ℕ, ¬ l ∣ u → IsUnit (u : S)) :
    R.PdI (Ideal.span {(l : S)}) := fun x hx k hk => by
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hx
  have := exists_dp_pow l hu 1 k one_ne_zero hk c
  rwa [pow_one, mul_comm (l : S) c] at this

theorem exists_pd_l {S : Type} [CommRing S] (l : ℕ) [hl : Fact l.Prime] (hu : ∀ u : ℕ, ¬ l ∣ u → IsUnit (u : S)) (ht : R.TF S)
    (m : ℕ) : ∃ δ : DividedPowers ((Ideal.span {(l : S)}).map (Ideal.Quotient.mk (Ideal.span {(l : S) ^ m}))),
      R.IsPd (Ideal.Quotient.mk _) (Ideal.span {(l : S)}) δ :=
  RL.pd_quot ht _ _ (pdI_l l hu) fun x _ hx k hk y hy => by
    rcases eq_or_ne m 0 with rfl | hm
    · rw [pow_zero, Ideal.span_singleton_one]; trivial
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hx
    obtain ⟨y', h1, h2⟩ := exists_dp_pow l hu m k hm hk c
    rw [mul_comm _ c, ← hy] at h2
    rwa [← (mul_cancel_left_mem_nonZeroDivisors (ht _ k.factorial_ne_zero)).1 h2]

variable (l : ℕ) [hl : Fact l.Prime] (k : Type) [Field k] [CharP k l]

theorem witt_unit (u : ℕ) (h : ¬ l ∣ u) : IsUnit (u : WittVector l k) :=
  WittVector.isUnit_of_coeff_zero_ne_zero _ (by
    rw [← WittVector.constantCoeff_apply, map_natCast]
    exact fun e => h ((CharP.cast_eq_zero_iff k l u).1 e))

theorem witt_tf : R.TF (WittVector l k) := fun n hn => by
  obtain ⟨v, u, hlu, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn l hl.out.ne_one
  push_cast
  exact mul_mem (pow_mem (mem_nonZeroDivisors_of_ne_zero (WittVector.p_nonzero l k)) _) (witt_unit l k u hlu).mem_nonZeroDivisors

end CrystallineSemistableComparison
