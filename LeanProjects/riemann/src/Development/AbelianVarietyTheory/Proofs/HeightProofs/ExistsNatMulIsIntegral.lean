import Mathlib

namespace GlobalTheory.ExistsNatMulIsIntegral₂

open NumberField

theorem exists_nat_mul_isIntegral {E : Type} [Field E] [NumberField E] (c : E) :
    ∃ d : ℕ, 0 < d ∧ IsIntegral ℤ ((d : E) * c) := by
  have halg : IsAlgebraic ℤ c := (IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr (Algebra.IsAlgebraic.isAlgebraic c)
  obtain ⟨y, hy, hint⟩ := halg.exists_integral_multiple
  refine ⟨y.natAbs, Int.natAbs_pos.mpr hy, ?_⟩
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg y
  · simpa using hint
  · simpa using hint.neg

theorem main : ∀ {E W : Type} [inst : Field E] [NumberField E] [inst_2 : AddCommGroup W] [inst_3 : Module E W]
    [inst_4 : Module (NumberField.RingOfIntegers E) W] [IsScalarTower (NumberField.RingOfIntegers E) E W]
    (L : Submodule (NumberField.RingOfIntegers E) W),
    ∀ x ∈ Submodule.span E (↑L : Set W), ∃ (k : ℕ), (0 : ℕ) < k ∧ k • x ∈ L := by
  intro E W _ _ _ _ _ _ L x hx
  induction hx using Submodule.span_induction with
  | mem x h => exact ⟨1, one_pos, by simpa using h⟩
  | zero => exact ⟨1, one_pos, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, hxa⟩ := hx
    obtain ⟨b, hb, hyb⟩ := hy
    refine ⟨a * b, Nat.mul_pos ha hb, ?_⟩
    rw [smul_add]
    refine L.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact nsmul_mem hxa b
    · rw [mul_smul]; exact nsmul_mem hyb a
  | smul c x _ hx =>
    obtain ⟨k, hk, hkx⟩ := hx
    obtain ⟨d, hd, hdc⟩ := exists_nat_mul_isIntegral c
    refine ⟨d * k, Nat.mul_pos hd hk, ?_⟩
    let a : 𝓞 E := ⟨(d : E) * c, hdc⟩
    have ha : (algebraMap (𝓞 E) E a) = (d : E) * c := rfl
    have key : (d * k) • (c • x) = a • (k • x) := by
      rw [← algebraMap_smul E a (k • x), ha, mul_smul, mul_smul, Nat.cast_smul_eq_nsmul, smul_comm c k x]
    rw [key]
    exact L.smul_mem a hkx

end GlobalTheory.ExistsNatMulIsIntegral₂
