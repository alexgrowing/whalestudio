import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.StickelbergerTheorem.FfsumPow
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.StickelbergerTheorem.ImportsTer
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.StickelbergerTheorem.RedRoot
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.StickelbergerTheorem.JacDvd
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.StickelbergerTheorem.StickelbergerAt

open NumberField IsDedekindDomain UpperTheory.V.Kum UpperTheory.V.Stick
open scoped nonZeroDivisors

private theorem zmod_pow_mul_eq_pow_mul_mod {p : ℕ} [Fact p.Prime] (M d : ℕ) (hMd : M * d = p - 1) (y : ZMod p)
    (hy : y ≠ 0) (n : ℕ) : y ^ (d * n) = y ^ (d * (n % M)) := by
  have h1 : (y ^ d) ^ M = 1 := by
    rw [← pow_mul, mul_comm, hMd]
    exact ZMod.pow_card_sub_one_eq_one hy
  conv_lhs => rw [← Nat.mod_add_div n M]
  rw [mul_add, pow_add, pow_mul y d (M * (n / M)), pow_mul (y ^ d) M, h1, one_pow, mul_one]

theorem UpperTheory.V.Stick.jacobi :
    ∀ (M : ℕ) [NeZero M] (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {M} ℚ K] (p : ℕ) [Fact p.Prime] (π : 𝓞 K →+* ZMod p), p.Coprime M →
    ∀ a b : ZMod M, a ≠ 0 → b ≠ 0 → a + b ≠ 0 →
    ∃ J : 𝓞 K, J ∣ (p : 𝓞 K) ∧ ∀ t : (ZMod M)ˣ, J ∈ conjI M K (RingHom.ker π) t ↔ carry M (a * t) (b * t) = 0 := by
  intro M _ K _ _ _ p _ π hp a b ha hb hab
  have hz := (IsCyclotomicExtension.zeta_spec M ℚ K).toInteger_isPrimitiveRoot
  obtain ⟨hπz, hdvd⟩ := redRoot (𝓞 K) p π M _ hp hz
  obtain ⟨d, hd⟩ := hdvd
  obtain ⟨χ, hχ, hord⟩ := teich (𝓞 K) p π M d _ hz hπz hd.symm
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  have hd0 : 0 < d := by
    rcases Nat.eq_zero_or_pos d with h | h
    · rw [h, mul_zero] at hd
      omega
    · exact h
  have hne : ∀ c : ZMod M, c ≠ 0 → χ ^ c.val ≠ 1 := by
    intro c hc h
    rw [← orderOf_dvd_iff_pow_eq_one, hord] at h
    exact hc ((ZMod.val_eq_zero c).mp (Nat.eq_zero_of_dvd_of_lt h (ZMod.val_lt c)))
  have hsum : χ ^ a.val * χ ^ b.val ≠ 1 := by
    rw [← pow_add]
    intro h
    rw [← orderOf_dvd_iff_pow_eq_one, hord] at h
    apply hab
    rw [← ZMod.natCast_zmod_val a, ← ZMod.natCast_zmod_val b, ← Nat.cast_add]
    exact (ZMod.natCast_eq_zero_iff _ _).mpr h
  refine ⟨jacobiSum (χ ^ a.val) (χ ^ b.val), jacDvd (𝓞 K) p _ _ (hne a ha) (hne b hb) hsum, ?_⟩
  intro t
  have hunit : ∀ c : ZMod M, c ≠ 0 → (c * t).val ≠ 0 := by
    intro c hc
    rw [Ne, ZMod.val_eq_zero]
    intro h
    exact hc ((Units.mul_left_eq_zero t).mp h)
  have hfac : ∀ c : ZMod M, c ≠ 0 → ∀ y : ZMod p,
      π (sgO M K t ((χ ^ c.val) y)) = y ^ (d * (c * t).val) := by
    intro c hc y
    have hcv : c.val ≠ 0 := by rwa [Ne, ZMod.val_eq_zero]
    by_cases hy : y = 0
    · subst hy
      rw [MulChar.map_zero, map_zero, map_zero, zero_pow (Nat.mul_ne_zero hd0.ne' (hunit c hc))]
    · obtain ⟨h1, h2⟩ := hχ y hy
      rw [MulChar.pow_apply' _ hcv,
        sgO_apply M K t (by rw [← pow_mul, mul_comm, pow_mul, h1, one_pow]),
        map_pow, map_pow, h2, ← pow_mul, ← pow_mul, ZMod.val_mul,
        zmod_pow_mul_eq_pow_mul_mod M d hd.symm y hy (c.val * (t : ZMod M).val)]
  have hlt : ∀ c : ZMod M, d * (c * t).val < p - 1 := by
    intro c
    rw [hd, mul_comm M d]
    exact (Nat.mul_lt_mul_left hd0).mpr (ZMod.val_lt _)
  rw [mem_conjI, RingHom.mem_ker]
  unfold jacobiSum
  rw [map_sum, map_sum]
  simp_rw [map_mul, hfac a ha, hfac b hb]
  rw [ffsum p _ _ (Nat.mul_pos hd0 (Nat.pos_of_ne_zero (hunit a ha))) (hlt a)
    (Nat.mul_pos hd0 (Nat.pos_of_ne_zero (hunit b hb))) (hlt b)]
  rw [hd, ← mul_add, mul_comm M d, Nat.mul_lt_mul_left hd0]
  by_cases h : M ≤ (a * t).val + (b * t).val
  · simp only [carry, h, if_true, one_ne_zero, iff_false, not_lt]
  · simp only [carry, h, if_false, iff_true]
    omega
