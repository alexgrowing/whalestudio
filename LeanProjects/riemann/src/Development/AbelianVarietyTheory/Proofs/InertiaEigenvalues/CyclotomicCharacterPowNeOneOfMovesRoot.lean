import Mathlib
import Formalism.CharacterColumnKernels.StatementRho
import Formalism.GaloisCohomology.LocalTateDualityK
import ReciprocityTheory.Hypotheses.GalCohDefs
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevRepZApply
open ReciprocityTheory.Gal
namespace GlobalTheory.ShapeNeg

theorem int_dvd_of_mem_span_pow {O : Type} [CommRing O] [IsDomain O] {p : ℕ} (hp : p.Prime)
    [IsLocalRing O] (hpm : (p : O) ∈ IsLocalRing.maximalIdeal O) (hp0 : (p : O) ≠ 0) (n : ℕ) (z : ℤ)
    (hz : (z : O) ∈ Ideal.span {(p : O) ^ n}) : (p : ℤ) ^ n ∣ z := by
  have hd : z.gcd ((p : ℤ) ^ n) ∣ p ^ n := by
    have := Int.gcd_dvd_right (a := z) (b := (p : ℤ) ^ n)
    have h2 : ((z.gcd ((p : ℤ) ^ n) : ℕ) : ℤ) ∣ ((p ^ n : ℕ) : ℤ) := by push_cast; exact this
    exact_mod_cast h2
  obtain ⟨m, hm, hgm⟩ := (Nat.dvd_prime_pow hp).1 hd
  rcases lt_or_eq_of_le hm with hlt | heq
  · exfalso
    have hb := Int.gcd_eq_gcd_ab z ((p : ℤ) ^ n)
    rw [hgm] at hb
    have hmem : ((p : O) ^ m) ∈ Ideal.span {(p : O) ^ n} := by
      have : (((p ^ m : ℕ) : ℤ) : O) = (z : O) * (z.gcdA ((p : ℤ) ^ n) : O)
          + ((p : O) ^ n) * (z.gcdB ((p : ℤ) ^ n) : O) := by
        rw [hb]; push_cast; ring
      have e : (((p ^ m : ℕ) : ℤ) : O) = (p : O) ^ m := by push_cast; ring
      rw [← e, this]
      exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ hz)
        (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.1 hmem
    have hsplit : (p : O) ^ n = (p : O) ^ m * (p : O) ^ (n - m) := by
      rw [← pow_add]; congr 1; omega
    rw [hsplit, mul_assoc] at hc
    have h1 : (p : O) ^ (n - m) * c = 1 := by
      have hne : (p : O) ^ m ≠ 0 := pow_ne_zero _ hp0
      have := mul_left_cancel₀ hne (hc.symm.trans (mul_one _).symm)
      exact this
    have hu : IsUnit ((p : O) ^ (n - m)) := isUnit_iff_exists_inv.2 ⟨c, h1⟩
    rw [isUnit_pow_iff (Nat.sub_ne_zero_of_lt hlt)] at hu
    exact (IsLocalRing.mem_maximalIdeal _).1 hpm hu
  · have := Int.gcd_dvd_left (a := z) (b := (p : ℤ) ^ n)
    rw [hgm, heq] at this
    exact_mod_cast this

theorem cyc_char_pow_ne_one : ∀ {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)} {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O], (p : O) ∈ IsLocalRing.maximalIdeal O → (p : O) ≠ 0 →
    ∀ ε : Formalism.GaloisCohomology.GK p K →* Oˣ, (∀ (g : Formalism.GaloisCohomology.GK p K) (n : ℕ) (ζ : PadicAlgCl p), ζ ^ (p ^ n) = 1 →
      ∃ a : ℕ, g ζ = ζ ^ a ∧ (((ε) g : Oˣ) : O) - (a : O) ∈ Ideal.span {(p : O) ^ n}) → ∀ k : ℕ,
    (∃ (σ : Formalism.GaloisCohomology.GK p K) (n : ℕ) (ζ : PadicAlgCl p), ζ ^ (p ^ n) = 1 ∧ (σ ^ k) ζ ≠ ζ) →
    ∃ σ : Formalism.GaloisCohomology.GK p K, ε σ ^ k ≠ 1 := by
  intro p hpF K O _ _ _ hpm hp0 ε hcyc k ⟨σ, n, ζ, hζ, hne⟩
  refine ⟨σ, fun hk => hne ?_⟩
  obtain ⟨a, ha, hmem⟩ := hcyc (σ ^ k) n ζ hζ
  rw [map_pow, hk, Units.val_one] at hmem
  have hz : (((a : ℤ) - 1 : ℤ) : O) ∈ Ideal.span {(p : O) ^ n} := by
    have := (Ideal.neg_mem_iff _).2 hmem
    push_cast
    convert this using 1; ring
  obtain ⟨t, ht⟩ := int_dvd_of_mem_span_pow hpF.out hpm hp0 n _ hz
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    rw [zero_pow (pow_ne_zero _ hpF.out.ne_zero)] at hζ
    exact zero_ne_one hζ
  rw [ha, ← zpow_natCast, show (a : ℤ) = 1 + (p : ℤ) ^ n * t by omega, zpow_add₀ hζ0, zpow_mul,
    zpow_one]
  have : ζ ^ ((p : ℤ) ^ n) = 1 := by
    rw [show ((p : ℤ) ^ n) = ((p ^ n : ℕ) : ℤ) by push_cast; rfl, zpow_natCast, hζ]
  rw [this, one_zpow, mul_one]

end GlobalTheory.ShapeNeg
