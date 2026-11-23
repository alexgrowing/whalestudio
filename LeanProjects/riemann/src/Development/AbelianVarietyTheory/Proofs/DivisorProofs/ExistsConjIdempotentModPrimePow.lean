import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsGPull
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtPlace

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev

namespace GlobalTheory.UPel.HT.SplitIdem

theorem isCoprime_deriv {p : ℕ} (hp : p.Prime) {t n ρ : ℤ} (hd : ¬ (p : ℤ) ∣ t ^ 2 - 4 * n)
    (h : (p : ℤ) ∣ ρ ^ 2 - t * ρ + n) : IsCoprime (2 * ρ - t) (p : ℤ) := by
  have hp' : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  refine ((hp'.irreducible.coprime_iff_not_dvd).mpr ?_).symm
  intro h2
  apply hd
  have : t ^ 2 - 4 * n = (2 * ρ - t) * (2 * ρ - t) - 4 * (ρ ^ 2 - t * ρ + n) := by ring
  rw [this]
  exact dvd_sub (h2.mul_right _) (h.mul_left _)

theorem exists_root_pow {p : ℕ} (hp : p.Prime) {t n : ℤ} (hd : ¬ (p : ℤ) ∣ t ^ 2 - 4 * n)
    (h : ∃ ρ : ℤ, (p : ℤ) ∣ ρ ^ 2 - t * ρ + n) (k : ℕ) :
    ∃ ρ : ℤ, (p : ℤ) ^ (k + 1) ∣ ρ ^ 2 - t * ρ + n := by
  induction k with
  | zero => simpa using h
  | succ k ih =>
    obtain ⟨ρ, c, hc⟩ := ih
    have h1 : (p : ℤ) ∣ ρ ^ 2 - t * ρ + n := by
      rw [hc]; exact (dvd_pow_self _ (Nat.succ_ne_zero k)).mul_right _
    obtain ⟨a, b, hab⟩ := isCoprime_deriv hp hd h1
    refine ⟨ρ - (p : ℤ) ^ (k + 1) * c * a, c * b + (p : ℤ) ^ k * c ^ 2 * a ^ 2, ?_⟩
    linear_combination hc - (p : ℤ) ^ (k + 1) * c * hab

theorem exists_conj_idem : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (r : ℕ), ∃ ε u v : 𝓞 D.F,
    ε + D.bar ε = 1 + (p : 𝓞 D.F) ^ r * u ∧ ε * D.bar ε = (p : 𝓞 D.F) ^ r * v := by
  intro p hp D r
  obtain ⟨ρ, c, hc⟩ := exists_root_pow hp.out D.disc_p D.split r
  have h1 : (p : ℤ) ∣ ρ ^ 2 - D.tr * ρ + D.nm := by
    rw [hc]; exact (dvd_pow_self _ (Nat.succ_ne_zero r)).mul_right _
  obtain ⟨s, b, hsb⟩ := (isCoprime_deriv hp.out D.disc_p h1).pow_right (n := r)
  have hc' := congrArg (Int.cast : ℤ → 𝓞 D.F) hc
  have hsb' := congrArg (Int.cast : ℤ → 𝓞 D.F) hsb
  push_cast at hc' hsb'
  have ht := D.tr_eq
  have hn := D.nm_eq
  refine ⟨(s : 𝓞 D.F) * ((ρ : 𝓞 D.F) - D.ω), -(b : 𝓞 D.F), (s : 𝓞 D.F) ^ 2 * (p : 𝓞 D.F) * (c : 𝓞 D.F), ?_, ?_⟩
  · rw [map_mul, map_sub, map_intCast, map_intCast]
    linear_combination hsb' - (s : 𝓞 D.F) * ht
  · rw [map_mul, map_sub, map_intCast, map_intCast]
    linear_combination (s : 𝓞 D.F) ^ 2 * hc' - (s : 𝓞 D.F) ^ 2 * (ρ : 𝓞 D.F) * ht + (s : 𝓞 D.F) ^ 2 * hn

end GlobalTheory.UPel.HT.SplitIdem
