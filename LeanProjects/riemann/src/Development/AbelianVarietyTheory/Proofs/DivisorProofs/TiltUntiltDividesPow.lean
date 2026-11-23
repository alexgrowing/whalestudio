import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PrismaticDieudonnePerfd

open Ideal WittVector

namespace GlobalTheory

private lemma perfection_isUnit_of_coeff_zero {p : ℕ} [hp : Fact p.Prime] {R : Type*}
    [CommRing R] [CharP R p]
    (x : Perfection R p) (h : IsUnit (Perfection.coeff R p 0 x)) : IsUnit x := by
  have hn : ∀ n, IsUnit (Perfection.coeff R p n x) := fun n => by
    have e : Perfection.coeff R p n x ^ p ^ n = Perfection.coeff R p 0 x :=
      Perfection.coeffMonoidHom_pow_p_pow_self x n
    rw [← e] at h
    exact (isUnit_pow_iff (pow_ne_zero _ hp.out.ne_zero)).1 h
  let y : Perfection R p := ⟨fun n => ((hn n).unit⁻¹ : Rˣ), fun n => by
    have e : (hn (n + 1)).unit ^ p = (hn n).unit :=
      Units.ext (by simp [Perfection.coeff_pow_p' x n])
    rw [← Units.val_pow_eq_pow_val, inv_pow, e]⟩
  have hy : ∀ n, Perfection.coeff R p n x * Perfection.coeff R p n y = 1 := fun n => by
    rw [Perfection.coeff_mk]
    exact (hn n).mul_val_inv
  refine ⟨⟨x, y, ?_, ?_⟩, rfl⟩
  · ext n; rw [map_mul, hy, map_one]
  · ext n; rw [map_mul, mul_comm, hy, map_one]

private lemma untilt_sub_one_congr {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O]
    [Fact ¬IsUnit (p : O)] [IsAdicComplete (span {(p : O)}) O] (x : PreTilt O p) :
    ∃ t : O, (x - 1).untilt = x.untilt - 1 + p * t := by
  have h : Ideal.Quotient.mk (span {(p : O)}) (x - 1).untilt =
      Ideal.Quotient.mk (span {(p : O)}) (x.untilt - 1) := by
    rw [PreTilt.mk_untilt_eq_coeff_zero, map_sub, map_sub, PreTilt.mk_untilt_eq_coeff_zero,
      map_one, map_one]
  obtain ⟨t, ht⟩ := mem_span_singleton'.1 (Ideal.Quotient.eq.1 h)
  exact ⟨t, by linear_combination -ht⟩

theorem preTilt_pow_sub_one_pow_dvd_of_associated (p : ℕ) [hp : Fact p.Prime] (R : Type)
    [CommRing R] [Fact ¬IsUnit (p : R)] [IsAdicComplete (Ideal.span {(p : R)}) R]
    (hreg : IsSMulRegular R (p : R)) (pflat f : PreTilt R p)
    (hpf : PreTilt.untilt pflat = (p : R))
    (hker : ∀ c : PreTilt R p, PreTilt.coeff 0 c = 0 → pflat ∣ c)
    (hass : Associated ((PreTilt.untilt f - 1) ^ (p * (p - 1))) (p : R))
    (c : PreTilt R p) (hc : PreTilt.coeff 0 c = 0) : (f ^ p - 1) ^ (p - 1) ∣ c := by
  obtain ⟨w, hw⟩ := hass
  obtain ⟨t, ht⟩ := untilt_sub_one_congr f
  set a : R := PreTilt.untilt f - 1 with ha
  have h2 := hp.out.two_le
  obtain ⟨M, hM⟩ : ∃ M, p * (p - 1) = M + 2 := by
    refine ⟨p * (p - 1) - 2, ?_⟩
    have : 2 * 1 ≤ p * (p - 1) := Nat.mul_le_mul h2 (by omega)
    omega
  have hpJ : (p : R) ∈ jacobson (⊥ : Ideal R) :=
    IsAdicComplete.le_jacobson_bot (span {(p : R)}) (mem_span_singleton_self _)
  have haJ : a ∈ jacobson (⊥ : Ideal R) := by
    refine Ideal.isRadical_jacobson ⊥ ⟨p * (p - 1), ?_⟩
    have : a ^ (p * (p - 1)) = (p : R) * ((w⁻¹ : Rˣ) : R) := by
      rw [← hw, mul_assoc, Units.mul_inv, mul_one]
    rw [this]
    exact Ideal.mul_mem_right _ _ hpJ
  have hu : IsUnit (a * (a ^ M * w * t) + 1) := mem_jacobson_bot.1 haJ _
  have h1 : (f - 1).untilt = a * (a * (a ^ M * w * t) + 1) := by
    rw [ht, ← hw, hM]; ring
  have hg : (f ^ p - 1) ^ (p - 1) = (f - 1) ^ (p * (p - 1)) := by
    rw [pow_mul, sub_pow_char (p := p) f 1, one_pow]
  have hu' : IsUnit (((w⁻¹ : Rˣ) : R) * (a * (a ^ M * w * t) + 1) ^ (p * (p - 1))) :=
    (Units.isUnit _).mul (hu.pow _)
  set u : R := ((w⁻¹ : Rˣ) : R) * (a * (a ^ M * w * t) + 1) ^ (p * (p - 1)) with hudef
  have hunt : ((f ^ p - 1) ^ (p - 1)).untilt = (p : R) * u := by
    rw [hg, PreTilt.untilt.map_pow, h1, mul_pow, hudef, ← hw, mul_assoc (a ^ (p * (p - 1))) (w : R),
      Units.mul_inv_cancel_left]
  have h0 : PreTilt.coeff 0 ((f ^ p - 1) ^ (p - 1)) = 0 := by
    rw [← PreTilt.mk_untilt_eq_coeff_zero, hunt]
    exact Ideal.Quotient.eq_zero_iff_mem.2
      (Ideal.mul_mem_right _ _ (mem_span_singleton_self _))
  obtain ⟨d, hd⟩ := hker _ h0
  have hdu : d.untilt = u := by
    apply hreg
    have := hunt
    rw [hd, map_mul, hpf] at this
    simpa [smul_eq_mul] using this
  have hdunit : IsUnit d := by
    apply perfection_isUnit_of_coeff_zero d
    have : IsUnit (PreTilt.coeff 0 d) := by
      rw [← PreTilt.mk_untilt_eq_coeff_zero, hdu]
      exact hu'.map _
    exact this
  rw [hd, hdunit.mul_right_dvd]
  exact hker c hc

end GlobalTheory
