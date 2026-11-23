import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PadicUnitNorm

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.Gal.W2.Seed UpperTheory.Gal.G1
open scoped TensorProduct

private lemma pow_neg_three_lt_two_norm_sq (q : ℕ) [hq : Fact q.Prime] :
    (q : ℝ) ^ (-3 : ℤ) < ‖(2 : ℤ_[q])‖ ^ 2 := by
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq.out.two_le
  by_cases h : q = 2
  · subst h
    have h2 : ‖(2 : ℤ_[2])‖ = (2 : ℝ) ^ (-1 : ℤ) := by
      have := PadicInt.norm_p_pow (p := 2) 1
      simpa using this
    rw [h2]
    norm_num
  · have h1 : ‖(2 : ℤ_[q])‖ = 1 := by
      apply le_antisymm (PadicInt.norm_le_one _)
      by_contra hlt
      push_neg at hlt
      have hd := (PadicInt.norm_int_lt_one_iff_dvd (p := q) 2).1 (by exact_mod_cast hlt)
      have hd' : q ∣ 2 := by exact_mod_cast hd
      exact h ((Nat.prime_dvd_prime_iff_eq hq.out Nat.prime_two).1 hd')
    rw [h1, one_pow, _root_.zpow_neg]
    have hlt : (1 : ℝ) < (q : ℝ) ^ (3 : ℤ) := one_lt_zpow₀ (by linarith) (by norm_num)
    exact inv_lt_one_of_one_lt₀ hlt

private lemma sq_of_close (q : ℕ) [hq : Fact q.Prime] (z : ℤ_[q])
    (hz : ‖(1 : ℤ_[q]) - z‖ < ‖(2 : ℤ_[q])‖ ^ 2) : ∃ x : ℤ_[q], x ^ 2 = z := by
  have hn : ‖Polynomial.aeval (1 : ℤ_[q]) (Polynomial.X ^ 2 - Polynomial.C z : Polynomial ℤ_[q])‖ <
      ‖Polynomial.aeval (1 : ℤ_[q])
        (Polynomial.derivative (Polynomial.X ^ 2 - Polynomial.C z : Polynomial ℤ_[q]))‖ ^ 2 := by
    simpa [Polynomial.derivative_X_pow, one_add_one_eq_two] using hz
  obtain ⟨x, hx, -⟩ := hensels_lemma hn
  refine ⟨x, ?_⟩
  simpa [sub_eq_zero] using hx

theorem UpperTheory.Gal.G1.pPadicSqFin :
    PadicSqFin := by
  intro q hq
  haveI : NeZero (q ^ 3) := ⟨pow_ne_zero 3 hq.out.ne_zero⟩
  refine ⟨Fintype.card (ZMod (q ^ 3)), fun u => Fintype.equivFin (ZMod (q ^ 3))
    (if h : ‖u‖ ≤ 1 then PadicInt.toZModPow 3 ⟨u, h⟩ else 0), ?_⟩
  intro u u' hu hu' hk
  simp only [dif_pos hu.le, dif_pos hu'.le, (Fintype.equivFin _).injective.eq_iff] at hk
  obtain ⟨a, ha⟩ : ∃ a : ℤ_[q], (a : ℚ_[q]) = u ∧ PadicInt.toZModPow 3 a =
      PadicInt.toZModPow 3 ⟨u, hu.le⟩ := ⟨⟨u, hu.le⟩, rfl, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : ℤ_[q], (b : ℚ_[q]) = u' ∧ PadicInt.toZModPow 3 b =
      PadicInt.toZModPow 3 ⟨u', hu'.le⟩ := ⟨⟨u', hu'.le⟩, rfl, rfl⟩
  have hmem : b - a ∈ RingHom.ker (PadicInt.toZModPow (p := q) 3) := by
    rw [RingHom.sub_mem_ker_iff, ha.2, hb.2]
    exact hk.symm
  rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton] at hmem
  obtain ⟨c, hc⟩ := hmem
  have hd : ‖u' - u‖ ≤ (q : ℝ) ^ (-3 : ℤ) := by
    have h1 : ‖b - a‖ ≤ (q : ℝ) ^ (-((3 : ℕ) : ℤ)) := by
      rw [hc, norm_mul, PadicInt.norm_p_pow]
      have hc1 := PadicInt.norm_le_one c
      have hpos : (0 : ℝ) ≤ (q : ℝ) ^ (-((3 : ℕ) : ℤ)) := by positivity
      calc _ ≤ (q : ℝ) ^ (-((3 : ℕ) : ℤ)) * 1 := mul_le_mul_of_nonneg_left hc1 hpos
        _ = _ := mul_one _
    rw [PadicInt.norm_def, PadicInt.coe_sub, ha.1, hb.1] at h1
    simpa using h1
  have hu0 : u ≠ 0 := by
    rintro rfl
    simp at hu
  have hz : ‖u' / u‖ ≤ 1 := by
    rw [norm_div, hu, hu']
    simp
  obtain ⟨w, hw⟩ : ∃ w : ℤ_[q], (w : ℚ_[q]) = u' / u := ⟨⟨u' / u, hz⟩, rfl⟩
  obtain ⟨x, hx⟩ := sq_of_close q w (by
    have e : ‖(1 : ℤ_[q]) - w‖ = ‖u' - u‖ := by
      rw [PadicInt.norm_def, PadicInt.coe_sub, PadicInt.coe_one, hw,
        show (1 : ℚ_[q]) - u' / u = (u - u') / u by field_simp, norm_div, hu, div_one,
        norm_sub_rev]
    rw [e]
    exact lt_of_le_of_lt hd (pow_neg_three_lt_two_norm_sq q))
  refine ⟨x, ?_⟩
  have hx' : (x : ℚ_[q]) ^ 2 = u' / u := by
    rw [← hw, ← hx]
    simp
  rw [hx']
  field_simp
