import Mathlib
import Development.AutomorphicSpectrum.PublishedTheorems.PublishedGlobalResults.PrimesInProgressionsRelative
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.PrimesInProgressionsRelativeOfTzRat

noncomputable section

namespace GlobalTheory.CompanionTheory.PrimesAP

theorem mainTerm_pos_model {θ β X : ℝ} (hX : 4 ≤ X) (h : θ = 0 ∨ (θ ≤ 1 ∧ 1 / 2 ≤ β ∧ β < 1)) :
    0 < (∫ t in (2 : ℝ)..X, 1 / Real.log t) - θ * ∫ t in (2 : ℝ)..X ^ β, 1 / Real.log t := by
  have hL : 0 < Real.log X := Real.log_pos (by linarith)
  rcases h with rfl | ⟨h1, h2, h3⟩
  · rw [zero_mul, sub_zero]
    exact lt_of_lt_of_le (div_pos (by linarith) hL) (le_integral_inv_log le_rfl (by linarith))
  · have hY : 2 ≤ X ^ β := by
      calc (2 : ℝ) = 4 ^ (1 / 2 : ℝ) := by
            rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]; norm_num
        _ ≤ X ^ (1 / 2 : ℝ) := Real.rpow_le_rpow (by norm_num) hX (by norm_num)
        _ ≤ X ^ β := Real.rpow_le_rpow_of_exponent_le (by linarith) h2
    have hYX : X ^ β < X := by
      have := Real.rpow_lt_rpow_of_exponent_lt (x := X) (by linarith) h3
      rwa [Real.rpow_one] at this
    have h5 : 0 < ∫ t in X ^ β..X, 1 / Real.log t :=
      lt_of_lt_of_le (div_pos (by linarith) hL) (le_integral_inv_log hY hYX.le)
    have h6 := intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_inv_log le_rfl hY) (intervalIntegrable_inv_log hY (X := X) (by linarith))
    have h7 : 0 ≤ ∫ t in (2 : ℝ)..X ^ β, 1 / Real.log t := by
      refine le_trans ?_ (le_integral_inv_log le_rfl hY)
      exact div_nonneg (by linarith) (Real.log_nonneg (by linarith))
    nlinarith

theorem linnik_of_relative_model (h : PrimesInProgressionsRelative) :
    ∃ L : ℝ, 0 < L ∧ ∀ (N : ℕ) [NeZero N] (a : ZMod N), IsUnit a →
      ∃ p : ℕ, p.Prime ∧ (p : ZMod N) = a ∧ (p : ℝ) ≤ (4 * N : ℝ) ^ L := by
  classical
  obtain ⟨C₀, C, c, cQ, c₁, h0, hC, hc, -, -, H⟩ := h
  set T : ℝ := 2 * C / c + 1 with hT
  have hT1 : 1 ≤ T := by have : 0 ≤ 2 * C / c := by positivity
                         linarith
  have hcT : c * T = 2 * C + c := by rw [hT]; field_simp
  have hexp : ∀ t : ℝ, T ≤ t → C * Real.exp (-(c * t)) < 1 / 2 := fun t ht => by
    have h1 : 2 * C < Real.exp (c * t) := by
      have := Real.add_one_le_exp (c * t)
      nlinarith
    rw [Real.exp_neg, ← div_eq_mul_inv, div_lt_iff₀ (Real.exp_pos _)]
    linarith
  set L : ℝ := max C₀ (T ^ 2) with hL
  have hLT : T ^ 2 ≤ L := le_max_right _ _
  have hL1 : 1 ≤ L := by nlinarith
  refine ⟨L, by linarith, fun N _ a ha => ?_⟩
  obtain ⟨β, θ, hθ, hb⟩ := H N
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast NeZero.pos N
  have hB : (4 : ℝ) ≤ 4 * N := by linarith
  set X : ℝ := (4 * N : ℝ) ^ L with hX
  have hX4 : 4 ≤ X := by
    have := Real.rpow_le_rpow_of_exponent_le (x := 4 * (N : ℝ)) (by linarith) hL1
    rw [Real.rpow_one] at this
    linarith
  have hlog : 1 ≤ Real.log (4 * N) := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    linarith [Real.exp_one_lt_d9]
  have hlX : Real.log X = L * Real.log (4 * N) := Real.log_rpow (by linarith) _
  have hb' := hb a ha X (Real.rpow_le_rpow_of_exponent_le (by linarith) (le_max_left _ _))
  have e1 : C * Real.exp (-(c * Real.log X / Real.log (4 * N))) < 1 / 2 := by
    have : c * Real.log X / Real.log (4 * N) = c * L := by
      rw [hlX]; field_simp
    rw [this]; exact hexp L (by nlinarith)
  have e2 : C * Real.exp (-(c * Real.sqrt (Real.log X))) < 1 / 2 :=
    hexp _ (Real.le_sqrt_of_sq_le (by rw [hlX]; nlinarith))
  have hm : 0 < ((∫ t in (2 : ℝ)..X, 1 / Real.log t) - θ a * ∫ t in (2 : ℝ)..X ^ β, 1 / Real.log t) /
      (Nat.totient N : ℝ) := by
    refine div_pos (mainTerm_pos_model hX4 ?_) (by exact_mod_cast Nat.totient_pos.2 (NeZero.pos N))
    rcases hθ with ⟨h1, -⟩ | ⟨χ, h1, h2, h3, -⟩
    · exact Or.inl (h1 a)
    · refine Or.inr ⟨?_, h2, h3⟩
      have := χ.norm_le_one a
      rw [h1 a, Complex.norm_real, Real.norm_eq_abs] at this
      exact (abs_le.1 this).2
  have hpos : (0 : ℝ) < (((Finset.Icc 1 ⌊X⌋₊).filter (fun p : ℕ => p.Prime ∧ (p : ZMod N) = a)).card : ℝ) := by
    have := (abs_le.1 hb').1
    nlinarith
  obtain ⟨p, hp⟩ := Finset.card_pos.1 (Nat.cast_pos.1 hpos)
  rw [Finset.mem_filter, Finset.mem_Icc] at hp
  exact ⟨p, hp.2.1, hp.2.2, (Nat.le_floor_iff (by linarith)).1 hp.1.2⟩

end GlobalTheory.CompanionTheory.PrimesAP

end

open scoped BigOperators Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.PrimesInProgressionsRelativeModel

theorem invLog_intervalIntegrable {u v : ℝ} (hu : 2 ≤ u) (hv : 2 ≤ v) :
    IntervalIntegrable (fun t : ℝ => 1 / Real.log t) MeasureTheory.volume u v := by
  apply ContinuousOn.intervalIntegrable
  have h2 : ∀ t ∈ Set.uIcc u v, (2 : ℝ) ≤ t := fun t ht => le_trans (le_min hu hv) ht.1
  refine ContinuousOn.div continuousOn_const (Real.continuousOn_log.mono ?_) ?_
  · intro t ht; have := h2 t ht; simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; linarith
  · intro t ht; have := h2 t ht; exact (Real.log_pos (by linarith)).ne'

theorem invLog_integral_pos {u v : ℝ} (hu : 2 ≤ u) (huv : u < v) :
    0 < ∫ t in u..v, 1 / Real.log t := by
  refine intervalIntegral.intervalIntegral_pos_of_pos_on
    (invLog_intervalIntegrable hu (by linarith)) ?_ huv
  intro t ht
  exact one_div_pos.2 (Real.log_pos (by linarith [ht.1]))

theorem main_pos {X Y θ : ℝ} (hθ : θ ≤ 1) (hY : 2 ≤ Y) (hYX : Y < X) :
    0 < (∫ t in (2 : ℝ)..X, 1 / Real.log t) - θ * ∫ t in (2 : ℝ)..Y, 1 / Real.log t := by
  have h1 := intervalIntegral.integral_add_adjacent_intervals
    (invLog_intervalIntegrable (le_refl 2) hY) (invLog_intervalIntegrable hY (by linarith : (2:ℝ) ≤ X))
  have h2 := invLog_integral_pos hY hYX
  have h3 : 0 ≤ ∫ t in (2 : ℝ)..Y, 1 / Real.log t := by
    rcases hY.eq_or_lt with h | h
    · subst h; simp
    · exact (invLog_integral_pos le_rfl h).le
  nlinarith

theorem exists_exponent {C c : ℝ} (C₀ : ℝ) (hc : 0 < c) :
    ∃ L : ℝ, C₀ ≤ L ∧ 2 ≤ L ∧ C * Real.exp (-(c * L)) + C * Real.exp (-(c * Real.sqrt L)) < 1 := by
  have t1 : Filter.Tendsto (fun L : ℝ => Real.exp (-(c * L))) Filter.atTop (nhds 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp (Filter.tendsto_id.const_mul_atTop hc)
  have t2 : Filter.Tendsto (fun L : ℝ => Real.exp (-(c * Real.sqrt L))) Filter.atTop (nhds 0) :=
    t1.comp Real.tendsto_sqrt_atTop
  have t3 := (t1.const_mul C).add (t2.const_mul C)
  simp only [mul_zero, add_zero] at t3
  have := (t3.eventually (gt_mem_nhds zero_lt_one)).and
    ((Filter.eventually_ge_atTop C₀).and (Filter.eventually_ge_atTop 2))
  obtain ⟨L, h, h1, h2⟩ := this.exists
  exact ⟨L, h1, h2, h⟩

theorem linnik (h : PrimesInProgressionsRelative) :
    ∃ L : ℝ, ∀ (N : ℕ) [NeZero N] (a : ZMod N), IsUnit a →
      ∃ p : ℕ, p.Prime ∧ (p : ZMod N) = a ∧ (p : ℝ) ≤ (4 * N : ℝ) ^ L := by
  obtain ⟨L, -, hL⟩ := GlobalTheory.CompanionTheory.PrimesAP.linnik_of_relative_model h
  exact ⟨L, hL⟩

end GlobalTheory.CompanionTheory.PrimesInProgressionsRelativeModel

end
