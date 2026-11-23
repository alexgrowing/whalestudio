import Formalism.ThetaLogCoordinates.TraceIsometryWeights.StatementF

namespace Formalism.InvariantFactorPaths.PW

open MvPolynomial Finset Formalism.GM.M Formalism.GM

theorem kapC_mono {p n n' d d' : ℕ} (hn : n ≤ n') (hd : d ≤ d') : kapC p n d ≤ kapC p n' d' := by
  unfold kapC
  exact Nat.mul_le_mul (Nat.choose_le_choose 2 hn) (Nat.log_mono_right (by omega))

theorem pow_smul_mem_of_le {p : ℕ} [Fact p.Prime] {σ : Type} (L : Submodule ℤ_[p] (MvPolynomial σ ℚ_[p]))
    {k e : ℕ} (hke : k ≤ e) {y : MvPolynomial σ ℚ_[p]} (hy : ((p : ℚ_[p]) ^ k) • y ∈ L) :
    ((p : ℚ_[p]) ^ e) • y ∈ L := by
  have h := L.smul_mem ((p : ℤ_[p]) ^ (e - k)) hy
  rw [← algebraMap_smul ℚ_[p] ((p : ℤ_[p]) ^ (e - k)), smul_smul] at h
  have e2 : ((p : ℚ_[p]) ^ e) = algebraMap ℤ_[p] ℚ_[p] ((p : ℤ_[p]) ^ (e - k)) * (p : ℚ_[p]) ^ k := by
    rw [map_pow, map_natCast, ← pow_add, Nat.sub_add_cancel hke]
  rw [e2]
  exact h

theorem dischargeP_of (h1 : ProjP) (h2 : CommP) (h3 : IntP) : DischargeP := by
  intro p _ N r LL ρ e1 he
  unfold Formalism.GM.M.HypP
  refine ⟨fun j _ Cs _ T hT => ?_, fun j j' Cs Cs' T T' P P' hj hC _ _ hP hP' =>
    h2 p N r LL j j' Cs Cs' T T' P P' hj hC hP hP'⟩
  obtain ⟨P, hP, hsym⟩ := h1 p N r LL j Cs T hT
  refine ⟨P, hP, hsym, fun F hF => ?_⟩
  have hcard : Cs.card ≤ r := by simpa using Finset.card_le_univ Cs
  exact pow_smul_mem_of_le _ ((kapC_mono hcard le_rfl).trans he) (h3 p N r LL j Cs T P hT hP F hF)

theorem dischargeW_of (h : WeylP) : DischargeW := by
  intro p _ N r LL e1 he
  have h0 := h p N r LL
  unfold Formalism.GM.M.HypW at h0 ⊢
  intro j hj la x hx hxI
  exact pow_smul_mem_of_le _ he (h0 j hj la x hx hxI)

theorem dischargeE_of (h : ExtP) : DischargeE := by
  intro p _ N r LL ρ e1 he
  have h0 := h p N r LL ρ
  unfold Formalism.GM.M.HypE at h0 ⊢
  intro j hj la
  obtain ⟨P, h1, h2, h3, h4, h5⟩ := h0 j hj la
  have hk : kapC p (r - 1) LL.total ≤ e1 := (kapC_mono (Nat.sub_le r 1) le_rfl).trans he
  exact ⟨P, h1, h2, h3, h4, fun F hF hW => pow_smul_mem_of_le _ hk (h5 F hF hW)⟩

theorem total_le {N : ℕ} (LL : Letters N) (b : ℕ) (h : ∀ x, LL.deg x ≤ b) : LL.total ≤ b * N := by
  unfold Letters.total
  calc ∑ i, LL.deg i ≤ ∑ _i : Fin N, b := Finset.sum_le_sum (fun i _ => h i)
    _ = b * N := by simp [mul_comm]

theorem kapC_le_real (p : ℕ) [Fact p.Prime] (r d a : ℕ) (h : d + r ≤ p ^ 2 * (8 * a + r) ^ 2) :
    (kapC p r d : ℝ) ≤ (r : ℝ) ^ 2 * lgV2 p a r := by
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr
    simp [kapC]
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hx : (1 : ℝ) ≤ 8 * a + r := by exact_mod_cast (by omega : 1 ≤ 8 * a + r)
  have hlg : 0 ≤ lgV2 p a r := by
    unfold lgV2
    have := Real.logb_nonneg hp1 hx
    linarith
  have hL : ((Nat.log p (d + r - 1) : ℕ) : ℝ) ≤ 2 * lgV2 p a r := by
    by_cases hD : d + r - 1 = 0
    · rw [hD, Nat.log_zero_right]
      simp only [CharP.cast_eq_zero]
      linarith
    have hpos : (0 : ℝ) < ((d + r - 1 : ℕ) : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hD
    have hpow : (p : ℝ) ^ (Nat.log p (d + r - 1)) ≤ ((d + r - 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.pow_log_le_self p hD
    have h1 : ((Nat.log p (d + r - 1) : ℕ) : ℝ) ≤ Real.logb p ((d + r - 1 : ℕ) : ℝ) := by
      rw [Real.le_logb_iff_rpow_le hp1 hpos, Real.rpow_natCast]
      exact hpow
    have h2 : ((d + r - 1 : ℕ) : ℝ) ≤ (p : ℝ) ^ 2 * (8 * a + r) ^ 2 := by
      exact_mod_cast (Nat.sub_le _ _).trans h
    have h3 := Real.logb_le_logb_of_le hp1 hpos h2
    have h4 : Real.logb p ((p : ℝ) ^ 2 * (8 * a + r) ^ 2) = 2 + 2 * Real.logb p (8 * a + r) := by
      rw [Real.logb_mul (by positivity) (by positivity), Real.logb_pow, Real.logb_pow,
        Real.logb_self_eq_one hp1]
      push_cast
      ring
    unfold lgV2
    linarith
  have hc : ((r.choose 2 : ℕ) : ℝ) * 2 ≤ (r : ℝ) ^ 2 := by
    have hn : r.choose 2 * 2 ≤ r ^ 2 := by
      rw [Nat.choose_two_right]
      calc r * (r - 1) / 2 * 2 ≤ r * (r - 1) := Nat.div_mul_le_self _ _
        _ ≤ r ^ 2 := by
          rw [sq]
          exact Nat.mul_le_mul_left _ (Nat.sub_le _ _)
    exact_mod_cast hn
  unfold kapC
  push_cast
  calc ((r.choose 2 : ℕ) : ℝ) * ((Nat.log p (d + r - 1) : ℕ) : ℝ)
      ≤ ((r.choose 2 : ℕ) : ℝ) * (2 * lgV2 p a r) := mul_le_mul_of_nonneg_left hL (Nat.cast_nonneg _)
    _ = (((r.choose 2 : ℕ) : ℝ) * 2) * lgV2 p a r := by ring
    _ ≤ (r : ℝ) ^ 2 * lgV2 p a r := mul_le_mul_of_nonneg_right hc hlg

theorem kappa_le_height_bound : ∀ (p : ℕ) [Fact p.Prime] (N r : ℕ) (LL : Letters N) (a : ℕ) (κ : ℝ),
    (∀ x, LL.deg x ≤ 2 * a) → 2 * a * N + r ≤ p ^ 2 * (8 * a + r) ^ 2 →
    ((N + 2) * r ^ 2 : ℝ) * lgV2 p a r ≤ κ → kapC p r LL.total ≤ ⌈κ / (N + 2)⌉₊ := by
  intro p _ N r LL a κ hdeg hpa hκ
  have htot := total_le LL (2 * a) hdeg
  have hk := kapC_le_real p r LL.total a (le_trans (Nat.add_le_add_right htot r) hpa)
  have hpos : (0 : ℝ) < (N : ℝ) + 2 := by positivity
  have hb : (r : ℝ) ^ 2 * lgV2 p a r ≤ κ / ((N : ℝ) + 2) := by
    rw [le_div_iff₀ hpos]
    calc (r : ℝ) ^ 2 * lgV2 p a r * ((N : ℝ) + 2) = ((N + 2) * r ^ 2 : ℝ) * lgV2 p a r := by ring
      _ ≤ κ := hκ
  exact Nat.cast_le.1 ((hk.trans hb).trans (Nat.le_ceil _))

theorem discharge_of_pwe (hP : DischargeP) (hW : DischargeW) (hE : DischargeE) : HeightBoundImplication := by
  intro p _ N r LL ρ a κ hdeg hpa hκ
  have hk := kappa_le_height_bound p N r LL a κ hdeg hpa hκ
  exact ⟨hP p N r LL ρ _ hk, hW p N r LL _ hk, hE p N r LL ρ _ hk⟩

end Formalism.InvariantFactorPaths.PW
