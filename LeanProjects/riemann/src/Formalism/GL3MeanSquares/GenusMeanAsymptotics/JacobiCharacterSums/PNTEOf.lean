import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.DeuringHeilbronnM

open Finset Complex Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds Formalism.ZeroFreeDirichlet

theorem cZ_pos : 0 < cZ :=
  lt_min (Classical.choose_spec Formalism.ZeroFreeDirichlet.zFRDirichlet).1 (by norm_num)

theorem cZ_le : cZ ≤ 1 / 20 :=
  min_le_right _ _

theorem inRegion_mono {c c' : ℝ} (hc : c ≤ c') (q : ℕ) [NeZero q] (s : ℂ) (hs : InRegion c q s) :
    InRegion c' q s := by
  unfold InRegion at hs ⊢
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hlog : 0 < Real.log ((q : ℝ) * (|s.im| + 2)) :=
    Real.log_pos (by nlinarith [abs_nonneg s.im])
  have h1 : c / Real.log ((q : ℝ) * (|s.im| + 2)) ≤ c' / Real.log ((q : ℝ) * (|s.im| + 2)) :=
    div_le_div_of_nonneg_right hc hlog.le
  linarith

theorem zfr_cZ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ) (hs : InRegion cZ q s)
    (hz : IsLZero χ s) :
    χ ^ 2 = 1 ∧ χ ≠ 1 ∧ s.im = 0 ∧ deriv (DirichletCharacter.LFunction χ) s ≠ 0 ∧
      ∀ (χ' : DirichletCharacter ℂ q) (s' : ℂ), InRegion cZ q s' → IsLZero χ' s' → χ' = χ ∧ s' = s := by
  have hZ := Classical.choose_spec Formalism.ZeroFreeDirichlet.zFRDirichlet
  have hle : cZ ≤ Classical.choose Formalism.ZeroFreeDirichlet.zFRDirichlet := min_le_left _ _
  obtain ⟨h1, h2, h3, h4, h5⟩ := hZ.2 q χ s (inRegion_mono hle q s hs) hz
  exact ⟨h1, h2, h3, h4, fun χ' s' hs' hz' => h5 χ' s' (inRegion_mono hle q s' hs') hz'⟩

theorem eOf_cases (M : ℕ) [NeZero M] :
    (∃ p : DirichletCharacter ℂ M × ℝ, eOf M = some p ∧ IsExcPair p.1 p.2 ∧ InRegion cZ M (p.2 : ℂ)) ∨
    (∃ p : DirichletCharacter ℂ M × ℝ, eOf M = some p ∧ IsExcPair p.1 p.2 ∧
      ∀ p' : DirichletCharacter ℂ M × ℝ, IsExcPair p'.1 p'.2 → ¬ InRegion cZ M (p'.2 : ℂ)) ∨
    (eOf M = none ∧ ∀ p' : DirichletCharacter ℂ M × ℝ, ¬ IsExcPair p'.1 p'.2) := by
  unfold eOf
  split_ifs with h h'
  · exact Or.inl ⟨h.choose, rfl, h.choose_spec.1, h.choose_spec.2⟩
  · exact Or.inr (Or.inl ⟨h'.choose, rfl, h'.choose_spec, fun p' hp' hr => h ⟨p', hp', hr⟩⟩)
  · exact Or.inr (Or.inr ⟨rfl, fun p' hp' => h' ⟨p', hp'⟩⟩)

theorem eOf_exc (M : ℕ) [NeZero M] (p : DirichletCharacter ℂ M × ℝ) (h : eOf M = some p) :
    IsExcPair p.1 p.2 := by
  rcases eOf_cases M with ⟨q, hq, hex, _⟩ | ⟨q, hq, hex, _⟩ | ⟨hn, _⟩
  · rw [h] at hq
    cases hq
    exact hex
  · rw [h] at hq
    cases hq
    exact hex
  · rw [h] at hn
    cases hn

theorem eOf_none (M : ℕ) [NeZero M] (h : eOf M = none) (χ₁ : DirichletCharacter ℂ M) (β₁ : ℝ) :
    ¬ IsExcPair χ₁ β₁ := by
  rcases eOf_cases M with ⟨q, hq, _, _⟩ | ⟨q, hq, _, _⟩ | ⟨_, hno⟩
  · rw [h] at hq
    cases hq
  · rw [h] at hq
    cases hq
  · exact hno (χ₁, β₁)

theorem inRegion_ofReal (c : ℝ) (q : ℕ) (β : ℝ) :
    InRegion c q (β : ℂ) ↔ 1 - c / Real.log ((q : ℝ) * 2) ≤ β := by
  unfold InRegion
  rw [Complex.ofReal_im, Complex.ofReal_re, abs_zero, zero_add]

theorem log_two_mul_le (M : ℕ) (hM : 2 ≤ M) : Real.log ((M : ℝ) * 2) ≤ 2 * Real.log M := by
  have hM' : (2 : ℝ) ≤ M := by exact_mod_cast hM
  rw [Real.log_mul (by positivity) (by norm_num)]
  have h1 : Real.log 2 ≤ Real.log M := Real.log_le_log (by norm_num) hM'
  linarith

theorem log_pos_of_two_le (M : ℕ) (hM : 2 ≤ M) : 0 < Real.log M := by
  apply Real.log_pos
  exact_mod_cast (show 1 < M by omega)

theorem isExcPair_of_region (M : ℕ) [NeZero M] (hM : 2 ≤ M) (χ : DirichletCharacter ℂ M) (β : ℝ)
    (h2 : χ ^ 2 = 1) (h1 : χ ≠ 1) (hz : DirichletCharacter.LFunction χ (β : ℂ) = 0)
    (hr : InRegion cZ M (β : ℂ)) : IsExcPair χ β := by
  refine ⟨h2, h1, hz, ?_, ?_⟩
  · rw [inRegion_ofReal] at hr
    have hlogM := log_pos_of_two_le M hM
    have hM' : (2 : ℝ) ≤ M := by exact_mod_cast hM
    have hlogge : Real.log M ≤ Real.log ((M : ℝ) * 2) := Real.log_le_log (by positivity) (by nlinarith)
    have hcz := cZ_le
    have hcz0 := cZ_pos
    have hlog2pos : 0 < Real.log ((M : ℝ) * 2) := lt_of_lt_of_le hlogM hlogge
    have h3 : cZ / Real.log ((M : ℝ) * 2) < 1 / (8 * Real.log M) := by
      rw [div_lt_div_iff₀ hlog2pos (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_right hcz hlogM.le]
    linarith
  · by_contra hge
    push_neg at hge
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl h1) (by simpa using hge) hz

theorem zero_in_region (M : ℕ) [NeZero M] (hM : 2 ≤ M) (χ : DirichletCharacter ℂ M) (s : ℂ)
    (hs : InRegion cZ M s) (hz : IsLZero χ s) :
    ∃ β₁ : ℝ, eOf M = some (χ, β₁) ∧ s = (β₁ : ℂ) ∧ deriv (DirichletCharacter.LFunction χ) s ≠ 0 := by
  obtain ⟨h2, h1, him, hder, huniq⟩ := zfr_cZ M χ s hs hz
  have hs' : s = ((s.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [him])
  have hzr : DirichletCharacter.LFunction χ ((s.re : ℝ) : ℂ) = 0 := by rw [← hs']; exact hz.2
  have hrr : InRegion cZ M ((s.re : ℝ) : ℂ) := by rw [← hs']; exact hs
  have hex : IsExcPair χ s.re := isExcPair_of_region M hM χ s.re h2 h1 hzr hrr
  rcases eOf_cases M with ⟨p, hp, hpex, hpr⟩ | ⟨p, hp, hpex, hno⟩ | ⟨hn, hno⟩
  · have hz' : IsLZero p.1 (p.2 : ℂ) := ⟨Or.inl hpex.2.1, hpex.2.2.1⟩
    obtain ⟨e1, e2⟩ := huniq p.1 (p.2 : ℂ) hpr hz'
    refine ⟨p.2, ?_, e2.symm, hder⟩
    rw [hp, ← e1]
  · exact absurd hrr (hno (χ, s.re) hex)
  · exact absurd hex (hno (χ, s.re))

theorem etaOf_some (M : ℕ) [NeZero M] (χ₁ : DirichletCharacter ℂ M) (β₁ : ℝ) (h : eOf M = some (χ₁, β₁)) :
    etaOf M = min 1 ((1 - β₁) * Real.log M) := by
  unfold etaOf
  rw [h]

theorem etaOf_none (M : ℕ) [NeZero M] (h : eOf M = none) : etaOf M = 1 := by
  unfold etaOf
  rw [h]

theorem etaOf_pos (M : ℕ) [NeZero M] (hM : 2 ≤ M) : 0 < etaOf M := by
  rcases hE : eOf M with _ | ⟨χ₁, β₁⟩
  · rw [etaOf_none M hE]
    exact one_pos
  · rw [etaOf_some M χ₁ β₁ hE]
    have hex := eOf_exc M (χ₁, β₁) hE
    exact lt_min one_pos (mul_pos (by linarith [hex.2.2.2.2]) (log_pos_of_two_le M hM))

theorem etaOf_le_one (M : ℕ) [NeZero M] : etaOf M ≤ 1 := by
  rcases hE : eOf M with _ | ⟨χ₁, β₁⟩
  · rw [etaOf_none M hE]
  · rw [etaOf_some M χ₁ β₁ hE]
    exact min_le_left _ _

theorem etaOf_lower (ε : ℝ) (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ ∀ (M : ℕ) [NeZero M], 3 ≤ M → c * (M : ℝ) ^ (-ε) ≤ etaOf M := by
  obtain ⟨c, hc, hb⟩ := Formalism.ZeroFreeDirichlet.excBound ε hε
  refine ⟨min 1 (c * Real.log 3), lt_min one_pos (mul_pos hc (Real.log_pos (by norm_num))), fun M _ hM => ?_⟩
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast (show 1 ≤ M by omega)
  have hpow : (M : ℝ) ^ (-ε) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hM1 (by linarith)
  have hpow0 : 0 < (M : ℝ) ^ (-ε) := Real.rpow_pos_of_pos (by linarith) _
  have hle1 : min 1 (c * Real.log 3) * (M : ℝ) ^ (-ε) ≤ 1 := by
    calc min 1 (c * Real.log 3) * (M : ℝ) ^ (-ε) ≤ 1 * 1 :=
          mul_le_mul (min_le_left _ _) hpow hpow0.le zero_le_one
      _ = 1 := one_mul 1
  rcases hE : eOf M with _ | ⟨χ₁, β₁⟩
  · rw [etaOf_none M hE]
    exact hle1
  · rw [etaOf_some M χ₁ β₁ hE]
    have hex := eOf_exc M (χ₁, β₁) hE
    have hβ := hb M χ₁ β₁ hex.1 hex.2.1 hex.2.2.1
    have hlog3 : Real.log 3 ≤ Real.log M := Real.log_le_log (by norm_num) (by exact_mod_cast hM)
    have hlogM : 0 ≤ Real.log M := le_trans (Real.log_nonneg (by norm_num)) hlog3
    have h1 : c * (M : ℝ) ^ (-ε) ≤ 1 - β₁ := by linarith
    apply le_min hle1
    calc min 1 (c * Real.log 3) * (M : ℝ) ^ (-ε) ≤ (c * Real.log 3) * (M : ℝ) ^ (-ε) :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) hpow0.le
      _ ≤ (c * Real.log M) * (M : ℝ) ^ (-ε) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlog3 hc.le) hpow0.le
      _ = (c * (M : ℝ) ^ (-ε)) * Real.log M := by ring
      _ ≤ (1 - β₁) * Real.log M := mul_le_mul_of_nonneg_right h1 hlogM

theorem etaOf_far (M : ℕ) [NeZero M] (hM : 2 ≤ M) (χ₁ : DirichletCharacter ℂ M) (β₁ : ℝ)
    (h : eOf M = some (χ₁, β₁)) (hr : ¬ InRegion cZ M (β₁ : ℂ)) : cZ / 2 ≤ etaOf M := by
  rw [etaOf_some M χ₁ β₁ h]
  rw [inRegion_ofReal] at hr
  push_neg at hr
  have hlogM := log_pos_of_two_le M hM
  have hlog2 := log_two_mul_le M hM
  have hM' : (2 : ℝ) ≤ M := by exact_mod_cast hM
  have hlogge : Real.log M ≤ Real.log ((M : ℝ) * 2) := Real.log_le_log (by positivity) (by nlinarith)
  have hlog2pos : 0 < Real.log ((M : ℝ) * 2) := lt_of_lt_of_le hlogM hlogge
  have hcz := cZ_le
  have hcz0 := cZ_pos
  have h1 : cZ / Real.log ((M : ℝ) * 2) < 1 - β₁ := by linarith
  have hb : 0 < 1 - β₁ := lt_trans (div_pos hcz0 hlog2pos) h1
  rw [div_lt_iff₀ hlog2pos] at h1
  have h2 : cZ / 2 ≤ (1 - β₁) * Real.log M := by
    nlinarith [mul_le_mul_of_nonneg_left hlog2 hb.le]
  exact le_min (by linarith) h2

theorem eOf_char_sq (M : ℕ) [NeZero M] (χ₁ : DirichletCharacter ℂ M) (β₁ : ℝ) (h : eOf M = some (χ₁, β₁))
    (b : ZMod M) (hb : IsUnit b) : χ₁ b = 1 ∨ χ₁ b = -1 := by
  have hex := eOf_exc M (χ₁, β₁) h
  have h2 : (χ₁ ^ 2) b = 1 := by
    rw [hex.1]
    exact MulChar.one_apply hb
  rw [MulChar.pow_apply' χ₁ (by norm_num)] at h2
  exact mul_self_eq_one_iff.mp (by rw [← sq]; exact h2)

end Formalism.HermitianLattices.Ext.PrimesInProgressions
