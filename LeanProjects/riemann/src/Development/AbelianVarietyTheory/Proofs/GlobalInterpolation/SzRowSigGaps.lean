import Mathlib
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PairRowIffQdRows
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LogAddRpowMulLogPowLeRpow

open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem rankVal_crude (s : Scale) (R : Ranks) (hx : 2 ≤ s.x) (h : RankVal s R) :
    (0 < (R.n : ℝ) ∧ (R.n : ℝ) ≤ s.x ^ 4) ∧ (R.m : ℝ) ≤ s.x ^ 2 ∧ (R.k : ℝ) ≤ s.x ^ 6 := by
  have hn1 := h.n_lo
  have hn2 := h.n_le'
  obtain ⟨-, ⟨-, hm⟩, ⟨-, hk⟩, -⟩ := h
  have hx1 : 1 ≤ s.x := by linarith
  have hx0 : 0 < s.x := by linarith
  have he := s.eps_pos
  have he' := s.eps_lt
  refine ⟨⟨lt_of_lt_of_le (Real.rpow_pos_of_pos hx0 _) hn1, ?_⟩, ?_, ?_⟩
  · have h1 : s.x ^ ((9 : ℝ) / 4) ≤ s.x ^ ((3 : ℕ) : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hx1 (by push_cast; norm_num)
    rw [Real.rpow_natCast] at h1
    have h2 : 0 < s.x ^ 3 := by positivity
    have h3 : s.x ^ 4 = s.x * s.x ^ 3 := by ring
    nlinarith
  · have h1 : s.delta1 ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx1 (by linarith)
    have h2 : Real.sqrt (s.x * s.delta1) ≤ s.x := by
      apply Real.sqrt_le_iff.2
      refine ⟨hx0.le, ?_⟩
      nlinarith
    nlinarith
  · have h1 : s.x ^ (9 / 2 + 10 * s.eps) ≤ s.x ^ ((5 : ℕ) : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hx1 (by push_cast; linarith)
    rw [Real.rpow_natCast] at h1
    have h2 : 0 < s.x ^ 5 := by positivity
    have h3 : s.x ^ 6 = s.x * s.x ^ 5 := by ring
    nlinarith

theorem gap_crude (x C k m t : ℝ) (hx : 2 ≤ x) (hC : C ≤ x) (hk0 : 0 ≤ k) (hm0 : 0 ≤ m) (ht0 : 0 ≤ t)
    (hm : m ≤ x ^ 2) (hk : k ≤ x ^ 6) (ht : t ≤ x ^ 401) :
    C * k * m ^ 4 + (k + m * (t + 1)) * m ^ 10 < x ^ 430 := by
  have hx1 : 1 ≤ x := by linarith
  have hx0 : 0 < x := by linarith
  have a1 : C * k * m ^ 4 ≤ x * x ^ 6 * (x ^ 2) ^ 4 := by
    have : C * k * m ^ 4 ≤ x * k * m ^ 4 := by gcongr
    refine this.trans ?_
    gcongr
  have a2 : (1 : ℝ) ≤ x ^ 401 := one_le_pow₀ hx1
  have a3 : (k + m * (t + 1)) * m ^ 10 ≤ (x ^ 6 + x ^ 2 * (x ^ 401 + x ^ 401)) * (x ^ 2) ^ 10 := by gcongr
  have a4 : x * x ^ 6 * (x ^ 2) ^ 4 = x ^ 15 := by ring
  have a5 : (x ^ 6 + x ^ 2 * (x ^ 401 + x ^ 401)) * (x ^ 2) ^ 10 = x ^ 26 + 2 * x ^ 423 := by ring
  have a6 : x ^ 15 ≤ x ^ 423 := pow_le_pow_right₀ hx1 (by norm_num)
  have a7 : x ^ 26 ≤ x ^ 423 := pow_le_pow_right₀ hx1 (by norm_num)
  have a8 : (2 : ℝ) ^ 7 ≤ x ^ 7 := by gcongr
  have a9 : x ^ 430 = x ^ 7 * x ^ 423 := by ring
  have a10 : 0 < x ^ 423 := by positivity
  have a11 : 2 ^ 7 * x ^ 423 ≤ x ^ 7 * x ^ 423 := by gcongr
  rw [a9]
  rw [a4] at a1
  rw [a5] at a3
  generalize x ^ 423 = y at *
  linarith

theorem base_sizes_ge (eps : ℝ) (he : 0 < eps) : ∃ x0 : ℝ, ∀ (s : Scale) (n : ℕ), s.eps = eps → x0 ≤ s.x →
    0 < (n : ℝ) → (n : ℝ) ≤ s.x ^ 4 → s.x ^ 430 ≤ s.b ∧ s.x ^ 430 ≤ s.b' ∧ s.x ^ 430 ≤ s.w'' n := by
  obtain ⟨x0, h0⟩ := GlobalTheory.log_add_rpow_mul_log_pow_le_rpow (eps / 3) eps 434 1 1 0 (by positivity)
    (by linarith) one_pos
  refine ⟨x0, fun s n hs hx hn0 hn => ?_⟩
  have hx1 : 1 ≤ s.x := s.one_lt_alt.le
  have hx0 : 0 < s.x := by linarith
  have h1 := h0 s.x hx
  rw [← hs] at h1
  simp only [pow_zero, one_mul, mul_one] at h1
  have hX0 : 0 < s.X' := Real.exp_pos _
  have hX1 : 1 ≤ s.X' := Real.one_le_exp (Real.rpow_nonneg hx0.le _)
  have h2 : s.x ^ 434 * s.X' ≤ s.b := by
    have e : s.x ^ 434 = Real.exp (434 * Real.log s.x) := by
      rw [show (434 : ℝ) = ((434 : ℕ) : ℝ) by norm_num, Real.exp_nat_mul, Real.exp_log hx0]
    rw [e, Scale.X', Scale.b, Scale.L, ← Real.exp_add]
    exact Real.exp_le_exp.2 (by linarith)
  have h3 : s.x ^ 430 ≤ s.x ^ 434 := pow_le_pow_right₀ hx1 (by norm_num)
  have h4 : s.x ^ 434 ≤ s.b / s.X' := (le_div_iff₀ hX0).2 h2
  have h5 : 0 < s.x ^ 434 := by positivity
  refine ⟨?_, ?_, ?_⟩
  · exact h3.trans ((le_mul_of_one_le_right h5.le hX1).trans h2)
  · have e : s.b' = s.x * (s.b / s.X') := by rw [Scale.b', Scale.a]; ring
    rw [e]
    exact h3.trans (h4.trans (le_mul_of_one_le_left (h5.le.trans h4) hx1))
  · have e : s.w'' n = (s.b / s.X') / n := by
      rw [Scale.w'', Scale.b', Scale.a]; field_simp
    rw [e, le_div_iff₀ hn0]
    refine le_trans ?_ h4
    calc s.x ^ 430 * n ≤ s.x ^ 430 * s.x ^ 4 := by gcongr
      _ = s.x ^ 434 := by ring

theorem szRow_sig_gaps : SzRow (fun C D L => (∀ τ, (∀ (i : ℕ) (h : i + 1 < D.R.k - 1), gapS D C.P.Cgap < (((D.hc τ).v ⟨i, by omega⟩ - (D.hc τ).v ⟨i + 1, h⟩ : ℚ) : ℝ)) ∧ (∀ (hk : 2 ≤ D.R.k) (hm : 0 < D.R.m), gapS D C.P.Cgap < (((D.hc τ).v ⟨D.R.k - 2, by omega⟩ + (D.hc τ).b ⟨0, hm⟩ : ℚ) : ℝ)) ∧ (∀ (j : ℕ) (h : j + 1 < D.R.m), gapS D C.P.Cgap < (((D.hc τ).b ⟨j + 1, h⟩ - (D.hc τ).b ⟨j, by omega⟩ : ℚ) : ℝ)))) := by
  intro eps he _ C hC
  obtain ⟨x0, hx0⟩ := base_sizes_ge eps he
  refine ⟨430, fun cD hcD => ⟨430, fun ch hch => ⟨max x0 (max 2 C.P.Cgap), fun D L hs hx hV => ?_⟩⟩⟩
  have hxa : x0 ≤ L.sc.x := (le_max_left _ _).trans hx
  have hx2 : 2 ≤ L.sc.x := ((le_max_left _ _).trans (le_max_right _ _)).trans hx
  have hxC : C.P.Cgap ≤ L.sc.x := ((le_max_right _ _).trans (le_max_right _ _)).trans hx
  have hx1 : 1 ≤ L.sc.x := by linarith
  obtain ⟨⟨hn0, hn⟩, hm, hk⟩ := rankVal_crude L.sc D.R hx2 hV.ranks
  obtain ⟨hb, hb', hw⟩ := hx0 L.sc D.R.n hs hxa hn0 hn
  have ht : (D.R.t : ℝ) ≤ L.sc.x ^ 401 := by
    have h1 := L.t_win.2
    rw [hV.Ct_eq, hC.1.2.2.2.2.2.2.2.2.2, show (401 : ℝ) = ((401 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at h1
    exact h1
  have hg : gapS D C.P.Cgap < L.sc.x ^ 430 := by
    have := gap_crude L.sc.x C.P.Cgap D.R.k D.R.m D.R.t hx2 hxC (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      (Nat.cast_nonneg _) hm hk ht
    unfold gapS Ranks.N
    push_cast
    exact this
  have hp : 0 < L.sc.x ^ 430 := by positivity
  have hpow : ∀ c : ℝ, 430 ≤ c → L.sc.x ^ 430 ≤ (⌈L.sc.x ^ c⌉₊ : ℝ) := by
    intro c hc
    refine le_trans ?_ (Nat.le_ceil _)
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hx1 (by push_cast; exact hc)
  obtain ⟨hv, -, ⟨b1, hbj, htop, hthick, hthin⟩, -⟩ := hV.hc
  have hb1 : ∀ τ, L.sc.x ^ 430 ≤ (b1 τ : ℝ) := by
    intro τ
    by_cases h1 : (D.eTau τ : D.R.GG) ∈ D.host.topPlaces
    · classical
      unfold Host.topPlaces at h1
      obtain ⟨t, htT, hteq⟩ := Finset.mem_image.1 h1
      rw [htop τ ⟨t, htT⟩ hteq.symm]
      have h2 := L.bT_ge ⟨t, htT⟩
      have h3 : (0 : ℝ) ≤ (⌊L.sc.b' / L.sc.x⌋ : ℤ) := by
        exact_mod_cast Int.floor_nonneg.2 (div_nonneg (by linarith) (by linarith))
      push_cast
      linarith
    · by_cases h2 : (D.eTau τ : D.R.GG) ∈ D.host.thickPlaces
      · have h3 := Int.le_ceil L.sc.b
        have h4 : ((⌈L.sc.b⌉ : ℤ) : ℝ) ≤ (b1 τ : ℝ) := by exact_mod_cast (hthick τ h2).1
        linarith
      · rw [hthin τ ⟨(D.eTau τ).2, h1, h2⟩]
        exact hw.trans (Int.le_ceil _)
  generalize L.sc.x ^ 430 = y at *
  intro τ
  refine ⟨fun i h => ?_, fun hk2 hm0 => ?_, fun j h => ?_⟩
  · rw [hv, hv]
    have e : D.R.k - 2 - i = (D.R.k - 2 - (i + 1)) + 1 := by omega
    simp only [e]
    have := hpow cD hcD
    unfold Delv
    push_cast
    linarith
  · rw [hv, (hbj τ _).1]
    have := hb1 τ
    simp only [Nat.sub_self]
    push_cast
    linarith
  · rw [(hbj τ _).1, (hbj τ _).1]
    have := hpow ch hch
    unfold h0v
    push_cast
    linarith

end GlobalTheory.EX
