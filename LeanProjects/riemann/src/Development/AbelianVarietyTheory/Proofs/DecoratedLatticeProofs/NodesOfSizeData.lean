import Formalism.SharpRestriction.CuspSpanNormBounds.StandingHypothesesHoldFamily
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ToGlob0
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.Diag.PG

noncomputable section

namespace GlobalTheory.Diag.PG.NodeParameters

theorem y_ge {eps x : ℝ} (he : 0 < eps) (hx : (4 + 18 / eps) ^ (3 / eps) ≤ x) :
    4 + 18 / eps ≤ x ^ (eps / 3) := by
  have h0 : 0 ≤ 4 + 18 / eps := by positivity
  calc 4 + 18 / eps = ((4 + 18 / eps) ^ (3 / eps)) ^ (eps / 3) := by
        rw [← Real.rpow_mul h0]
        have : 3 / eps * (eps / 3) = 1 := by field_simp
        rw [this, Real.rpow_one]
    _ ≤ x ^ (eps / 3) := Real.rpow_le_rpow (by positivity) hx (by positivity)

theorem xeps_eq {eps x : ℝ} (hx : 0 ≤ x) : x ^ eps = (x ^ (eps / 3)) ^ 3 := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]; congr 1; push_cast; ring

theorem logx_le' {eps x : ℝ} (he : 0 < eps) (hx : 0 ≤ x) : Real.log x ≤ 3 * x ^ (eps / 3) / eps := by
  have := Real.log_le_rpow_div hx (by positivity : 0 < eps / 3)
  calc _ ≤ _ := this
    _ = _ := by field_simp

theorem poly {eps y : ℝ} (he : 0 < eps) (hy : 4 + 18 / eps ≤ y) :
    2 + 2 * y + 6 * (3 * y / eps) ≤ y ^ 3 ∧ 2 + 5 * (3 * y / eps) ≤ y ^ 3 := by
  have hq : 0 ≤ 18 / eps := by positivity
  have h1 : 1 ≤ y := by linarith
  have h2 : y * (4 + 18 / eps) ≤ y ^ 2 := by rw [sq]; exact mul_le_mul_of_nonneg_left hy (by linarith)
  have h3 : y ^ 2 ≤ y ^ 3 := pow_le_pow_right₀ h1 (by norm_num)
  have e1 : 6 * (3 * y / eps) = y * (18 / eps) := by ring
  have e2 : 5 * (3 * y / eps) = y * (15 / eps) := by ring
  have h4 : y * (15 / eps) ≤ y * (18 / eps) :=
    mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (by norm_num) he.le) (by linarith)
  have h5 : 0 ≤ y * (18 / eps) := by positivity
  rw [e1, e2]
  constructor <;> nlinarith

theorem exp_big {eps x : ℝ} (he : 0 < eps) (hx1 : 1 ≤ x) (hx : (4 + 18 / eps) ^ (3 / eps) ≤ x) :
    4 * Real.exp (x ^ (eps / 3)) ^ 2 * x ^ 6 ≤ Real.exp (x ^ eps) ∧
      3 * x ^ 5 ≤ Real.exp (x ^ eps) := by
  have hx0 : 0 < x := by linarith
  have hyg := y_ge he hx
  obtain ⟨p1, p2⟩ := poly he hyg
  have hl := logx_le' he hx0.le
  have hxe : x ^ eps = (x ^ (eps / 3)) ^ 3 := xeps_eq hx0.le
  rw [hxe]
  set y := x ^ (eps / 3) with hy
  have h4 : (4 : ℝ) ≤ Real.exp 2 := by
    have := Real.add_one_le_exp (1 : ℝ)
    have e : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    nlinarith
  have h3 : (3 : ℝ) ≤ Real.exp 2 := by linarith
  have ex : x = Real.exp (Real.log x) := (Real.exp_log hx0).symm
  constructor
  · calc 4 * Real.exp y ^ 2 * x ^ 6 ≤ Real.exp 2 * Real.exp y ^ 2 * Real.exp (Real.log x) ^ 6 := by
          rw [← ex]; gcongr
      _ = Real.exp (2 + 2 * y + 6 * Real.log x) := by
          rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]; push_cast; ring_nf
      _ ≤ Real.exp (y ^ 3) := Real.exp_le_exp.2 (by nlinarith)
  · calc 3 * x ^ 5 ≤ Real.exp 2 * Real.exp (Real.log x) ^ 5 := by
          rw [← ex]; gcongr
      _ = Real.exp (2 + 5 * Real.log x) := by
          rw [← Real.exp_nat_mul, ← Real.exp_add]; push_cast; ring_nf
      _ ≤ Real.exp (y ^ 3) := Real.exp_le_exp.2 (by nlinarith)

end GlobalTheory.Diag.PG.NodeParameters

namespace GlobalTheory.Diag.PG.NodeParameters

theorem w''_eq {D : D7} (L : SizeData₂ D) : L.sc.w'' D.R.n = L.sc.b / (L.sc.X' * D.R.n) := by
  have hx : 0 < L.sc.x := lt_trans one_pos L.sc.one_lt_alt
  have hn : (0 : ℝ) < D.R.n := by
    have : 0 < D.R.n := D.R.ord_pos
    exact_mod_cast this
  have hX : 0 < L.sc.X' := by unfold Scale.X'; positivity
  unfold Scale.w'' Scale.b' Scale.a
  field_simp

theorem top_real {x b a c k aT bT bp b1 u1 uk s : ℝ} (hx1 : 1 ≤ x) (hb1 : 1 ≤ b) (ha : a = x * b) (hc : 1 ≤ c)
    (hk : 3 ≤ k) (hk5 : k ≤ x ^ 5) (hB : 3 * x ^ 5 ≤ b) (hs : s ≤ b)
    (hu1 : u1 = aT + (k - 1) / 2) (huk : uk = -bT - (k - 1) / 2)
    (haT : a ≤ aT ∧ aT ≤ a + a / c) (hbT : bp ≤ bT) (hbp : 0 ≤ bp)
    (hb1t : b1 - bT > (k - 1) / 2 + 3) (hb1e : b1 = bT + ((⌊bp / x⌋ : ℤ) : ℝ)) :
    s ≤ u1 ∧ u1 ≤ b ^ 2 ∧ 3 ≤ b1 + uk ∧ b1 / 2 ≤ -uk := by
  have hb0 : 0 ≤ b := by linarith
  have hx0 : 0 ≤ x := by linarith
  have ha0 : 0 ≤ a := by rw [ha]; positivity
  have hab : b ≤ a := by rw [ha]; exact le_mul_of_one_le_left hb0 hx1
  have hdiv : a / c ≤ a := div_le_self ha0 hc
  have hfl : ((⌊bp / x⌋ : ℤ) : ℝ) ≤ bp / x := Int.floor_le _
  have hbx : bp / x ≤ bp := div_le_self hbp hx1
  have hx5 : x ≤ x ^ 5 := by
    have := pow_le_pow_right₀ hx1 (by norm_num : 1 ≤ 5); simpa using this
  have h1 : x * b ≤ x ^ 5 * b := mul_le_mul_of_nonneg_right hx5 hb0
  have h2 : x ^ 5 ≤ x ^ 5 * b := le_mul_of_one_le_right (by positivity) hb1
  have h3 : 3 * x ^ 5 * b ≤ b * b := mul_le_mul_of_nonneg_right hB hb0
  refine ⟨?_, ?_, ?_, ?_⟩
  · linarith only [hs, hab, haT.1, hu1, hk]
  · rw [sq]
    linarith only [hu1, haT.2, hdiv, ha, h1, h2, h3, hk5, hk]
  · linarith only [hb1t, huk]
  · linarith only [hb1e, hfl, hbx, hbT, huk, hk]

theorem node_real {bj ej w eta t x s : ℝ} (hw : w ≤ ej) (hc : -eta ≤ bj - ej) (ht : 1 ≤ t) (he : 0 < eta)
    (hte : t * eta ≤ w / x) (hx2 : 2 ≤ x) (hw0 : 0 < w) (hs : s ≤ w / 2) : s ≤ bj := by
  have h1 : eta ≤ t * eta := le_mul_of_one_le_left he.le ht
  have h2 : w / x ≤ w / 2 := div_le_div_of_nonneg_left hw0.le two_pos hx2
  linarith only [hw, hc, h1, h2, hte, hs]

theorem nodes_of_parameters : ∀ eps : ℝ, 0 < eps → eps < 1 / 52 → ∃ x0 : ℝ, ∀ (D : D7) (L : SizeData₂ D)
    (_ : ParameterChoice' D L), SizesAt L → L.sc.eps = eps → x0 ≤ L.sc.x → Nodes D L.sc.x eps := by
  intro eps he he52
  refine ⟨max 2 ((4 + 18 / eps) ^ (3 / eps)), ?_⟩
  intro D L P hS heps hx
  subst heps
  have hx2 : 2 ≤ L.sc.x := le_trans (le_max_left _ _) hx
  have hxb : (4 + 18 / L.sc.eps) ^ (3 / L.sc.eps) ≤ L.sc.x := le_trans (le_max_right _ _) hx
  obtain ⟨hN, -, hK, -, hT, -, -, -, -, -, -, -, -, hEta, -, -, -, -, hBm, -⟩ := hS
  obtain ⟨hA, hB⟩ := exp_big he (by linarith) hxb
  have hx1 : (1 : ℝ) ≤ L.sc.x := by linarith
  have hx0 : (0 : ℝ) < L.sc.x := by linarith
  have hbdef : bx L.sc.x L.sc.eps = L.sc.b := rfl
  have hbe : Real.exp (L.sc.x ^ L.sc.eps) = L.sc.b := rfl
  have hXe : Real.exp (L.sc.x ^ (L.sc.eps / 3)) = L.sc.X' := rfl
  rw [hbe] at hA hB
  rw [hXe] at hA
  have hb1 : 1 ≤ L.sc.b := Real.one_le_exp (Real.rpow_nonneg hx0.le _)
  have hb0 : 0 < L.sc.b := by linarith
  have hX0 : 0 < L.sc.X' := by unfold Scale.X'; positivity
  have hn0 : (0 : ℝ) < D.R.n := by
    have : 0 < D.R.n := D.R.ord_pos
    exact_mod_cast this

  have hth : szTh L = L.sc.eps / 100 := rfl
  have hn3 : (D.R.n : ℝ) ≤ L.sc.x ^ 3 := by
    have h := hN.2
    rw [hth] at h
    have e := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith : 2 + 8 * L.sc.eps + L.sc.eps / 100 ≤ (3 : ℝ))
    have e3 : L.sc.x ^ (3 : ℝ) = L.sc.x ^ (3 : ℕ) := by
      rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [e3] at e
    exact le_trans h e
  have hk5 : (D.R.k : ℝ) ≤ L.sc.x ^ 5 := by
    have h := hK.2
    rw [hth] at h
    have e := Real.rpow_le_rpow_of_exponent_le hx1
      (by linarith : 9 / 2 + 10 * L.sc.eps + L.sc.eps / 100 ≤ (5 : ℝ))
    have e5 : L.sc.x ^ (5 : ℝ) = L.sc.x ^ (5 : ℕ) := by
      rw [show (5 : ℝ) = ((5 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [e5] at e
    exact le_trans h e

  have hw0 := S.w''_pos L
  have hsq : Real.sqrt L.sc.b ≤ L.sc.w'' D.R.n / 2 := by
    have hw := w''_eq L
    have hn6 : (D.R.n : ℝ) ^ 2 ≤ L.sc.x ^ 6 := by
      have := pow_le_pow_left₀ hn0.le hn3 2
      rw [← pow_mul] at this; simpa using this
    have h4 : 4 * L.sc.X' ^ 2 * (D.R.n : ℝ) ^ 2 ≤ L.sc.b := by
      have : 4 * L.sc.X' ^ 2 * (D.R.n : ℝ) ^ 2 ≤ 4 * L.sc.X' ^ 2 * L.sc.x ^ 6 :=
        mul_le_mul_of_nonneg_left hn6 (by positivity)
      linarith
    have hw0' : 0 ≤ L.sc.w'' D.R.n / 2 := by positivity
    rw [← Real.sqrt_sq hw0']
    apply Real.sqrt_le_sqrt
    rw [hw, div_div, div_pow, le_div_iff₀ (by positivity)]
    have := mul_le_mul_of_nonneg_left h4 hb0.le
    nlinarith
  have hwb := S.w''_le_b L
  have hk3 : 3 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
  have hk3r : (3 : ℝ) ≤ D.R.k := by exact_mod_cast hk3
  have hm0 : 0 < D.R.m := by have := D.R.two_le_m; omega
  refine ⟨?_, ?_, ?_⟩
  ·
    intro τ j
    refine ⟨?_, L.b_le τ j⟩
    have hwj := S.wj_ge L τ (j.1 + 1) (by omega) (by omega)
    have e : wj D (j.1 + 1) τ = (((D.hc τ).e j : ℚ) : ℝ) := by
      have : j.1 + 1 - 1 < D.R.m := by omega
      simp only [wj, dif_pos this]
      rfl
    rw [e] at hwj
    have hc := abs_le.1 (L.be_close τ j j)
    push_cast at hc
    rw [hbdef]
    exact node_real hwj hc.1 hT.1 L.etaSz_pos hEta.2.2.2.1 hx2 hw0 hsq
  ·
    intro τ
    exact hBm τ hm0
  ·
    rintro τ ⟨t, ht⟩
    have hk0 : 0 < D.R.k := by omega
    obtain ⟨hu1, huk⟩ := L.top_u τ t hk0 ht
    have hden : 1 ≤ (D.R.k : ℝ) * L.sc.x ^ (Scale.A / 2) := by
      have h1 : 1 ≤ L.sc.x ^ (Scale.A / 2) := Real.one_le_rpow hx1 (by unfold Scale.A; norm_num)
      have h2 : (1 : ℝ) ≤ D.R.k := by linarith
      calc (1 : ℝ) = 1 * 1 := by norm_num
        _ ≤ _ := mul_le_mul h2 h1 zero_le_one (by linarith)
    have hb'0 : 0 ≤ L.sc.b' := by unfold Scale.b' Scale.a Scale.b Scale.X'; positivity
    rw [hbdef]
    exact top_real hx1 hb1 rfl hden hk3r hk5 hB (le_trans hsq (by linarith)) hu1 huk (L.aT_win t) (L.bT_ge t) hb'0
      (L.top_b τ t hm0 ht) (P.topPlace_first_bound τ t hm0 ht)

end GlobalTheory.Diag.PG.NodeParameters
