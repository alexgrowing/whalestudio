import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.PerronTruncOf

namespace PI.EF.PK

open Complex MeasureTheory intervalIntegral Real

lemma seg_bound (f : ℝ → ℂ) (K a b : ℝ) (hab : a ≤ b) (h : ∀ x, a ≤ x → x ≤ b → ‖f x‖ ≤ K) :
    ‖∫ x in a..b, f x‖ ≤ K * (b - a) := by
  have hK := intervalIntegral.norm_integral_le_of_norm_le_const (f := f) (C := K) (a := a) (b := b)
    (fun x hx => by
      rw [Set.uIoc_of_le hab] at hx
      exact h x hx.1.le hx.2)
  rwa [abs_of_nonneg (sub_nonneg.mpr hab)] at hK

lemma continuous_inv_sqrt : Continuous fun t : ℝ => 2 * (√(1 + (2 * t) ^ 2))⁻¹ :=
  continuous_const.mul ((continuous_const.add ((continuous_const.mul continuous_id).pow 2)).sqrt.inv₀
    (fun t => (Real.sqrt_pos.mpr (by positivity : (0 : ℝ) < 1 + (2 * t) ^ 2)).ne'))

lemma integral_inv_sqrt (T : ℝ) :
    ∫ t in -T..T, 2 * (√(1 + (2 * t) ^ 2))⁻¹ = 2 * Real.arsinh (2 * T) := by
  have hd : ∀ t : ℝ, HasDerivAt (fun t => Real.arsinh (2 * t)) (2 * (√(1 + (2 * t) ^ 2))⁻¹) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => 2 * t) 2 t := by
      simpa using (hasDerivAt_id t).const_mul (2 : ℝ)
    have h2 := (Real.hasDerivAt_arsinh (2 * t)).comp t h1
    rw [mul_comm _ (2 : ℝ)] at h2
    exact h2
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)
    (continuous_inv_sqrt.intervalIntegrable _ _)]
  simp only [mul_neg, Real.arsinh_neg]
  ring

lemma arsinh_le (x : ℝ) (hx : 0 ≤ x) : Real.arsinh x ≤ Real.log (1 + 2 * x) := by
  have hs0 : 0 < √(1 + x ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have hs : √(1 + x ^ 2) ≤ 1 + x := by
    rw [Real.sqrt_le_iff]
    constructor
    · linarith
    · nlinarith
  unfold Real.arsinh
  exact Real.log_le_log (by linarith) (by linarith)

lemma norm_upow_div (u : ℝ) (hu : 1 ≤ u) (s : ℂ) (c m : ℝ) (hm : 0 < m) (hsc : s.re ≤ c)
    (hsm : m ≤ ‖s‖) : ‖(u : ℂ) ^ s / s‖ ≤ u ^ c / m := by
  rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos (by linarith)]
  exact div_le_div₀ (Real.rpow_pos_of_pos (by linarith) _).le
    (Real.rpow_le_rpow_of_exponent_le hu hsc) hm hsm

lemma norm_upow_div_left (u : ℝ) (hu : 1 ≤ u) (t : ℝ) :
    ‖(u : ℂ) ^ (((-1 / 2 : ℝ) : ℂ) + t * I) / (((-1 / 2 : ℝ) : ℂ) + t * I)‖ ≤
      2 * (√(1 + (2 * t) ^ 2))⁻¹ := by
  have hsq : 0 < √(1 + (2 * t) ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have hm : 0 < √(1 + (2 * t) ^ 2) / 2 := by positivity
  have hsm : √(1 + (2 * t) ^ 2) / 2 ≤ ‖(((-1 / 2 : ℝ) : ℂ) + t * I)‖ := by
    rw [Complex.norm_add_mul_I, Real.le_sqrt hm.le, div_pow, Real.sq_sqrt (by positivity)]
    · exact le_of_eq (by ring)
    · positivity
  have h1 := norm_upow_div u hu (((-1 / 2 : ℝ) : ℂ) + t * I) (-1 / 2) _ hm (by simp) hsm
  calc _ ≤ u ^ (-1 / 2 : ℝ) / (√(1 + (2 * t) ^ 2) / 2) := h1
    _ ≤ 1 / (√(1 + (2 * t) ^ 2) / 2) := by
        gcongr
        exact Real.rpow_le_one_of_one_le_of_nonpos hu (by norm_num)
    _ = 2 * (√(1 + (2 * t) ^ 2))⁻¹ := by field_simp

lemma combine {B Tp R Lf : ℂ} {b1 b2 b3 : ℝ} (h1 : ‖B‖ ≤ b1) (h2 : ‖Tp‖ ≤ b2) (h3 : ‖Lf‖ ≤ b3) :
    ‖B - Tp + I * R - I * Lf + -(I * R)‖ ≤ b1 + b2 + b3 := by
  have e : B - Tp + I * R - I * Lf + -(I * R) = B - Tp - I * Lf := by ring
  rw [e]
  have hI : ‖I * Lf‖ = ‖Lf‖ := by rw [norm_mul, Complex.norm_I, one_mul]
  have hs := norm_sub_le (B - Tp) (I * Lf)
  have hs2 := norm_sub_le B Tp
  linarith

lemma cLine_le_three {u : ℝ} (hu : 2 ≤ u) : cLine u ≤ 3 := by
  unfold cLine
  have h2 : (1 : ℝ) / 2 < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have hl : Real.log 2 ≤ Real.log u := Real.log_le_log (by norm_num) hu
  have hpos : 0 < Real.log u := by linarith
  have h3 : 1 / Real.log u ≤ 2 := by rw [div_le_iff₀ hpos]; linarith
  linarith

lemma rpow_cLine_le {u : ℝ} (hu : 2 ≤ u) : u ^ cLine u ≤ 3 * u := by
  have hu0 : 0 < u := by linarith
  have hl : 0 < Real.log u := Real.log_pos (by linarith)
  unfold cLine
  rw [Real.rpow_add hu0, Real.rpow_one, Real.rpow_def_of_pos hu0, mul_one_div_cancel hl.ne']
  have := Real.exp_one_lt_d9
  nlinarith

lemma log_le_two_mul {X Y : ℝ} (hX : 0 < X) (hXY : X ≤ Y ^ 2) : Real.log X ≤ 2 * Real.log Y := by
  calc Real.log X ≤ Real.log (Y ^ 2) := Real.log_le_log hX hXY
    _ = 2 * Real.log Y := by rw [Real.log_pow]; push_cast; ring

lemma log_facts {N : ℕ} {u T T' : ℝ} (hN : (1 : ℝ) ≤ N) (hT : 2 ≤ T) (hTu : T ≤ u) (hTT' : T ≤ T')
    (hT'1 : T' ≤ T + 1) :
    0 ≤ Real.log (N * u * T) ∧ Real.log (N * T') ≤ Real.log (N * u * T) ∧
      0 ≤ Real.log (N * T') ∧ Real.log (N * (T' + 2)) ≤ 2 * Real.log (N * u * T) ∧
      Real.log (1 + 2 * (2 * T')) ≤ 2 * Real.log (N * u * T) ∧ 0 ≤ Real.log (N * (T' + 2)) ∧
      0 ≤ Real.log (N * u) := by
  have hT0 : 0 < T := by linarith
  have hu2 : 2 ≤ u := le_trans hT hTu
  have hN0 : 0 < (N : ℝ) := by linarith
  have hT'2 : 2 ≤ T' := le_trans hT hTT'
  have hNu : 2 ≤ (N : ℝ) * u := by nlinarith
  have hNuT : 4 ≤ (N : ℝ) * u * T := by nlinarith
  have hY2 : (N : ℝ) * (4 * T ^ 2) ≤ ((N : ℝ) * u * T) ^ 2 := by
    have h1 : (N : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith
    have h2 : 4 * T ^ 2 ≤ u ^ 2 * T ^ 2 := by
      have hu4 : 4 ≤ u ^ 2 := by nlinarith
      exact mul_le_mul_of_nonneg_right hu4 (sq_nonneg T)
    calc (N : ℝ) * (4 * T ^ 2) ≤ (N : ℝ) ^ 2 * (u ^ 2 * T ^ 2) :=
          mul_le_mul h1 h2 (by positivity) (by positivity)
      _ = ((N : ℝ) * u * T) ^ 2 := by ring
  have hNT' : 1 ≤ (N : ℝ) * T' := by nlinarith
  have hNT'2 : 1 ≤ (N : ℝ) * (T' + 2) := by nlinarith
  refine ⟨Real.log_nonneg (by linarith), Real.log_le_log (by nlinarith) ?_, Real.log_nonneg hNT', ?_, ?_,
    Real.log_nonneg hNT'2, Real.log_nonneg (by linarith)⟩
  · have h : T' ≤ u * T := by nlinarith
    calc (N : ℝ) * T' ≤ N * (u * T) := mul_le_mul_of_nonneg_left h hN0.le
      _ = N * u * T := by ring
  · apply log_le_two_mul (by nlinarith)
    calc (N : ℝ) * (T' + 2) ≤ N * (4 * T ^ 2) := mul_le_mul_of_nonneg_left (by nlinarith) hN0.le
      _ ≤ _ := hY2
  · apply log_le_two_mul (by nlinarith)
    calc 1 + 2 * (2 * T') ≤ (N : ℝ) * (4 * T ^ 2) := by nlinarith
      _ ≤ _ := hY2

lemma hor_side (G : ℂ → ℂ) (u c T' A h : ℝ) (hu : 1 ≤ u) (hc : -1 / 2 ≤ c) (hT'0 : 0 < T')
    (hA : 0 ≤ A) (hh : |h| = T') (hb : ∀ σ : ℝ, -1 / 2 ≤ σ → σ ≤ c → ‖G ((σ : ℂ) + h * I)‖ ≤ A) :
    ‖∫ x : ℝ in (-1 / 2)..c, G ((x : ℂ) + h * I) * ((u : ℂ) ^ ((x : ℂ) + h * I) / ((x : ℂ) + h * I))‖ ≤
      A * (u ^ c / T') * (c - -1 / 2) := by
  refine seg_bound _ _ _ _ hc (fun x hx1 hx2 => ?_)
  rw [norm_mul]
  have h1 := hb x hx1 hx2
  have him : |h| ≤ ‖(x : ℂ) + h * I‖ := by
    have := Complex.abs_im_le_norm ((x : ℂ) + h * I)
    simpa using this
  have h2 : ‖(u : ℂ) ^ ((x : ℂ) + h * I) / ((x : ℂ) + h * I)‖ ≤ u ^ c / T' :=
    norm_upow_div u hu _ c T' hT'0 (by simpa using hx2) (by rw [← hh]; exact him)
  exact mul_le_mul h1 h2 (norm_nonneg _) hA

lemma left_side (G : ℂ → ℂ) (u T' K2 : ℝ) (hu : 1 ≤ u) (hT'0 : 0 < T') (hK20 : 0 ≤ K2)
    (hb : ∀ t : ℝ, |t| ≤ T' → ‖G (((-1 / 2 : ℝ) : ℂ) + t * I)‖ ≤ K2) :
    ‖∫ t : ℝ in -T'..T', G (((-1 / 2 : ℝ) : ℂ) + t * I) *
        ((u : ℂ) ^ (((-1 / 2 : ℝ) : ℂ) + t * I) / (((-1 / 2 : ℝ) : ℂ) + t * I))‖ ≤
      K2 * (2 * Real.arsinh (2 * T')) := by
  have hle : -T' ≤ T' := by linarith
  calc _ ≤ ∫ t in -T'..T', K2 * (2 * (√(1 + (2 * t) ^ 2))⁻¹) := by
        refine intervalIntegral.norm_integral_le_of_norm_le hle
          (Filter.Eventually.of_forall (fun t ht => ?_))
          ((continuous_const.mul continuous_inv_sqrt).intervalIntegrable _ _)
        rw [norm_mul]
        have ht' : |t| ≤ T' := abs_le.mpr ⟨ht.1.le, ht.2⟩
        exact mul_le_mul (hb t ht') (norm_upow_div_left u hu t) (norm_nonneg _) hK20
    _ = K2 * (2 * Real.arsinh (2 * T')) := by
        rw [intervalIntegral.integral_const_mul, integral_inv_sqrt]

lemma vert_cancel (G k : ℝ → ℂ) (T' : ℝ) :
    2 * π * I * ((1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ in -T'..T', -G t * k t) =
      -(I * ∫ t : ℝ in -T'..T', G t * k t) := by
  have h : ∫ t : ℝ in -T'..T', -G t * k t = -∫ t : ℝ in -T'..T', G t * k t := by
    simp only [neg_mul]
    exact intervalIntegral.integral_neg
  rw [h]
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp

lemma sides_arith {C1 C2 u T T' c l1 l2 as large₂ lNu uc : ℝ} (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2) (hT0 : 0 < T)
    (hu0 : 0 < u) (hTu : T ≤ u) (hTT' : T ≤ T') (hc1 : 1 < c) (hc3 : c ≤ 3) (huc0 : 0 ≤ uc)
    (huc : uc ≤ 3 * u)
    (hLg0 : 0 ≤ large₂) (hl1 : l1 ≤ large₂) (hl1' : 0 ≤ l1) (hl2 : l2 ≤ 2 * large₂) (has : as ≤ 2 * large₂)
    (has0 : 0 ≤ as) (hlNu : 0 ≤ lNu) :
    C1 * l1 ^ 2 * (uc / T') * (c - -1 / 2) + C1 * l1 ^ 2 * (uc / T') * (c - -1 / 2) +
      C2 * l2 * (2 * as) ≤ (21 * C1 + 8 * C2) * (u * large₂ ^ 2 / T + lNu) := by
  have hT'0 : 0 < T' := by linarith
  have hq : uc / T' ≤ 3 * u / T := by
    rw [div_le_div_iff₀ hT'0 hT0]
    nlinarith
  have hl1sq : l1 ^ 2 ≤ large₂ ^ 2 := by nlinarith
  have hcc : c - -1 / 2 ≤ 7 / 2 := by linarith
  have hcc0 : 0 ≤ c - -1 / 2 := by linarith
  have hq0 : 0 ≤ uc / T' := div_nonneg huc0 hT'0.le
  have hY0 : 0 ≤ C1 * large₂ ^ 2 * (3 * u / T) :=
    mul_nonneg (mul_nonneg hC1 (sq_nonneg _)) (div_nonneg (by linarith) hT0.le)
  have hX : C1 * l1 ^ 2 * (uc / T') ≤ C1 * large₂ ^ 2 * (3 * u / T) :=
    mul_le_mul (mul_le_mul_of_nonneg_left hl1sq hC1) hq hq0 (mul_nonneg hC1 (sq_nonneg _))
  have hA : C1 * l1 ^ 2 * (uc / T') * (c - -1 / 2) ≤ C1 * large₂ ^ 2 * (3 * u / T) * (7 / 2) :=
    mul_le_mul hX hcc hcc0 hY0
  have hB : C2 * l2 * (2 * as) ≤ C2 * (2 * large₂) * (2 * (2 * large₂)) :=
    mul_le_mul (mul_le_mul_of_nonneg_left hl2 hC2) (by linarith) (by linarith)
      (mul_nonneg hC2 (by linarith))
  have e1 : C1 * large₂ ^ 2 * (3 * u / T) * (7 / 2) = 21 / 2 * (C1 * (u * large₂ ^ 2 / T)) := by ring
  have e2 : C2 * (2 * large₂) * (2 * (2 * large₂)) = 8 * (C2 * large₂ ^ 2) := by ring
  have h3 : large₂ ^ 2 ≤ u * large₂ ^ 2 / T := by
    rw [le_div_iff₀ hT0]
    nlinarith [sq_nonneg large₂]
  have h4 : C2 * large₂ ^ 2 ≤ C2 * (u * large₂ ^ 2 / T) := mul_le_mul_of_nonneg_left h3 hC2
  have h5 : 0 ≤ (21 * C1 + 8 * C2) * lNu := mul_nonneg (by linarith) hlNu
  have e3 : (21 * C1 + 8 * C2) * (u * large₂ ^ 2 / T + lNu) =
      21 * (C1 * (u * large₂ ^ 2 / T)) + 8 * (C2 * (u * large₂ ^ 2 / T)) + (21 * C1 + 8 * C2) * lNu := by ring
  rw [e3]
  linarith

theorem sidesBound_of {κ C1 C2 : ℝ} (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2) (hH : LogDerivHoriz κ C1)
    (hL : LogDerivLeft C2) : SidesBound κ (21 * C1 + 8 * C2) := by
  intro N _ χ hχ u T T' hT hTu hTT' hT'1 hgood
  have hu2 : 2 ≤ u := le_trans hT hTu
  have hT'2 : 2 ≤ T' := le_trans hT hTT'
  have hT'0 : 0 < T' := by linarith
  have hc1 : 1 < cLine u := one_lt_cLine hu2
  have hc3 : cLine u ≤ 3 := cLine_le_three hu2
  have hN : (1 : ℝ) ≤ N := Nat.one_le_cast.mpr (Nat.pos_of_ne_zero (NeZero.ne N))
  obtain ⟨hf1, hf2, hf3, hf4, hf5, hf6, hf7⟩ := log_facts hN hT hTu hTT' hT'1

  have hbot := hor_side (fun s => logDeriv (DirichletCharacter.LFunction χ) s) u (cLine u) T'
    (C1 * Real.log (N * T') ^ 2) (-T') (by linarith) (by linarith) hT'0
    (mul_nonneg hC1 (sq_nonneg _)) (by rw [abs_neg, abs_of_pos hT'0])
    (fun σ h1 h2 => (hH N χ hχ T' hT'2 hgood σ h1 (by linarith)).2)
  have htop := hor_side (fun s => logDeriv (DirichletCharacter.LFunction χ) s) u (cLine u) T'
    (C1 * Real.log (N * T') ^ 2) T' (by linarith) (by linarith) hT'0
    (mul_nonneg hC1 (sq_nonneg _)) (abs_of_pos hT'0)
    (fun σ h1 h2 => (hH N χ hχ T' hT'2 hgood σ h1 (by linarith)).1)
  have hleft := left_side (fun s => logDeriv (DirichletCharacter.LFunction χ) s) u T'
    (C2 * Real.log (N * (T' + 2))) (by linarith) hT'0 (mul_nonneg hC2 hf6)
    (fun t ht => le_trans (hL N χ hχ t) (mul_le_mul_of_nonneg_left
      (Real.log_le_log (mul_pos (by linarith) (by positivity))
        (mul_le_mul_of_nonneg_left (by linarith) (by linarith))) hC2))

  have hv := vert_cancel (fun t => logDeriv (DirichletCharacter.LFunction χ) ((cLine u : ℂ) + t * I))
    (fun t => (u : ℂ) ^ ((cLine u : ℂ) + t * I) / ((cLine u : ℂ) + t * I)) T'
  unfold rectInt vertInt
  rw [hv]
  simp only [smul_eq_mul]
  refine le_trans (combine hbot htop hleft) ?_
  exact sides_arith hC1 hC2 (by linarith) (by linarith) hTu hTT' hc1 hc3
    (Real.rpow_nonneg (by linarith) _) (rpow_cLine_le hu2) hf1 hf2 hf3 hf4
    ((arsinh_le (2 * T') (by linarith)).trans hf5) (Real.arsinh_nonneg_iff.mpr (by linarith)) hf7

end PI.EF.PK
