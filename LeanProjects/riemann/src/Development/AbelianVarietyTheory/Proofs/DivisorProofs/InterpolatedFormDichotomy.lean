import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightBoundConst
open Matrix Filter Topology Set GlobalTheory.HermFrame GlobalTheory.IndefiniteRowSideFullHecke.HermitianInterpolation GlobalTheory.InterpCurv
open scoped ComplexOrder ContDiff

noncomputable section

namespace GlobalTheory.CurvRemainder

open ComplexConjugate

variable {n : Type} [Fintype n]

theorem form_comb (P₀ P : Matrix n n ℂ) (σ : ℝ) (x y : n → ℂ) :
    form (((1 - σ : ℝ) : ℂ) • P₀ + (σ : ℂ) • P) x y
      = ((1 - σ : ℝ) : ℂ) * form P₀ x y + (σ : ℂ) * form P x y := by
  rw [form_add, form_smul, form_smul]

theorem re_form_comb (P₀ P : Matrix n n ℂ) (σ : ℝ) (x y : n → ℂ) :
    (form (((1 - σ : ℝ) : ℂ) • P₀ + (σ : ℂ) • P) x y).re
      = (1 - σ) * (form P₀ x y).re + σ * (form P x y).re := by
  rw [form_comb, Complex.add_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul]

theorem re_form_swap {H : Matrix n n ℂ} (hH : H.IsHermitian) (x y : n → ℂ) :
    (form H y x).re = (form H x y).re := by
  rw [← conj_form hH x y, Complex.conj_re]

theorem re_form_nonneg {H : Matrix n n ℂ} (hH : H.PosSemidef) (x : n → ℂ) :
    0 ≤ (form H x x).re := by
  rw [← gnorm_sq hH]; positivity

theorem re_form_comb_nonneg {P₀ P : Matrix n n ℂ} (h₀ : P₀.PosSemidef) (h₁ : P.PosSemidef)
    {σ : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) (x : n → ℂ) :
    0 ≤ (form (((1 - σ : ℝ) : ℂ) • P₀ + (σ : ℂ) • P) x x).re := by
  rw [re_form_comb]
  exact add_nonneg (mul_nonneg (by linarith) (re_form_nonneg h₀ x))
    (mul_nonneg hσ0 (re_form_nonneg h₁ x))

theorem proj_eq {P₀ P : Matrix n n ℂ} (h₀ : P₀.IsHermitian) (h₁ : P.IsHermitian) {σ : ℝ}
    {X p q : n → ℂ}
    (h : ∀ w, form (((1 - σ : ℝ) : ℂ) • P₀ + (σ : ℂ) • P) X w
      = ((1 - σ : ℝ) : ℂ) * form P₀ p w + (σ : ℂ) * form P q w) (u : n → ℂ) :
    (1 - σ) * (form P₀ p p).re + σ * (form P q q).re
        - (form (((1 - σ : ℝ) : ℂ) • P₀ + (σ : ℂ) • P) X X).re
      = (1 - σ) * (form P₀ (p - u) (p - u)).re + σ * (form P (q - u) (q - u)).re
        - (form (((1 - σ : ℝ) : ℂ) • P₀ + (σ : ℂ) • P) (X - u) (X - u)).re := by
  have hh := congrArg Complex.re (h u)
  rw [re_form_comb, Complex.add_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul] at hh
  have s1 := re_form_swap h₀ p u
  have s2 := re_form_swap h₀ X u
  have s3 := re_form_swap h₁ q u
  have s4 := re_form_swap h₁ X u
  rw [re_form_comb, re_form_comb]
  simp only [form_sub_left, form_sub_right, Complex.sub_re]
  linear_combination (1 - σ) * s1 + σ * s3 - (1 - σ) * s2 - σ * s4 - 2 * hh

theorem proj_nonneg {P₀ P : Matrix n n ℂ} (h₀ : P₀.PosSemidef) (h₁ : P.PosSemidef) {σ : ℝ}
    (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) {X p q : n → ℂ}
    (h : ∀ w, form (((1 - σ : ℝ) : ℂ) • P₀ + (σ : ℂ) • P) X w
      = ((1 - σ : ℝ) : ℂ) * form P₀ p w + (σ : ℂ) * form P q w) :
    0 ≤ (1 - σ) * (form P₀ p p).re + σ * (form P q q).re
        - (form (((1 - σ : ℝ) : ℂ) • P₀ + (σ : ℂ) • P) X X).re := by
  rw [proj_eq h₀.isHermitian h₁.isHermitian h X, sub_self]
  have e : (form (((1 - σ : ℝ) : ℂ) • P₀ + (σ : ℂ) • P) 0 0).re = 0 := by simp [form]
  rw [e, sub_zero]
  exact add_nonneg (mul_nonneg (by linarith) (re_form_nonneg h₀ _))
    (mul_nonneg hσ0 (re_form_nonneg h₁ _))

theorem proj_le {P₀ P : Matrix n n ℂ} (h₀ : P₀.PosSemidef) (h₁ : P.PosSemidef) {σ : ℝ}
    (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) {X p q : n → ℂ}
    (h : ∀ w, form (((1 - σ : ℝ) : ℂ) • P₀ + (σ : ℂ) • P) X w
      = ((1 - σ : ℝ) : ℂ) * form P₀ p w + (σ : ℂ) * form P q w) (u : n → ℂ) :
    (1 - σ) * (form P₀ p p).re + σ * (form P q q).re
        - (form (((1 - σ : ℝ) : ℂ) • P₀ + (σ : ℂ) • P) X X).re
      ≤ (1 - σ) * (form P₀ (p - u) (p - u)).re + σ * (form P (q - u) (q - u)).re := by
  rw [proj_eq h₀.isHermitian h₁.isHermitian h u]
  linarith [re_form_comb_nonneg h₀ h₁ hσ0 hσ1 (X - u)]

theorem re_form_smul {H : Matrix n n ℂ} (hH : H.PosSemidef) (c : ℂ) (v : n → ℂ) :
    (form H (c • v) (c • v)).re = ‖c‖ ^ 2 * (form H v v).re := by
  rw [← gnorm_sq hH, ← gnorm_sq hH, gnorm_smul hH, mul_pow]

theorem re_form_add_smul {H : Matrix n n ℂ} (hH : H.PosSemidef) (Y v : n → ℂ) (c : ℂ) :
    (form H (Y + c • v) (Y + c • v)).re
      = (form H Y Y).re + 2 * (conj c * form H Y v).re + (form H (c • v) (c • v)).re := by
  have e1 : (form H (c • v) Y).re = (conj c * form H Y v).re := by
    rw [re_form_swap hH.isHermitian, form_smul_right]
  simp only [form_add_left, form_add_right, Complex.add_re]
  rw [e1, form_smul_right H c Y v]
  ring

theorem re_form_sub_le {H : Matrix n n ℂ} (hH : H.PosSemidef) (x y : n → ℂ) :
    (form H (x - y) (x - y)).re ≤ 2 * ((form H x x).re + (form H y y).re) := by
  have h := gnorm_parallelogram hH x y
  rw [gnorm_sq hH, gnorm_sq hH, gnorm_sq hH, gnorm_sq hH] at h
  linarith [re_form_nonneg hH (x + y)]

theorem ell_bound {a b σ ρ N K l : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1)
    (hρ : 0 ≤ ρ) (hba : ρ * b ≤ a) (h1 : |l| ≤ K * N ^ 2 * (σ + ρ * (1 - σ)))
    (h2 : |l| ≤ K * N ^ 2 * (1 - σ)) :
    |(a - b) * l| ≤ 2 * |K| * N ^ 2 * ((1 - σ) * a + σ * b) := by
  have h1σ : 0 ≤ 1 - σ := by linarith
  have hs : 0 ≤ σ + ρ * (1 - σ) := by positivity
  have hK1 : K * N ^ 2 * (1 - σ) ≤ |K| * N ^ 2 * (1 - σ) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self K) (sq_nonneg N)) h1σ
  have hK2 : K * N ^ 2 * (σ + ρ * (1 - σ)) ≤ |K| * N ^ 2 * (σ + ρ * (1 - σ)) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self K) (sq_nonneg N)) hs
  have e1 : a * |l| ≤ a * (|K| * N ^ 2 * (1 - σ)) := mul_le_mul_of_nonneg_left (h2.trans hK1) ha
  have e2 : b * |l| ≤ b * (|K| * N ^ 2 * (σ + ρ * (1 - σ))) :=
    mul_le_mul_of_nonneg_left (h1.trans hK2) hb
  have hKN : 0 ≤ |K| * N ^ 2 := by positivity
  have e3 : |K| * N ^ 2 * ((1 - σ) * (ρ * b)) ≤ |K| * N ^ 2 * ((1 - σ) * a) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hba h1σ) hKN
  have e4 : 0 ≤ |K| * N ^ 2 * ((1 - σ) * a) := mul_nonneg hKN (mul_nonneg h1σ ha)
  have e5 : 0 ≤ |K| * N ^ 2 * (σ * b) := mul_nonneg hKN (mul_nonneg hσ0 hb)
  have hab : |a - b| ≤ a + b := abs_le.2 ⟨by linarith, by linarith⟩
  rw [abs_mul]
  calc |a - b| * |l| ≤ (a + b) * |l| := mul_le_mul_of_nonneg_right hab (abs_nonneg _)
    _ = a * |l| + b * |l| := by ring
    _ ≤ 2 * |K| * N ^ 2 * ((1 - σ) * a + σ * b) := by linarith

theorem rem_zero {P₀ P : Matrix n n ℂ} (h₀ : P₀.PosSemidef) (h₁ : P.PosSemidef) {σ : ℝ}
    (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) {X Y : n → ℂ}
    (h : ∀ w, form (((1 - σ : ℝ) : ℂ) • P₀ + (σ : ℂ) • P) X w = (σ : ℂ) * form P Y w) :
    |(form (((1 - σ : ℝ) : ℂ) • P₀ + (σ : ℂ) • P) X X).re - σ * (form P Y Y).re|
      ≤ (1 - σ) * (form P₀ Y Y).re := by
  have h' : ∀ w, form (((1 - σ : ℝ) : ℂ) • P₀ + (σ : ℂ) • P) X w
      = ((1 - σ : ℝ) : ℂ) * form P₀ 0 w + (σ : ℂ) * form P Y w := by
    intro w; rw [h w]; simp [form]
  have e1 := proj_nonneg h₀ h₁ hσ0 hσ1 h'
  have e2 := proj_le h₀ h₁ hσ0 hσ1 h' Y
  have z0 : (form P₀ 0 0).re = 0 := by simp [form]
  have z1 : (form P₀ (0 - Y) (0 - Y)).re = (form P₀ Y Y).re := by
    simp [form, Matrix.mulVec_neg]
  have z2 : (form P (Y - Y) (Y - Y)).re = 0 := by simp [form]
  rw [z0] at e1 e2
  rw [z1, z2] at e2
  rw [abs_le]; constructor <;> nlinarith

theorem remainder_bound : ∀ {n : Type} [Fintype n] {P₀ P : Matrix n n ℂ} {σ ρ N C₂ K : ℝ} {d ℓ : ℂ} {v X Y : n → ℂ}, P₀.PosDef → P.PosDef → 0 ≤ σ → σ ≤ 1 → 0 < ρ → 0 ≤ N → ℓ.im = 0 → ρ * (form P₀ v v).re ≤ (form P v v).re → ρ * (form P v v).re ≤ (form P₀ v v).re → gnorm P₀ Y ≤ C₂ * N * gnorm P₀ v → (∀ w, form (((1 - σ : ℝ) : ℂ) • P₀ + (σ : ℂ) • P) X w = (σ : ℂ) * form P Y w + d * (form P v w - form P₀ v w)) → ((d = 0 ∧ ℓ.re = 0) ∨ (σ < 1 ∧ ‖d‖ ≤ K * (1 - σ) * N ∧ ‖d‖ ^ 2 ≤ K * N ^ 2 * σ * (σ + ρ * (1 - σ)) ∧ |ℓ.re| ≤ K * N ^ 2 * (σ + ρ * (1 - σ)) ∧ |ℓ.re| ≤ K * N ^ 2 * (1 - σ))) → |((form P₀ v v - form P v v) * ℓ - 2 * ((d * starRingEnd ℂ (form P Y v)).re : ℂ) + form (((1 - σ : ℝ) : ℂ) • P₀ + (σ : ℂ) • P) X X - (σ : ℂ) * form P Y Y).re| ≤ (2 * C₂ ^ 2 + 4 * |K| + 3 * K ^ 2) * N ^ 2 * ((1 - σ) * (form P₀ v v).re + σ * (form P v v).re) := by
  intro n _ P₀ P σ ρ N C₂ K d ℓ v X Y h₀ h₁ hσ0 hσ1 hρ hN hℓ hab hba hY hX hcase
  have p₀ := h₀.posSemidef
  have p₁ := h₁.posSemidef
  have h1σ : 0 ≤ 1 - σ := by linarith
  have hR : ((form P₀ v v - form P v v) * ℓ - 2 * ((d * starRingEnd ℂ (form P Y v)).re : ℂ)
      + form (((1 - σ : ℝ) : ℂ) • P₀ + (σ : ℂ) • P) X X - (σ : ℂ) * form P Y Y).re
      = ((form P₀ v v).re - (form P v v).re) * ℓ.re - 2 * (d * starRingEnd ℂ (form P Y v)).re
        + (form (((1 - σ : ℝ) : ℂ) • P₀ + (σ : ℂ) • P) X X).re - σ * (form P Y Y).re := by
    simp only [Complex.sub_re, Complex.add_re, Complex.mul_re, hℓ, mul_zero, sub_zero,
      Complex.ofReal_re, Complex.ofReal_im, Complex.sub_im]
    norm_num
  rw [hR]
  have ha := re_form_nonneg p₀ v
  have hb := re_form_nonneg p₁ v
  have hy0 := re_form_nonneg p₀ Y
  have hyC : (form P₀ Y Y).re ≤ C₂ ^ 2 * N ^ 2 * (form P₀ v v).re := by
    have h2 : gnorm P₀ Y ^ 2 ≤ (C₂ * N * gnorm P₀ v) ^ 2 := pow_le_pow_left₀ (gnorm_nonneg _ _) hY 2
    rw [mul_pow, mul_pow, gnorm_sq p₀, gnorm_sq p₀] at h2
    exact h2
  have hW : 0 ≤ N ^ 2 * ((1 - σ) * (form P₀ v v).re + σ * (form P v v).re) :=
    mul_nonneg (sq_nonneg N) (add_nonneg (mul_nonneg h1σ ha) (mul_nonneg hσ0 hb))
  have hyV : (1 - σ) * (form P₀ Y Y).re
      ≤ C₂ ^ 2 * (N ^ 2 * ((1 - σ) * (form P₀ v v).re + σ * (form P v v).re)) := by
    have := mul_le_mul_of_nonneg_left hyC h1σ
    have : 0 ≤ C₂ ^ 2 * N ^ 2 * (σ * (form P v v).re) :=
      mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (mul_nonneg hσ0 hb)
    nlinarith
  have hK0 : 0 ≤ |K| * (N ^ 2 * ((1 - σ) * (form P₀ v v).re + σ * (form P v v).re)) :=
    mul_nonneg (abs_nonneg K) hW
  have hK2 : 0 ≤ K ^ 2 * (N ^ 2 * ((1 - σ) * (form P₀ v v).re + σ * (form P v v).re)) :=
    mul_nonneg (sq_nonneg K) hW
  have hC0 : 0 ≤ C₂ ^ 2 * (N ^ 2 * ((1 - σ) * (form P₀ v v).re + σ * (form P v v).re)) :=
    mul_nonneg (sq_nonneg _) hW
  by_cases hd : d = 0
  · have h' : ∀ w, form (((1 - σ : ℝ) : ℂ) • P₀ + (σ : ℂ) • P) X w = (σ : ℂ) * form P Y w := by
      intro w; rw [hX w, hd, zero_mul, add_zero]
    have hz := abs_le.1 (rem_zero p₀ p₁ hσ0 hσ1 h')
    have hc : (d * starRingEnd ℂ (form P Y v)).re = 0 := by simp [hd]
    have hE : |((form P₀ v v).re - (form P v v).re) * ℓ.re|
        ≤ 2 * |K| * N ^ 2 * ((1 - σ) * (form P₀ v v).re + σ * (form P v v).re) := by
      rcases hcase with ⟨-, hl⟩ | ⟨-, -, -, hl1, hl2⟩
      · rw [hl, mul_zero, abs_zero]; nlinarith
      · exact ell_bound ha hb hσ0 hσ1 hρ.le hba hl1 hl2
    have hE' := abs_le.1 hE
    rw [hc, abs_le]
    constructor <;> nlinarith
  · rcases hcase with ⟨hd0, -⟩ | ⟨hs1, hd1, hd2, hl1, hl2⟩
    · exact absurd hd0 hd
    have hσpos : 0 < σ := by
      rcases hσ0.lt_or_eq with h | h
      · exact h
      · exfalso
        rw [← h] at hd2
        have : ‖d‖ ^ 2 ≤ 0 := by simpa using hd2
        exact hd (norm_eq_zero.1 (by nlinarith [norm_nonneg d]))
    have h1σp : 0 < 1 - σ := by linarith
    have h1σc : ((1 - σ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 h1σp.ne'
    have hσc : (σ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hσpos.ne'
    have hproj : ∀ w, form (((1 - σ : ℝ) : ℂ) • P₀ + (σ : ℂ) • P) X w
        = ((1 - σ : ℝ) : ℂ) * form P₀ ((-(d / ((1 - σ : ℝ) : ℂ))) • v) w
          + (σ : ℂ) * form P (Y + (d / (σ : ℂ)) • v) w := by
      intro w
      have e1 : ((1 - σ : ℝ) : ℂ) * (d / ((1 - σ : ℝ) : ℂ)) = d := mul_div_cancel₀ d h1σc
      have e2 : (σ : ℂ) * (d / (σ : ℂ)) = d := mul_div_cancel₀ d hσc
      rw [hX w, form_smul_left, form_add_left, form_smul_left]
      linear_combination (form P₀ v w) * e1 - (form P v w) * e2
    have pos := proj_nonneg p₀ p₁ hσ0 hσ1 hproj
    have le := proj_le p₀ p₁ hσ0 hσ1 hproj Y
    have n1 : ‖-(d / ((1 - σ : ℝ) : ℂ))‖ = ‖d‖ / (1 - σ) := by
      rw [norm_neg, norm_div, Complex.norm_real, Real.norm_of_nonneg h1σ]
    have n2 : ‖d / (σ : ℂ)‖ = ‖d‖ / σ := by
      rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hσ0]
    have hp : (form P₀ ((-(d / ((1 - σ : ℝ) : ℂ))) • v) ((-(d / ((1 - σ : ℝ) : ℂ))) • v)).re
        = (‖d‖ / (1 - σ)) ^ 2 * (form P₀ v v).re := by rw [re_form_smul p₀, n1]
    have hq := re_form_add_smul p₁ Y v (d / (σ : ℂ))
    rw [re_form_smul p₁, n2] at hq
    have hγ : σ * (starRingEnd ℂ (d / (σ : ℂ)) * form P Y v).re
        = (d * starRingEnd ℂ (form P Y v)).re := by
      rw [← Complex.re_ofReal_mul, map_div₀, Complex.conj_ofReal, ← mul_assoc,
        mul_div_cancel₀ _ hσc, ← Complex.conj_re, map_mul, Complex.conj_conj]
    have hqY : (form P (Y + (d / (σ : ℂ)) • v - Y) (Y + (d / (σ : ℂ)) • v - Y)).re
        = (‖d‖ / σ) ^ 2 * (form P v v).re := by
      rw [add_sub_cancel_left, re_form_smul p₁, n2]
    have hpY := re_form_sub_le p₀ ((-(d / ((1 - σ : ℝ) : ℂ))) • v) Y
    rw [hp] at hpY pos le
    rw [hq] at pos le
    rw [hqY] at le
    have le' := mul_le_mul_of_nonneg_left hpY h1σ

    have hD1 : ‖d‖ / (1 - σ) ≤ K * N := by rw [div_le_iff₀ h1σp]; linarith
    have hD1' : (‖d‖ / (1 - σ)) ^ 2 ≤ K ^ 2 * N ^ 2 := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (div_nonneg (norm_nonneg _) h1σ) hD1 2
    have he1 : (1 - σ) * ((‖d‖ / (1 - σ)) ^ 2 * (form P₀ v v).re)
        ≤ K ^ 2 * N ^ 2 * ((1 - σ) * (form P₀ v v).re) := by
      have := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hD1' ha) h1σ
      linarith
    have hKσ : 0 ≤ K ^ 2 * N ^ 2 * (σ * (form P v v).re) :=
      mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (mul_nonneg hσ0 hb)
    have he1' : 0 ≤ (1 - σ) * ((‖d‖ / (1 - σ)) ^ 2 * (form P₀ v v).re) :=
      mul_nonneg h1σ (mul_nonneg (sq_nonneg _) ha)
    have hs2 : σ * (‖d‖ / σ) ^ 2 = ‖d‖ ^ 2 / σ := by field_simp
    have hD2 : ‖d‖ ^ 2 / σ ≤ K * N ^ 2 * (σ + ρ * (1 - σ)) := by
      rw [div_le_iff₀ hσpos]; linarith
    have hsρ : 0 ≤ σ + ρ * (1 - σ) := by positivity
    have hD2' : ‖d‖ ^ 2 / σ ≤ |K| * N ^ 2 * (σ + ρ * (1 - σ)) :=
      hD2.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_abs_self K) (sq_nonneg N)) hsρ)
    have he2 : σ * ((‖d‖ / σ) ^ 2 * (form P v v).re)
        ≤ |K| * N ^ 2 * ((1 - σ) * (form P₀ v v).re + σ * (form P v v).re) := by
      have e : σ * ((‖d‖ / σ) ^ 2 * (form P v v).re) = ‖d‖ ^ 2 / σ * (form P v v).re := by
        rw [← hs2]; ring
      rw [e]
      have h3 := mul_le_mul_of_nonneg_right hD2' hb
      have hKN : 0 ≤ |K| * N ^ 2 := by positivity
      have h4 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hba h1σ) hKN
      linarith
    have he2' : 0 ≤ σ * ((‖d‖ / σ) ^ 2 * (form P v v).re) :=
      mul_nonneg hσ0 (mul_nonneg (sq_nonneg _) hb)
    have hE := abs_le.1 (ell_bound ha hb hσ0 hσ1 hρ.le hba hl1 hl2)
    rw [abs_le]
    constructor <;> linarith [hE.1, hE.2]

end GlobalTheory.CurvRemainder
