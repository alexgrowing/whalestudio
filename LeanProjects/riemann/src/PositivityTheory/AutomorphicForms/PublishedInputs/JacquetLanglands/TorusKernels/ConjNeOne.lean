import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.Imports

noncomputable section

open MeasureTheory Matrix
open scoped ENNReal NNReal ComplexConjugate

namespace UpperTheory.Esk.RadialIntegralLemmas
open UpperTheory.Esk

theorem key_id (α β u ub : ℂ) (hα : α ≠ 0) (hu : 1 - u ≠ 0) (h1 : β - α * u ≠ 0) (h2 : α - β * ub ≠ 0)
    (hA : α - β * u * ub ≠ 0) :
    (Complex.I * (β + α * u) / (β - α * u) - -Complex.I * (α + β * ub) / (α - β * ub)) /
      (Complex.I * (1 + u) / (1 - u) - -Complex.I * (α + β * ub) / (α - β * ub)) * ((β - α * u) / (1 - u)) =
      β * (1 - u * ub) / (1 - β / α * (u * ub)) := by
  have hI := Complex.I_ne_zero
  have e1 : Complex.I * (1 + u) / (1 - u) - -Complex.I * (α + β * ub) / (α - β * ub) =
      2 * Complex.I * (α - β * u * ub) / ((1 - u) * (α - β * ub)) := by
    field_simp; ring
  have e2 : Complex.I * (β + α * u) / (β - α * u) - -Complex.I * (α + β * ub) / (α - β * ub) =
      2 * Complex.I * α * β * (1 - u * ub) / ((β - α * u) * (α - β * ub)) := by
    field_simp; ring
  have e3 : 1 - β / α * (u * ub) = (α - β * u * ub) / α := by field_simp
  rw [e1, e2, e3]
  field_simp

theorem pow_combine (c X Y S T : ℂ) (k : ℕ) (h : X * Y / S = T) :
    c * X ^ k * (Y ^ k * (S ^ k)⁻¹) = c * T ^ k := by
  rw [← h, div_pow, mul_pow]; ring

theorem cayley_val (k : ℕ) (m : GL (Fin 2) ℝ) (a b : ℝ) (h00 : m 0 0 = a) (h01 : m 0 1 = b)
    (h10 : m 1 0 = -b) (h11 : m 1 1 = a) (hb : b ≠ 0) (r θ : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    ext1 (U k m) (Complex.I * (1 + circleMap 0 r θ) / (1 - circleMap 0 r θ)) =
      ((k : ℂ) - 1) / (4 * Real.pi) * (eta a b * (1 - (r : ℂ) ^ 2) / (1 - eta a b ^ 2 * (r : ℂ) ^ 2)) ^ k := by
  set u := circleMap 0 r θ with hu_def
  have hnu : ‖u‖ = r := by simp [u, abs_of_pos hr0]
  have hu1 : (1 : ℂ) - u ≠ 0 := by
    intro h; rw [sub_eq_zero] at h; rw [← h, norm_one] at hnu; linarith
  have huu : u * conj u = (r : ℂ) ^ 2 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hnu]; push_cast; ring
  have hn : u.re ^ 2 + u.im ^ 2 = r ^ 2 := by
    rw [← hnu, Complex.sq_norm, Complex.normSq_apply]; ring
  set z := Complex.I * (1 + u) / (1 - u) with hz_def
  have hz_im : z.im = (1 - r ^ 2) / Complex.normSq (1 - u) := by
    rw [hz_def, Complex.div_im, ← sub_div]
    congr 1
    simp
    nlinarith [hn]
  have hzpos : 0 < z.im := by
    rw [hz_im]
    apply div_pos
    · nlinarith
    · exact Complex.normSq_pos.2 hu1
  have hz : z.im ≠ 0 := hzpos.ne'
  set zP : P := ⟨z, hz⟩ with hzP
  have hzP1 : zP.1 = z := rfl
  have hzpos' : 0 < zP.1.im := hzpos
  have hext : ext1 (U k m) z = F k m zP := by
    unfold ext1; rw [dif_pos hz]; exact if_pos hzpos'
  have hab : 0 < a ^ 2 + b ^ 2 := by
    have := lt_of_le_of_ne (sq_nonneg b) (Ne.symm (pow_ne_zero 2 hb)); nlinarith [sq_nonneg a]
  obtain ⟨s, hs_def⟩ : ∃ s, s = Real.sqrt (a ^ 2 + b ^ 2) := ⟨_, rfl⟩
  have hs : 0 < s := by rw [hs_def]; exact Real.sqrt_pos.2 hab
  have hs2 : s ^ 2 = a ^ 2 + b ^ 2 := by rw [hs_def]; exact Real.sq_sqrt hab.le
  have hS0 : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have hα0 : (a : ℂ) + b * Complex.I ≠ 0 := by
    intro h; have := congrArg Complex.im h; simp at this; exact hb this
  have hβ0 : (a : ℂ) - b * Complex.I ≠ 0 := by
    intro h; have := congrArg Complex.im h; simp at this; exact hb this
  have hden : den m z = (((a : ℂ) - b * Complex.I) - ((a : ℂ) + b * Complex.I) * u) / (1 - u) := by
    rw [eq_div_iff hu1]; unfold den; rw [h10, h11, hz_def]; push_cast; field_simp; ring
  have hnum : num m z = Complex.I * (((a : ℂ) - b * Complex.I) + ((a : ℂ) + b * Complex.I) * u) / (1 - u) := by
    rw [eq_div_iff hu1]; unfold num; rw [h00, h01, hz_def]; field_simp
    linear_combination (b * (1 - u)) * Complex.I_sq
  have h1 : ((a : ℂ) - b * Complex.I) - ((a : ℂ) + b * Complex.I) * u ≠ 0 := by
    have := den_ne m hz; rw [hden] at this; exact (div_ne_zero_iff.1 this).1
  have h2 : ((a : ℂ) + b * Complex.I) - ((a : ℂ) - b * Complex.I) * conj u ≠ 0 := by
    have h := (map_ne_zero (starRingEnd ℂ)).2 h1
    convert h using 1
    simp only [map_sub, map_mul, map_add, Complex.conj_ofReal, Complex.conj_I]; ring
  have hA : ((a : ℂ) + b * Complex.I) - ((a : ℂ) - b * Complex.I) * u * conj u ≠ 0 := by
    intro h
    rw [mul_assoc, huu, ← Complex.ofReal_pow] at h
    have := congrArg Complex.im h
    simp only [Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re,
      Complex.I_re, Complex.I_im, Complex.sub_re, Complex.mul_re, Complex.add_re, Complex.zero_im] at this
    have h3 : b * (1 + r ^ 2) = 0 := by
      linear_combination this
    rcases mul_eq_zero.1 h3 with h4 | h4
    · exact hb h4
    · nlinarith [sq_nonneg r]
  have hw : (m • zP).1 = Complex.I * (((a : ℂ) - b * Complex.I) + ((a : ℂ) + b * Complex.I) * u) /
      (((a : ℂ) - b * Complex.I) - ((a : ℂ) + b * Complex.I) * u) := by
    rw [coe_smul, hzP1, hnum, hden, div_div_div_cancel_right₀ hu1]
  have hwb : conj (Complex.I * (((a : ℂ) - b * Complex.I) + ((a : ℂ) + b * Complex.I) * u) /
      (((a : ℂ) - b * Complex.I) - ((a : ℂ) + b * Complex.I) * u)) =
      -Complex.I * (((a : ℂ) + b * Complex.I) + ((a : ℂ) - b * Complex.I) * conj u) /
      (((a : ℂ) + b * Complex.I) - ((a : ℂ) - b * Complex.I) * conj u) := by
    simp only [map_div₀, map_sub, map_mul, map_add, Complex.conj_ofReal, Complex.conj_I]; ring
  have hwim : 0 < (m • zP).1.im := by
    rw [coe_smul, im_div, det_eq, h00, h01, h10, h11]
    apply div_pos (mul_pos (by nlinarith) hzpos') (Complex.normSq_pos.2 (den_ne m hz))
  have hdet : |m.val.det| = s ^ 2 := by
    rw [det_eq, h00, h01, h10, h11, hs2, abs_of_pos (by nlinarith)]; ring
  have hrp : (|m.val.det| ^ (-(k : ℝ) / 2) : ℝ) = (s ^ k)⁻¹ := by
    rw [hdet, ← Real.rpow_natCast s 2, ← Real.rpow_mul hs.le,
      show ((2 : ℕ) : ℝ) * (-(k : ℝ) / 2) = -(k : ℝ) by push_cast; ring, Real.rpow_neg hs.le, Real.rpow_natCast]
  have hηsq : (((a : ℂ) - b * Complex.I) / (s : ℂ)) ^ 2 = ((a : ℂ) - b * Complex.I) / ((a : ℂ) + b * Complex.I) := by
    rw [div_pow, div_eq_div_iff (pow_ne_zero 2 hS0) hα0, ← Complex.ofReal_pow, hs2]
    push_cast
    linear_combination (-((a : ℂ) - b * Complex.I) * (b : ℂ) ^ 2) * Complex.I_sq
  rw [hext]
  unfold F q1 j1
  rw [if_pos (mul_pos hzpos' hwim), hrp]
  push_cast
  refine pow_combine _ _ _ _ _ k ?_
  rw [hw, hwb, hzP1, hden, key_id _ _ _ _ hα0 hu1 h1 h2 hA, ← huu, eta, ← hs_def, hηsq]
  field_simp

end UpperTheory.Esk.RadialIntegralLemmas
