import Mathlib

noncomputable section

open Matrix

namespace PositivityTheory.SiegelWeilFormula.Krd.CP

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem cay_inU {J Y : Matrix ι ι ℂ} (hY : Yᴴ * J + J * Y = 0) (hu : IsUnit (1 - Y).det) :
    ((1 + Y) * (1 - Y)⁻¹)ᴴ * J * ((1 + Y) * (1 - Y)⁻¹) = J := by
  have hY' : Yᴴ * J = -(J * Y) := eq_neg_of_add_eq_zero_left hY
  have h1 : J * (1 - Y) = (1 + Y)ᴴ * J := by
    rw [conjTranspose_add, conjTranspose_one, Matrix.add_mul, hY', Matrix.mul_sub, Matrix.mul_one, Matrix.one_mul,
      sub_eq_add_neg]
  have h2 : J * (1 + Y) = (1 - Y)ᴴ * J := by
    rw [conjTranspose_sub, conjTranspose_one, Matrix.sub_mul, hY', Matrix.mul_add, Matrix.mul_one, Matrix.one_mul,
      sub_neg_eq_add]
  have hc : (1 - Y) * (1 + Y) = (1 + Y) * (1 - Y) := by noncomm_ring
  have hB : (1 + Y)ᴴ * J * (1 + Y) = (1 - Y)ᴴ * J * (1 - Y) := by
    rw [← h1, Matrix.mul_assoc, hc, ← Matrix.mul_assoc, h2]
  have hA : ((1 - Y)⁻¹)ᴴ * (1 - Y)ᴴ = 1 := by
    rw [← conjTranspose_mul, Matrix.mul_nonsing_inv _ hu, conjTranspose_one]
  calc ((1 + Y) * (1 - Y)⁻¹)ᴴ * J * ((1 + Y) * (1 - Y)⁻¹)
      = ((1 - Y)⁻¹)ᴴ * ((1 + Y)ᴴ * J * (1 + Y)) * (1 - Y)⁻¹ := by
        rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = ((1 - Y)⁻¹)ᴴ * (1 - Y)ᴴ * J * ((1 - Y) * (1 - Y)⁻¹) := by
        rw [hB]; simp only [Matrix.mul_assoc]
    _ = J := by rw [hA, Matrix.mul_nonsing_inv _ hu, Matrix.one_mul, Matrix.mul_one]

theorem cay_surj {J h : Matrix ι ι ℂ} (hh : hᴴ * J * h = J) (hu : IsUnit (1 + h).det) :
    ∃ Y : Matrix ι ι ℂ, Yᴴ * J + J * Y = 0 ∧ IsUnit (1 - Y).det ∧ (1 + Y) * (1 - Y)⁻¹ = h := by
  obtain ⟨P, hP⟩ : ∃ P : Matrix ι ι ℂ, P = 1 + h := ⟨_, rfl⟩
  rw [← hP] at hu
  have hPi : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
  have hiP : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul _ hu
  obtain ⟨Y, hYd⟩ : ∃ Y : Matrix ι ι ℂ, Y = (h - 1) * P⁻¹ := ⟨_, rfl⟩
  have e1 : 1 - Y = (2 : ℂ) • P⁻¹ := by
    calc 1 - Y = P * P⁻¹ - (h - 1) * P⁻¹ := by rw [hPi, hYd]
      _ = (P - (h - 1)) * P⁻¹ := by rw [← Matrix.sub_mul]
      _ = ((2 : ℂ) • 1) * P⁻¹ := by rw [hP, two_smul]; congr 1; abel
      _ = (2 : ℂ) • P⁻¹ := by rw [Matrix.smul_mul, Matrix.one_mul]
  have e2 : 1 + Y = (2 : ℂ) • (h * P⁻¹) := by
    calc 1 + Y = P * P⁻¹ + (h - 1) * P⁻¹ := by rw [hPi, hYd]
      _ = (P + (h - 1)) * P⁻¹ := by rw [← Matrix.add_mul]
      _ = ((2 : ℂ) • h) * P⁻¹ := by rw [hP, two_smul]; congr 1; abel
      _ = (2 : ℂ) • (h * P⁻¹) := by rw [Matrix.smul_mul]
  have hdet : IsUnit (1 - Y).det := by
    rw [e1, Matrix.det_smul]
    exact (IsUnit.pow _ (isUnit_iff_ne_zero.2 two_ne_zero)).mul ((Matrix.isUnit_nonsing_inv_det_iff).2 hu)
  refine ⟨Y, ?_, hdet, ?_⟩
  · have hPc : (P⁻¹)ᴴ * Pᴴ = 1 := by rw [← conjTranspose_mul, hPi, conjTranspose_one]
    have eY : Y * P = h - 1 := by rw [hYd, Matrix.mul_assoc, hiP, Matrix.mul_one]
    have eYh : Pᴴ * Yᴴ = (h - 1)ᴴ := by rw [← conjTranspose_mul, eY]
    have key : Pᴴ * (Yᴴ * J + J * Y) * P = 0 := by
      have e3 : Pᴴ * (Yᴴ * J + J * Y) * P = (Pᴴ * Yᴴ) * J * P + Pᴴ * J * (Y * P) := by noncomm_ring
      rw [e3, eYh, eY, hP, conjTranspose_sub, conjTranspose_add, conjTranspose_one]
      have e4 : (hᴴ - 1) * J * (1 + h) + (1 + hᴴ) * J * (h - 1) = (2 : ℂ) • (hᴴ * J * h - J) := by
        rw [two_smul]; noncomm_ring
      rw [e4, hh, sub_self, smul_zero]
    calc Yᴴ * J + J * Y = ((P⁻¹)ᴴ * Pᴴ) * (Yᴴ * J + J * Y) * (P * P⁻¹) := by
          rw [hPc, hPi, Matrix.one_mul, Matrix.mul_one]
      _ = (P⁻¹)ᴴ * (Pᴴ * (Yᴴ * J + J * Y) * P) * P⁻¹ := by simp only [Matrix.mul_assoc]
      _ = 0 := by rw [key, Matrix.mul_zero, Matrix.zero_mul]
  · rw [e1, e2]
    have hinv : ((2 : ℂ) • P⁻¹)⁻¹ = (2 : ℂ)⁻¹ • P := by
      refine Matrix.inv_eq_left_inv ?_
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ two_ne_zero, one_smul, hPi]
    rw [hinv, Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ two_ne_zero, one_smul, Matrix.mul_assoc, hiP,
      Matrix.mul_one]

theorem scalar_avoid {J h : Matrix ι ι ℂ} (hh : hᴴ * J * h = J) {V : Set (Matrix ι ι ℂ)} (hV : IsOpen V) (hhV : h ∈ V) :
    ∃ μ : ℂ, star μ * μ = 1 ∧ μ • h ∈ V ∧ IsUnit (1 + μ • h).det := by
  obtain ⟨q, hqd⟩ : ∃ q : Polynomial ℂ, q = (1 + (Polynomial.X : Polynomial ℂ) • h.map Polynomial.C).det := ⟨_, rfl⟩
  have hq : ∀ μ : ℂ, q.eval μ = (1 + μ • h).det := by
    intro μ
    rw [hqd, ← Polynomial.coe_evalRingHom, RingHom.map_det]
    congr 1
    ext i j
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij] <;> ring
  have hq0 : q ≠ 0 := fun h0 => by
    have := hq 0
    rw [h0, Polynomial.eval_zero, zero_smul, add_zero, Matrix.det_one] at this
    exact zero_ne_one this
  have hg : Continuous fun θ : ℝ => Complex.exp (θ * Complex.I) • h :=
    (Complex.continuous_exp.comp (Complex.continuous_ofReal.mul continuous_const)).smul continuous_const
  have hO : IsOpen ((fun θ : ℝ => Complex.exp (θ * Complex.I) • h) ⁻¹' V) := hV.preimage hg
  have h0O : (0 : ℝ) ∈ (fun θ : ℝ => Complex.exp (θ * Complex.I) • h) ⁻¹' V := by
    simp only [Set.mem_preimage, Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_smul]
    exact hhV
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hO 0 h0O
  have hδ' : (0 : ℝ) < min δ 1 := lt_min hδ one_pos
  have hSinf : (Set.Ioo (0 : ℝ) (min δ 1)).Infinite := Set.Ioo_infinite hδ'
  have hinj : Set.InjOn (fun θ : ℝ => Complex.exp (θ * Complex.I)) (Set.Ioo (0 : ℝ) (min δ 1)) := by
    intro a ha b hb hab
    have hpi : (1 : ℝ) < Real.pi := lt_trans (by norm_num) Real.pi_gt_three
    have hIoc : ∀ t ∈ Set.Ioo (0 : ℝ) (min δ 1), t ∈ Set.Ioc (-Real.pi) Real.pi := fun t ht =>
      ⟨by linarith [ht.1, Real.pi_pos], by linarith [ht.2, min_le_right δ 1]⟩
    have e := congrArg Complex.arg hab
    simp only [Complex.exp_mul_I] at e
    rwa [Complex.arg_cos_add_sin_mul_I (hIoc a ha), Complex.arg_cos_add_sin_mul_I (hIoc b hb)] at e
  obtain ⟨μ, ⟨θ, hθ, rfl⟩, hμ⟩ := (hSinf.image hinj).exists_notMem_finset q.roots.toFinset
  refine ⟨Complex.exp (θ * Complex.I), ?_, ?_, ?_⟩
  · rw [Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
    rw [show (θ : ℂ) * -Complex.I + θ * Complex.I = 0 by ring, Complex.exp_zero]
  · refine hball ?_
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hθ.1]
    exact lt_of_lt_of_le hθ.2 (min_le_left δ 1)
  · rw [isUnit_iff_ne_zero, ← hq]
    intro h0
    exact hμ (Multiset.mem_toFinset.2 ((Polynomial.mem_roots hq0).2 h0))

end PositivityTheory.SiegelWeilFormula.Krd.CP

end
