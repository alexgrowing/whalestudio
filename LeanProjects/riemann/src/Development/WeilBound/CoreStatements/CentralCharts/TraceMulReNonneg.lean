import Mathlib

noncomputable section

namespace AnalyticReference.An

open Matrix
open scoped ComplexOrder MatrixOrder

variable {r k : ℕ}

theorem exists_factor {X : Matrix (Fin r) (Fin r) ℂ} (hX : X.PosSemidef) :
    ∃ S : Matrix (Fin r) (Fin r) ℂ, X = Sᴴ * S := by
  have h0 : 0 ≤ X := hX.nonneg
  refine ⟨CFC.sqrt X, ?_⟩
  have h1 : (CFC.sqrt X).PosSemidef := (CFC.sqrt_nonneg X).posSemidef
  rw [h1.1.eq, CFC.sqrt_mul_sqrt_self X h0]

theorem det_re_pos {X : Matrix (Fin r) (Fin r) ℂ} (hX : X.PosDef) : 0 < X.det.re :=
  (Complex.pos_iff.1 hX.det_pos).1

theorem det_eq_re {X : Matrix (Fin r) (Fin r) ℂ} (hX : X.PosDef) : X.det = (X.det.re : ℂ) :=
  Complex.ext (by simp) (by simpa using (Complex.pos_iff.1 hX.det_pos).2.symm)

theorem logdet_le_trace {Z : Matrix (Fin r) (Fin r) ℂ} (hZ : Z.PosDef) :
    Real.log Z.det.re ≤ Z.trace.re - r := by
  have h1 : Z.det.re = ∏ i, hZ.1.eigenvalues i := by
    rw [hZ.1.det_eq_prod_eigenvalues]
    have : (∏ i, (RCLike.ofReal (hZ.1.eigenvalues i) : ℂ)) = ((∏ i, hZ.1.eigenvalues i : ℝ) : ℂ) := by
      push_cast; rfl
    rw [this, Complex.ofReal_re]
  have h2 : Z.trace.re = ∑ i, hZ.1.eigenvalues i := by
    rw [hZ.1.trace_eq_sum_eigenvalues]
    have : (∑ i, (RCLike.ofReal (hZ.1.eigenvalues i) : ℂ)) = ((∑ i, hZ.1.eigenvalues i : ℝ) : ℂ) := by
      push_cast; rfl
    rw [this, Complex.ofReal_re]
  rw [h1, h2, Real.log_prod fun i _ => (hZ.eigenvalues_pos i).ne']
  have h3 : ∑ i, Real.log (hZ.1.eigenvalues i) ≤ ∑ i, (hZ.1.eigenvalues i - 1) :=
    Finset.sum_le_sum fun i _ => Real.log_le_sub_one_of_pos (hZ.eigenvalues_pos i)
  simpa [Finset.sum_sub_distrib] using h3

theorem logdet_le {X X₀ : Matrix (Fin r) (Fin r) ℂ} (hX : X.PosDef) (h₀ : X₀.PosDef) :
    Real.log X.det.re ≤ Real.log X₀.det.re + (X₀⁻¹ * X).trace.re - r := by
  obtain ⟨S, hS⟩ := exists_factor h₀.inv.posSemidef
  have hd : IsUnit S.det := by
    have h1 := h₀.inv.det_pos.ne'
    rw [hS, det_mul] at h1
    exact IsUnit.mk0 _ (right_ne_zero_of_mul h1)
  have hinj : Function.Injective (Sᴴ).mulVec :=
    Matrix.mulVec_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det _).2 (by rw [det_conjTranspose]; exact hd.star))
  have hZ : (S * X * Sᴴ).PosDef := by
    have := hX.conjTranspose_mul_mul_same hinj
    rwa [conjTranspose_conjTranspose] at this
  have h1 := logdet_le_trace hZ
  have h2 : (S * X * Sᴴ).trace = (X₀⁻¹ * X).trace := by
    rw [hS, trace_mul_cycle]
  have h3 : (S * X * Sᴴ).det = X₀.det⁻¹ * X.det := by
    rw [← Ring.inverse_eq_inv, ← det_nonsing_inv, hS, det_mul, det_mul, det_mul]; ring
  rw [h2, h3, det_eq_re hX, det_eq_re h₀, ← Complex.ofReal_inv, ← Complex.ofReal_mul, Complex.ofReal_re,
    Real.log_mul (inv_ne_zero (det_re_pos h₀).ne') (det_re_pos hX).ne', Real.log_inv] at h1
  linarith

theorem trace_mul_re_nonneg {X Y : Matrix (Fin r) (Fin r) ℂ} (hX : X.PosSemidef) (hY : Y.PosSemidef) :
    0 ≤ (X * Y).trace.re := by
  obtain ⟨S, hS⟩ := exists_factor hX
  have h1 := (hY.mul_mul_conjTranspose_same S).trace_nonneg
  have h2 : (S * Y * Sᴴ).trace = (X * Y).trace := by rw [hS, trace_mul_cycle]
  rw [h2] at h1
  exact (Complex.nonneg_iff.1 h1).1

theorem logdet_mono {P G : Matrix (Fin r) (Fin r) ℂ} (hP : P.PosDef) (hG : G.PosDef) (h : (G - P).PosSemidef) :
    Real.log P.det.re ≤ Real.log G.det.re := by
  have h1 := logdet_le hP hG
  have h2 := trace_mul_re_nonneg hG.inv.posSemidef h
  rw [Matrix.mul_sub, nonsing_inv_mul _ (IsUnit.mk0 _ hG.det_pos.ne'), trace_sub, trace_one] at h2
  simp at h2
  linarith

theorem posDef_smul_one {c : ℝ} (hc : 0 < c) : ((c : ℂ) • (1 : Matrix (Fin r) (Fin r) ℂ)).PosDef :=
  Matrix.PosDef.one.smul (by exact_mod_cast hc)

theorem logdet_smul_one {c : ℝ} (hc : 0 < c) :
    Real.log ((c : ℂ) • (1 : Matrix (Fin r) (Fin r) ℂ)).det.re = r * Real.log c := by
  rw [det_smul, det_one, mul_one, Fintype.card_fin, ← Complex.ofReal_pow, Complex.ofReal_re, Real.log_pow]

theorem logdet_inv {X : Matrix (Fin r) (Fin r) ℂ} (hX : X.PosDef) :
    Real.log X⁻¹.det.re = -Real.log X.det.re := by
  rw [det_nonsing_inv, Ring.inverse_eq_inv, det_eq_re hX, ← Complex.ofReal_inv, Complex.ofReal_re, Complex.ofReal_re,
    Real.log_inv]

theorem posDef_of_inv_ge {Γ : Matrix (Fin r) (Fin r) ℂ} {c : ℝ} (hc : 0 < c)
    (h : (Γ⁻¹ - (c : ℂ) • (1 : Matrix (Fin r) (Fin r) ℂ)).PosSemidef) : Γ.PosDef := by
  have := (posDef_smul_one hc).add_posSemidef h
  rw [add_sub_cancel] at this
  exact Matrix.posDef_inv_iff.1 this

theorem ge_of_inv_le {Γ : Matrix (Fin r) (Fin r) ℂ} {K : ℝ} (hK : 0 < K) (hΓ : Γ.PosDef)
    (h : ((K : ℂ) • (1 : Matrix (Fin r) (Fin r) ℂ) - Γ⁻¹).PosSemidef) :
    (Γ - ((K⁻¹ : ℝ) : ℂ) • (1 : Matrix (Fin r) (Fin r) ℂ)).PosSemidef := by
  have hu : IsUnit Γ.det := IsUnit.mk0 _ hΓ.det_pos.ne'
  have hK' : (K : ℂ) ≠ 0 := by exact_mod_cast hK.ne'
  have h1 := hΓ.posSemidef.conjTranspose_mul_mul_same (1 - ((K⁻¹ : ℝ) : ℂ) • Γ⁻¹)
  have h2 := h.smul (a := (((K⁻¹ ^ 2 : ℝ)) : ℂ)) (by exact_mod_cast (by positivity : (0 : ℝ) ≤ K⁻¹ ^ 2))
  convert h1.add h2 using 1
  rw [conjTranspose_sub, conjTranspose_one, conjTranspose_smul, hΓ.inv.1.eq]
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul,
    nonsing_inv_mul _ hu, mul_nonsing_inv _ hu, smul_sub, smul_smul, Complex.star_def, Complex.conj_ofReal]
  push_cast
  have e : (K : ℂ)⁻¹ ^ 2 * K = (K : ℂ)⁻¹ := by field_simp
  rw [e, pow_two]
  abel

theorem le_of_inv_ge {Γ : Matrix (Fin r) (Fin r) ℂ} {c : ℝ} (hc : 0 < c) (hΓ : Γ.PosDef)
    (h : (Γ⁻¹ - (c : ℂ) • (1 : Matrix (Fin r) (Fin r) ℂ)).PosSemidef) :
    (((c⁻¹ : ℝ) : ℂ) • (1 : Matrix (Fin r) (Fin r) ℂ) - Γ).PosSemidef := by
  have hu : IsUnit Γ.det := IsUnit.mk0 _ hΓ.det_pos.ne'
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have h1 := h.conjTranspose_mul_mul_same Γ
  have h2 := (posDef_smul_one (r := r) (inv_pos.2 hc)).posSemidef.conjTranspose_mul_mul_same (1 - (c : ℂ) • Γ)
  convert h1.add h2 using 1
  rw [conjTranspose_sub, conjTranspose_one, conjTranspose_smul, hΓ.1.eq]
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul,
    nonsing_inv_mul _ hu, mul_nonsing_inv _ hu, smul_sub, smul_smul, Complex.star_def, Complex.conj_ofReal]
  push_cast
  have e1 : (c : ℂ)⁻¹ * c = 1 := by field_simp
  have e2 : (c : ℂ) * (c : ℂ)⁻¹ = 1 := by field_simp
  simp only [e1, e2, one_smul, mul_one]
  abel

theorem norm_entry_le {Γ : Matrix (Fin r) (Fin r) ℂ} {K : ℝ} (hΓ : Γ.PosSemidef)
    (h : ((K : ℂ) • (1 : Matrix (Fin r) (Fin r) ℂ) - Γ).PosSemidef) (p q : Fin r) : ‖Γ p q‖ ≤ K := by
  obtain ⟨S, hS⟩ := exists_factor hΓ
  have hd : ∀ p, ∑ i, ‖S i p‖ ^ 2 ≤ K := fun p => by
    have h1 := (Complex.nonneg_iff.1 (h.diag_nonneg (i := p))).1
    have h2 : (Γ p p).re = ∑ i, ‖S i p‖ ^ 2 := by
      rw [hS, mul_apply, Complex.re_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [conjTranspose_apply, Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]
    simp [h2] at h1
    exact h1
  have h3 : ‖Γ p q‖ ≤ ∑ i, (‖S i p‖ ^ 2 + ‖S i q‖ ^ 2) / 2 := by
    rw [hS, mul_apply]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [conjTranspose_apply, norm_mul, norm_star]
    nlinarith [sq_nonneg (‖S i p‖ - ‖S i q‖)]
  rw [← Finset.sum_div, Finset.sum_add_distrib] at h3
  linarith [hd p, hd q]

theorem logdet_dual_ge {Y : Matrix (Fin k) (Fin k) ℂ} (hY : Y.PosDef) (B C : Matrix (Fin k) (Fin r) ℂ)
    (hM : (Cᴴ * Y * C).PosDef) (hG : (Bᴴ * Y⁻¹ * B).PosDef) (hN : (Cᴴ * B).det ≠ 0) :
    2 * Real.log ‖(Cᴴ * B).det‖ - Real.log (Cᴴ * Y * C).det.re ≤ Real.log (Bᴴ * Y⁻¹ * B).det.re := by
  set M := Cᴴ * Y * C with hMd
  set N := Cᴴ * B with hNd
  have huY : IsUnit Y.det := IsUnit.mk0 _ hY.det_pos.ne'
  have huM : IsUnit M.det := IsUnit.mk0 _ hM.det_pos.ne'
  have hP : (Nᴴ * M⁻¹ * N).PosDef := hM.inv.conjTranspose_mul_mul_same
    (Matrix.mulVec_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det _).2 (IsUnit.mk0 _ hN)))
  have h1 := hY.inv.posSemidef.conjTranspose_mul_mul_same (B - Y * C * M⁻¹ * N)
  have e : (B - Y * C * M⁻¹ * N)ᴴ * Y⁻¹ * (B - Y * C * M⁻¹ * N) = Bᴴ * Y⁻¹ * B - Nᴴ * M⁻¹ * N := by
    have a1 : (Y * C * M⁻¹ * N)ᴴ * Y⁻¹ = Nᴴ * M⁻¹ * Cᴴ := by
      simp only [conjTranspose_mul, hM.inv.1.eq, hY.1.eq, Matrix.mul_assoc, mul_nonsing_inv _ huY, Matrix.mul_one]
    have a2 : Bᴴ * Y⁻¹ * (Y * C * M⁻¹ * N) = Nᴴ * M⁻¹ * N := by
      rw [hNd, conjTranspose_mul, conjTranspose_conjTranspose]
      simp only [Matrix.mul_assoc, nonsing_inv_mul_cancel_left _ _ huY]
    have a3 : Nᴴ * M⁻¹ * Cᴴ * (Y * C * M⁻¹ * N) = Nᴴ * M⁻¹ * N := by
      have : Nᴴ * M⁻¹ * Cᴴ * (Y * C * M⁻¹ * N) = Nᴴ * M⁻¹ * (M * M⁻¹) * N := by
        rw [hMd]; simp only [Matrix.mul_assoc]
      rw [this, mul_nonsing_inv _ huM, Matrix.mul_one]
    have a4 : Nᴴ * M⁻¹ * Cᴴ * B = Nᴴ * M⁻¹ * N := by rw [Matrix.mul_assoc _ Cᴴ]
    rw [conjTranspose_sub, Matrix.sub_mul, a1, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, a2, a3, a4]
    abel
  rw [e] at h1
  have h2 := logdet_mono hP hG h1
  have h3 : (Nᴴ * M⁻¹ * N).det = ((‖N.det‖ ^ 2 * (M.det.re)⁻¹ : ℝ) : ℂ) := by
    rw [det_mul, det_mul, det_conjTranspose, det_nonsing_inv, Ring.inverse_eq_inv, det_eq_re hM]
    push_cast
    rw [← Complex.conj_mul', Complex.star_def, Complex.ofReal_re]; ring
  rw [h3, Complex.ofReal_re, Real.log_mul (pow_ne_zero _ (norm_ne_zero_iff.2 hN)) (inv_ne_zero (det_re_pos hM).ne'),
    Real.log_pow, Real.log_inv] at h2
  push_cast at h2
  linarith

end AnalyticReference.An
