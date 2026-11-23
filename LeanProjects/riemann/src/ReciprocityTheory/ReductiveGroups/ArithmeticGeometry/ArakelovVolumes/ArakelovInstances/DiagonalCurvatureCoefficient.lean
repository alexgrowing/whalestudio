import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.CoeffMatrixZeroCorrectedLineGramPoly

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf

open Polynomial Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.P Filter Topology

variable {r m : ℕ} (hm : m ≤ r) (D : Fin r → ℝ) (Y : Matrix (Fin r) (Fin r) ℂ)

section CD

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {k : WithTop ℕ∞}

theorem cd_mul {n : ℕ} (F G : E → Matrix (Fin n) (Fin n) ℂ) (hF : ∀ a b, ContDiff ℝ k fun v => F v a b)
    (hG : ∀ a b, ContDiff ℝ k fun v => G v a b) (a b : Fin n) : ContDiff ℝ k fun v => (F v * G v) a b := by
  simp only [Matrix.mul_apply]
  exact ContDiff.sum fun i _ => (hF a i).mul (hG i b)

theorem cd_conjT {n : ℕ} (F : E → Matrix (Fin n) (Fin n) ℂ) (hF : ∀ a b, ContDiff ℝ k fun v => F v a b)
    (a b : Fin n) : ContDiff ℝ k fun v => (F v)ᴴ a b := by
  simp only [Matrix.conjTranspose_apply]
  exact Complex.conjCLE.contDiff.comp (hF b a)

theorem cd_det {n : ℕ} (F : E → Matrix (Fin n) (Fin n) ℂ) (hF : ∀ a b, ContDiff ℝ k fun v => F v a b) :
    ContDiff ℝ k fun v => (F v).det := by
  simp only [Matrix.det_apply']
  refine ContDiff.sum fun σ _ => ?_
  exact contDiff_const.mul (contDiff_prod fun i _ => hF (σ i) i)

end CD

def fY (v : Fin 1 → ℂ) : ℝ := (Gz hm D Y (v 0)).det.re

def fn (v : Fin 1 → ℂ) : ℝ := (Gnz hm D Y (v 0)).det.re

def pd (v : Fin 1 → ℂ) : ℂ := (1 - (v 0) • Ym hm Y).det

theorem cd_lin {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (c : ℂ) (a b : Fin n) :
    ContDiff ℝ 2 fun v : Fin 1 → ℂ => (1 + (c * v 0) • A) a b := by
  have h0 : ContDiff ℝ 2 fun v : Fin 1 → ℂ => v 0 := contDiff_pi.mp contDiff_id 0
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  exact contDiff_const.add ((contDiff_const.mul h0).mul contDiff_const)

theorem cd_Gz (a b : Fin m) : ContDiff ℝ 2 fun v : Fin 1 → ℂ => Gz hm D Y (v 0) a b := by
  have hl : ∀ i j : Fin r, ContDiff ℝ 2 fun v : Fin 1 → ℂ => (1 + v 0 • Y) i j := by
    intro i j
    have h := cd_lin Y 1 i j
    simp only [one_mul] at h
    exact h
  show ContDiff ℝ 2 fun v : Fin 1 → ℂ =>
    ((1 + v 0 • Y)ᴴ * Dc D * (1 + v 0 • Y) : Matrix (Fin r) (Fin r) ℂ) (Fin.castLE hm a) (Fin.castLE hm b)
  exact cd_mul (fun v : Fin 1 → ℂ => (1 + v 0 • Y)ᴴ * Dc D) (fun v => 1 + v 0 • Y)
    (fun i j => cd_mul (fun v : Fin 1 → ℂ => (1 + v 0 • Y)ᴴ) (fun _ => Dc D)
      (cd_conjT (fun v : Fin 1 → ℂ => 1 + v 0 • Y) hl) (fun _ _ => contDiff_const) i j) hl _ _

theorem cd_Gnz (a b : Fin m) : ContDiff ℝ 2 fun v : Fin 1 → ℂ => Gnz hm D Y (v 0) a b := by
  have hl : ∀ i j : Fin m, ContDiff ℝ 2 fun v : Fin 1 → ℂ => (1 - v 0 • Ym hm Y) i j := by
    intro i j
    have h := cd_lin (Ym hm Y) (-1) i j
    have e : ∀ v : Fin 1 → ℂ, (1 + (-1 * v 0) • Ym hm Y) = 1 - v 0 • Ym hm Y := by
      intro v
      rw [neg_one_mul, neg_smul, ← sub_eq_add_neg]
    simp only [e] at h
    exact h
  show ContDiff ℝ 2 fun v : Fin 1 → ℂ =>
    ((1 - v 0 • Ym hm Y)ᴴ * (Gz hm D Y (v 0) * (1 - v 0 • Ym hm Y)) : Matrix (Fin m) (Fin m) ℂ) a b
  exact cd_mul (fun v : Fin 1 → ℂ => (1 - v 0 • Ym hm Y)ᴴ)
    (fun v => Gz hm D Y (v 0) * (1 - v 0 • Ym hm Y))
    (cd_conjT (fun v : Fin 1 → ℂ => 1 - v 0 • Ym hm Y) hl)
    (fun i j => cd_mul (fun v : Fin 1 → ℂ => Gz hm D Y (v 0)) (fun v => 1 - v 0 • Ym hm Y)
      (fun i j => cd_Gz hm D Y i j) hl i j) a b

theorem contDiff_fn : ContDiff ℝ 2 (fn hm D Y) := by
  have h := cd_det (fun v : Fin 1 → ℂ => Gnz hm D Y (v 0)) (fun a b => cd_Gnz hm D Y a b)
  exact Complex.reCLM.contDiff.comp h

theorem contDiff_fY : ContDiff ℝ 2 (fY hm D Y) := by
  have h := cd_det (fun v : Fin 1 → ℂ => Gz hm D Y (v 0)) (fun a b => cd_Gz hm D Y a b)
  exact Complex.reCLM.contDiff.comp h

theorem fn_line (t : ℂ) (s : ℝ) :
    fn hm D Y (s • fun _ => t) = ((GnP hm D Y t).det.eval (s : ℂ)).re := by

  have hlin : ∀ {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ),
      (Polynomial.evalRingHom (s : ℂ)).mapMatrix (lin A) = 1 + (s : ℂ) • A := by
    intro n A
    unfold lin
    rw [map_add, map_one]
    congr 1
    ext i j
    simp
    exact mul_comm _ _
  have hC : (Polynomial.evalRingHom (s : ℂ)).mapMatrix ((Dc D).map Polynomial.C) = Dc D := by
    ext i j
    by_cases h : i = j <;> simp [Matrix.diagonal_apply, h]
  have hsub : ∀ M : Matrix (Fin r) (Fin r) ℂ[X],
      (Polynomial.evalRingHom (s : ℂ)).mapMatrix (M.submatrix (Fin.castLE hm) (Fin.castLE hm)) =
        ((Polynomial.evalRingHom (s : ℂ)).mapMatrix M).submatrix (Fin.castLE hm) (Fin.castLE hm) :=
    fun M => rfl
  have hst : star ((s : ℂ) * t) = (s : ℂ) * (starRingEnd ℂ) t := by
    rw [star_mul', Complex.star_def, Complex.conj_ofReal]
  have key : (GnP hm D Y t).map (Polynomial.eval (s : ℂ)) = Gnz hm D Y ((s : ℂ) * t) := by
    change (Polynomial.evalRingHom (s : ℂ)).mapMatrix (GnP hm D Y t) = _
    unfold GnP GP Gnz Gz
    rw [map_mul, map_mul, hsub, map_mul, map_mul, hlin, hlin, hlin, hlin, hC]
    simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_add, Matrix.conjTranspose_one,
      Matrix.conjTranspose_smul, hst, smul_smul, smul_neg, ← sub_eq_add_neg, Matrix.mul_assoc]
  have hs : (s • fun _ : Fin 1 => t) 0 = (s : ℂ) * t := by
    simp [Complex.real_smul]
  unfold fn
  rw [hs, ← key]
  congr 1
  have h := RingHom.map_det (Polynomial.evalRingHom (s : ℂ)) (GnP hm D Y t)
  simpa using h.symm

theorem Gz_zero : Gz hm D Y 0 = Dm hm D := by
  ext i j
  simp [Gz, Matrix.diagonal_apply, Fin.castLE_inj]

theorem fn_zero : fn hm D Y (0 : Fin 1 → ℂ) = ∏ a : Fin m, D (Fin.castLE hm a) := by
  have e : Gnz hm D Y 0 = Dm hm D := by
    unfold Gnz
    rw [Gz_zero]
    simp
  unfold fn
  simp only [Pi.zero_apply]
  rw [e]
  simp [Matrix.det_diagonal, ← Complex.ofReal_prod]

theorem fY_zero : fY hm D Y (0 : Fin 1 → ℂ) = ∏ a : Fin m, D (Fin.castLE hm a) := by
  unfold fY
  simp only [Pi.zero_apply]
  rw [Gz_zero]
  simp [Matrix.det_diagonal, ← Complex.ofReal_prod]

theorem fderiv_fn_zero : fderiv ℝ (fn hm D Y) 0 = 0 := by
  refine ContinuousLinearMap.ext fun w => ?_
  set t := w 0 with ht
  have hw : w = fun _ => t := funext fun i => by fin_cases i; rfl
  rw [fderiv_line_zero (((contDiff_fn hm D Y).differentiable (by norm_num)) 0), hw]
  have e : (fun s : ℝ => fn hm D Y (s • fun _ => t)) = fun s : ℝ => ((GnP hm D Y t).det.eval (s : ℂ)).re :=
    funext (fn_line hm D Y t)
  rw [e, deriv_re_eval_zero, (det_coeff_zero_one_of_coeffMatrix_one _ (coeffMatrix_one_correctedLineGramPoly hm D Y t)).2]
  simp

theorem sum_castLE' {M : Type} [AddCommMonoid M] (g : Fin r → M) :
    ∑ j : Fin m, g (Fin.castLE hm j) = ∑ k : Fin r, if (k : ℕ) < m then g k else 0 := by
  rw [← Finset.sum_filter]
  refine Finset.sum_bij (fun j _ => Fin.castLE hm j) ?_ ?_ ?_ ?_
  · intro j _
    simp
  · intro a _ b _ h
    exact Fin.ext (by simpa using congrArg Fin.val h)
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
    exact ⟨⟨k, hk⟩, Finset.mem_univ _, Fin.ext (by simp)⟩
  · intro j _
    rfl

def Sa (a : Fin m) : ℝ := ∑ k : Fin r, if m ≤ (k : ℕ) then D k * ‖Y k (Fin.castLE hm a)‖ ^ 2 else 0

theorem diagonal_curvature_coefficient (a : Fin m) :
    (cf 2 (GnP hm D Y 1) + cf 2 (GnP hm D Y Complex.I)) a a = 2 * (Sa hm D Y a : ℂ) := by
  rw [coeffMatrix_two_correctedLineGramPoly, coeffMatrix_two_correctedLineGramPoly]
  have hc1 : (starRingEnd ℂ) (1 : ℂ) = 1 := map_one _
  have hcI : (starRingEnd ℂ) Complex.I = -Complex.I := Complex.conj_I
  simp only [hc1, hcI, one_mul, one_pow, one_smul, neg_mul, Complex.I_mul_I, neg_neg, Complex.I_sq,
    neg_sq, neg_smul, one_smul, sub_neg_eq_add]
  have e : ∀ (A P Q : Matrix (Fin m) (Fin m) ℂ), (A - P - Q) + (A + P + Q) = (2 : ℂ) • A := by
    intro A P Q; rw [two_smul]; abel
  rw [e, Matrix.smul_apply, smul_eq_mul, Matrix.sub_apply]
  congr 1
  simp only [Matrix.submatrix_apply]
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp only [Dc, Dm, Ym, Matrix.mul_diagonal, Matrix.conjTranspose_apply, Matrix.submatrix_apply]
  rw [sum_castLE' hm (fun k => star (Y k (Fin.castLE hm a)) * (D k : ℂ) * Y k (Fin.castLE hm a)),
    ← Finset.sum_sub_distrib, Sa]
  push_cast
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases hk : (k : ℕ) < m
  · rw [if_pos hk, if_neg (by omega), sub_self]
    simp
  · rw [if_neg hk, if_pos (by omega), sub_zero, Complex.ofReal_mul, Complex.ofReal_pow,
      ← Complex.conj_mul', Complex.star_def]
    ring

theorem levi_fn (hD : ∀ k, D k ≠ 0) :
    levi (fn hm D Y) 0 (fun _ => 1) =
      (∏ a : Fin m, D (Fin.castLE hm a)) * ∑ a : Fin m, (D (Fin.castLE hm a))⁻¹ * Sa hm D Y a := by
  rw [levi_eq_lines (contDiff_fn hm D Y)]
  have hI : (Complex.I • fun _ : Fin 1 => (1 : ℂ)) = fun _ => Complex.I := by funext i; simp
  have e1 : (fun s : ℝ => fn hm D Y (s • fun _ => (1 : ℂ))) =
      fun s : ℝ => ((GnP hm D Y 1).det.eval (s : ℂ)).re := funext (fn_line hm D Y 1)
  have e2 : (fun s : ℝ => fn hm D Y (s • (Complex.I • fun _ : Fin 1 => (1 : ℂ)))) =
      fun s : ℝ => ((GnP hm D Y Complex.I).det.eval (s : ℂ)).re := by
    rw [hI]; exact funext (fn_line hm D Y Complex.I)
  rw [e1, e2, deriv2_re_eval_zero, deriv2_re_eval_zero]
  set d : Fin m → ℂ := fun a => (D (Fin.castLE hm a) : ℂ) with hdd
  have hd : ∀ a, d a ≠ 0 := fun a => Complex.ofReal_ne_zero.2 (hD _)
  rw [coeff2_det_of _ d hd (coeffMatrix_zero_correctedLineGramPoly hm D Y 1) (coeffMatrix_one_correctedLineGramPoly hm D Y 1),
    coeff2_det_of _ d hd (coeffMatrix_zero_correctedLineGramPoly hm D Y Complex.I) (coeffMatrix_one_correctedLineGramPoly hm D Y _)]
  have hterm : ∀ a, (d a)⁻¹ * cf 2 (GnP hm D Y 1) a a + (d a)⁻¹ * cf 2 (GnP hm D Y Complex.I) a a =
      (d a)⁻¹ * (2 * (Sa hm D Y a : ℂ)) := fun a => by
    rw [← mul_add, ← Matrix.add_apply, diagonal_curvature_coefficient]
  have key : (∏ a, d a) * ∑ a, (d a)⁻¹ * cf 2 (GnP hm D Y 1) a a +
      (∏ a, d a) * ∑ a, (d a)⁻¹ * cf 2 (GnP hm D Y Complex.I) a a =
      (((∏ a : Fin m, D (Fin.castLE hm a)) * ∑ a, (D (Fin.castLE hm a))⁻¹ * (2 * Sa hm D Y a) : ℝ) : ℂ) := by
    rw [← mul_add, ← Finset.sum_add_distrib]
    simp_rw [hterm]
    push_cast
    rfl
  have hre := congrArg Complex.re key
  rw [Complex.add_re, Complex.ofReal_re] at hre
  calc (2 * ((∏ a, d a) * ∑ a, (d a)⁻¹ * cf 2 (GnP hm D Y 1) a a).re +
        2 * ((∏ a, d a) * ∑ a, (d a)⁻¹ * cf 2 (GnP hm D Y Complex.I) a a).re) / 4
      = (((∏ a : Fin m, D (Fin.castLE hm a)) * ∑ a, (D (Fin.castLE hm a))⁻¹ * (2 * Sa hm D Y a))) / 2 := by
        rw [← hre]; ring
    _ = _ := by rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_div]; congr 1; funext a; ring

end ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf
