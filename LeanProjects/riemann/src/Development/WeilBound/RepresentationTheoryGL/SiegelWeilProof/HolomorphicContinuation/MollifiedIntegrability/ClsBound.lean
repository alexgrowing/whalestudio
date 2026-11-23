import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.ClsBoundB

noncomputable section

open Matrix MvPolynomial

namespace PositivityTheory.Rg.Sw.WR.B

open PositivityTheory.Rg.Sw

variable {n : ℕ}

theorem line_hasDerivAt {F : E n → ℂ} {y : E n} (hF : DifferentiableAt ℝ F y) (h : E n) :
    HasDerivAt (fun t : ℝ => F (y + t • h)) (fderiv ℝ F y h) 0 := by
  have hl : HasDerivAt (fun t : ℝ => y + t • h) h 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const h).const_add y
  have hF' : HasFDerivAt F (fderiv ℝ F y) (y + (0 : ℝ) • h) := by simpa using hF.hasFDerivAt
  exact hF'.comp_hasDerivAt (0 : ℝ) hl

theorem det_line (M N : Matrix (Fin n) (Fin n) ℂ) (hM : M.det ≠ 0) :
    HasDerivAt (fun t : ℝ => (M + (t : ℂ) • N).det) (M.det * (M⁻¹ * N).trace) 0 := by
  set P := M⁻¹ * N with hP
  set Q : Polynomial ℂ := Matrix.det (1 + (Polynomial.X : Polynomial ℂ) • P.map Polynomial.C) with hQ
  have e : ∀ t : ℂ, (M + t • N).det = M.det * Q.eval t := by
    intro t
    have h1 : M + t • N = M * (1 + t • P) := by
      rw [hP, Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, ← Matrix.mul_assoc,
        Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hM), Matrix.one_mul]
    rw [h1, Matrix.det_mul, hQ, ← Polynomial.coe_evalRingHom, RingHom.map_det]
    congr 2
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply,
      smul_eq_mul, Polynomial.coe_evalRingHom, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
      Polynomial.eval_C]
    split_ifs <;> simp
  have hp := (Polynomial.hasDerivAt Q ((0 : ℝ) : ℂ)).comp_ofReal.const_mul M.det
  have hv : Q.derivative.eval ((0 : ℝ) : ℂ) = P.trace := by
    rw [Complex.ofReal_zero, hQ]; exact Matrix.derivative_det_one_add_X_smul P
  rw [hv] at hp
  have e2 : (fun t : ℝ => (M + (t : ℂ) • N).det) = fun t : ℝ => M.det * Q.eval (t : ℂ) := funext fun t => e t
  rw [e2]; exact hp

theorem Am_line (s : ℂ) (y h : E n) (t : ℝ) :
    Am s (y + t • h) = Am s y + (t : ℂ) • (-((Complex.I * s) • herm h)) := by
  ext i j
  simp only [Am, herm_add, herm_smul, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.neg_apply,
    smul_eq_mul]
  ring

theorem Bm_line (s : ℂ) (y h : E n) (t : ℝ) :
    Bm s (y + t • h) = Bm s y + (t : ℂ) • ((Complex.I * s) • herm h) := by
  ext i j
  simp only [Bm, herm_add, herm_smul, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  ring

theorem contDiff_detAm (s : ℂ) : ContDiff ℝ (⊤ : ℕ∞) (fun y : E n => (Am s y).det) :=
  contDiff_det_of (contDiff_Am_entry s)

theorem contDiff_detBm (s : ℂ) : ContDiff ℝ (⊤ : ℕ∞) (fun y : E n => (Bm s y).det) :=
  contDiff_det_of (contDiff_Bm_entry s)

theorem fderiv_detAm {s : ℂ} (hs : s = 1 ∨ s = -1) (y h : E n) :
    fderiv ℝ (fun y => (Am s y).det) y h = (Am s y).det * ((Am s y)⁻¹ * (-((Complex.I * s) • herm h))).trace := by
  have h1 := line_hasDerivAt (diffAt_of (contDiff_detAm s) y) h
  have h2 := det_line (Am s y) (-((Complex.I * s) • herm h)) (det_Am_ne hs y)
  have e : (fun t : ℝ => (Am s (y + t • h)).det) = fun t : ℝ => (Am s y + (t : ℂ) • (-((Complex.I * s) • herm h))).det :=
    funext fun t => by rw [Am_line]
  rw [e] at h1
  exact h1.unique h2

theorem fderiv_detBm {s : ℂ} (hs : s = 1 ∨ s = -1) (y h : E n) :
    fderiv ℝ (fun y => (Bm s y).det) y h = (Bm s y).det * ((Bm s y)⁻¹ * ((Complex.I * s) • herm h)).trace := by
  have h1 := line_hasDerivAt (diffAt_of (contDiff_detBm s) y) h
  have h2 := det_line (Bm s y) ((Complex.I * s) • herm h) (det_Bm_ne hs y)
  have e : (fun t : ℝ => (Bm s (y + t • h)).det) = fun t : ℝ => (Bm s y + (t : ℂ) • ((Complex.I * s) • herm h)).det :=
    funext fun t => by rw [Bm_line]
  rw [e] at h1
  exact h1.unique h2

theorem trace_combo (U : Matrix (Fin n) (Fin n) ℂ) (c : ℂ) (k l : Fin n) :
    (U * (c • herm (fun a b => (vkl k l a b).re))).trace + Complex.I * (U * (c • herm (fun a b => (vkl k l a b).im))).trace =
      c * U k l := by
  rw [← trace_mul_single U k l, ← hc_vkl k l]
  simp only [Matrix.mul_smul, Matrix.trace_smul, Matrix.mul_add, Matrix.trace_add, smul_eq_mul]
  ring

theorem trace_comboN (U : Matrix (Fin n) (Fin n) ℂ) (c : ℂ) (k l : Fin n) :
    (U * -(c • herm (fun a b => (vkl k l a b).re))).trace +
      Complex.I * (U * -(c • herm (fun a b => (vkl k l a b).im))).trace = -c * U k l := by
  have := trace_combo U c k l
  simp only [Matrix.mul_neg, Matrix.trace_neg]
  linear_combination -this

theorem dirC_detAm {s : ℂ} (hs : s = 1 ∨ s = -1) (y : E n) (k l : Fin n) :
    dirC (fun y => (Am s y).det) (vkl k l) y = -(Complex.I * s) * (Am s y).det * uM s y k l := by
  rw [dirC, fderiv_detAm hs, fderiv_detAm hs, ← uM_eq]
  linear_combination (Am s y).det * trace_comboN (uM s y) (Complex.I * s) k l

theorem dirC_detBm {s : ℂ} (hs : s = 1 ∨ s = -1) (y : E n) (k l : Fin n) :
    dirC (fun y => (Bm s y).det) (vkl k l) y = Complex.I * s * (Bm s y).det * vM s y k l := by
  rw [dirC, fderiv_detBm hs, fderiv_detBm hs, ← vM_eq]
  linear_combination (Bm s y).det * trace_combo (vM s y) (Complex.I * s) k l

theorem detU_eq (s : ℂ) (y : E n) : (uM s y).det = ((Am s y).det)⁻¹ := by
  rw [uM_eq, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']

theorem detV_eq (s : ℂ) (y : E n) : (vM s y).det = ((Bm s y).det)⁻¹ := by
  rw [vM_eq, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']

theorem contDiff_detU {s : ℂ} (hs : s = 1 ∨ s = -1) : ContDiff ℝ (⊤ : ℕ∞) (fun y : E n => (uM s y).det) := by
  simp_rw [detU_eq]; exact (contDiff_detAm s).inv (det_Am_ne hs)

theorem contDiff_detV {s : ℂ} (hs : s = 1 ∨ s = -1) : ContDiff ℝ (⊤ : ℕ∞) (fun y : E n => (vM s y).det) := by
  simp_rw [detV_eq]; exact (contDiff_detBm s).inv (det_Bm_ne hs)

theorem dirC_detU {s : ℂ} (hs : s = 1 ∨ s = -1) (y : E n) (k l : Fin n) :
    dirC (fun y => (uM s y).det) (vkl k l) y = Complex.I * s * uM s y k l * (uM s y).det := by
  simp_rw [detU_eq]
  rw [dirC_comp (hasDerivAt_inv (det_Am_ne hs y)) (diffAt_of (contDiff_detAm s) y), dirC_detAm hs]
  have := det_Am_ne hs y
  field_simp <;> ring

theorem dirC_detV {s : ℂ} (hs : s = 1 ∨ s = -1) (y : E n) (k l : Fin n) :
    dirC (fun y => (vM s y).det) (vkl k l) y = -(Complex.I * s * vM s y k l * (vM s y).det) := by
  simp_rw [detV_eq]
  rw [dirC_comp (hasDerivAt_inv (det_Bm_ne hs y)) (diffAt_of (contDiff_detBm s) y), dirC_detBm hs]
  have := det_Bm_ne hs y
  field_simp <;> ring

theorem dirC_pow {f : E n → ℂ} {y : E n} (hf : DifferentiableAt ℝ f y) (p : ℕ) (w : Fin n → Fin n → ℂ) (c : ℂ)
    (hc : dirC f w y = c * f y) : dirC (fun y => f y ^ p) w y = p * c * f y ^ p := by
  rw [dirC_comp (hasDerivAt_pow p (f y)) hf, hc]
  cases p with
  | zero => simp
  | succ p => simp only [Nat.cast_succ, Nat.add_sub_cancel, pow_succ]; ring

theorem dP_eq {s : ℂ} (hs : s = 1 ∨ s = -1) (y : E n) : ((dP y : ℝ) : ℂ) = (Bm s y).det * (Am s y).det :=
  (det_Bm_mul_det_Am hs y).symm

theorem contDiff_dPpow (z : ℂ) : ContDiff ℝ (⊤ : ℕ∞) (fun y : E n => ((dP y : ℝ) : ℂ) ^ (-z)) := by
  have hP : ContDiff ℝ (⊤ : ℕ∞) (fun y : E n => ((dP y : ℝ) : ℂ)) := by
    have : (fun y : E n => ((dP y : ℝ) : ℂ)) = fun y => (1 + herm y * herm y).det :=
      funext fun y => (det_one_add_eq y).symm
    rw [this]
    refine contDiff_det_of fun a b => ?_
    simp only [Matrix.add_apply, Matrix.mul_apply]
    exact contDiff_const.add (ContDiff.sum fun c _ => (contDiff_herm_entry a c).mul (contDiff_herm_entry c b))
  have e : (fun y : E n => ((dP y : ℝ) : ℂ) ^ (-z)) = fun y => Complex.exp (Complex.log ((dP y : ℝ) : ℂ) * (-z)) :=
    funext fun y => Complex.cpow_def_of_ne_zero (by exact_mod_cast (dP_pos y).ne') _
  rw [e]
  refine ContDiff.cexp (ContDiff.mul ?_ contDiff_const)
  rw [contDiff_iff_contDiffAt]
  intro y
  exact ((Complex.contDiffAt_log (Complex.ofReal_mem_slitPlane.mpr (dP_pos y))).restrict_scalars ℝ).comp y hP.contDiffAt

theorem dirC_dPpow {s : ℂ} (hs : s = 1 ∨ s = -1) (z : ℂ) (y : E n) (k l : Fin n) :
    dirC (fun y : E n => ((dP y : ℝ) : ℂ) ^ (-z)) (vkl k l) y =
      Complex.I * s * z * (uM s y k l - vM s y k l) * ((dP y : ℝ) : ℂ) ^ (-z) := by
  have hmem : ((dP y : ℝ) : ℂ) ∈ Complex.slitPlane := Complex.ofReal_mem_slitPlane.mpr (dP_pos y)
  have hne : ((dP y : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (dP_pos y).ne'
  have hPd : DifferentiableAt ℝ (fun y : E n => (Bm s y).det * (Am s y).det) y :=
    (diffAt_of (contDiff_detBm s) y).mul (diffAt_of (contDiff_detAm s) y)
  have e : (fun y : E n => ((dP y : ℝ) : ℂ) ^ (-z)) = fun y => ((Bm s y).det * (Am s y).det) ^ (-z) :=
    funext fun y => by rw [dP_eq hs]
  rw [e]
  rw [dP_eq hs] at hmem
  rw [dirC_comp (Complex.hasStrictDerivAt_cpow_const hmem).hasDerivAt hPd,
    dirC_mul (diffAt_of (contDiff_detBm s) y) (diffAt_of (contDiff_detAm s) y), dirC_detAm hs, dirC_detBm hs,
    ← dP_eq hs, Complex.cpow_sub _ _ hne, Complex.cpow_one]
  rw [show ((Bm s y).det * (-(Complex.I * s) * (Am s y).det * uM s y k l) +
      (Am s y).det * (Complex.I * s * (Bm s y).det * vM s y k l)) =
      -(Complex.I * s) * ((Bm s y).det * (Am s y).det) * (uM s y k l - vM s y k l) by ring, ← dP_eq hs]
  field_simp <;> ring

def ent (s : ℂ) (e : Bool × Fin n × Fin n) (y : E n) : ℂ := if e.1 then vM s y e.2.1 e.2.2 else uM s y e.2.1 e.2.2

theorem evUV_eq (s : ℂ) (R : MvPolynomial (Bool × Fin n × Fin n) ℂ) (y : E n) :
    evUV s R y = MvPolynomial.eval (fun e => ent s e y) R := rfl

theorem contDiff_ent {s : ℂ} (hs : s = 1 ∨ s = -1) (e : Bool × Fin n × Fin n) :
    ContDiff ℝ (⊤ : ℕ∞) (ent (n := n) s e) := by
  unfold ent
  split_ifs
  · exact contDiff_vM_entry hs _ _
  · exact contDiff_uM_entry hs _ _

def dEnt (s : ℂ) (k l : Fin n) (e : Bool × Fin n × Fin n) : MvPolynomial (Bool × Fin n × Fin n) ℂ :=
  if e.1 then -(C (Complex.I * s) * X (true, e.2.1, l) * X (true, k, e.2.2))
  else C (Complex.I * s) * X (false, e.2.1, l) * X (false, k, e.2.2)

theorem dirC_ent {s : ℂ} (hs : s = 1 ∨ s = -1) (y : E n) (k l : Fin n) (e : Bool × Fin n × Fin n) :
    dirC (ent s e) (vkl k l) y = MvPolynomial.eval (fun e => ent s e y) (dEnt s k l e) := by
  obtain ⟨b, a, c⟩ := e
  cases b
  · have e1 : ent (n := n) s (false, a, c) = fun y => uM s y a c := by funext y; simp [ent]
    rw [e1, dirC_uM hs]
    simp [dEnt, ent] <;> ring
  · have e1 : ent (n := n) s (true, a, c) = fun y => vM s y a c := by funext y; simp [ent]
    rw [e1, dirC_vM hs]
    simp [dEnt, ent] <;> ring

theorem contDiff_evUV {s : ℂ} (hs : s = 1 ∨ s = -1) (R : MvPolynomial (Bool × Fin n × Fin n) ℂ) :
    ContDiff ℝ (⊤ : ℕ∞) (evUV s R) :=
  contDiff_eval (fun e y => ent s e y) (contDiff_ent hs) R

theorem dirC_evUV {s : ℂ} (hs : s = 1 ∨ s = -1) (y : E n) (k l : Fin n) (R : MvPolynomial (Bool × Fin n × Fin n) ℂ) :
    dirC (evUV s R) (vkl k l) y = evUV s (∑ e, MvPolynomial.pderiv e R * dEnt s k l e) y := by
  rw [show evUV s R = fun y => MvPolynomial.eval (fun e => ent s e y) R from rfl,
    dirC_eval (fun e y => ent s e y) (contDiff_ent hs) (vkl k l) y R, evUV_eq]
  simp only [map_sum, map_mul]
  exact Finset.sum_congr rfl fun e _ => by rw [dirC_ent hs]

def dR (s z : ℂ) (p q : ℕ) (k l : Fin n) (R : MvPolynomial (Bool × Fin n × Fin n) ℂ) :
    MvPolynomial (Bool × Fin n × Fin n) ℂ :=
  C (Complex.I * s) * (C z * (X (false, k, l) - X (true, k, l)) + C (p : ℂ) * X (false, k, l) -
    C (q : ℂ) * X (true, k, l)) * R + ∑ e, MvPolynomial.pderiv e R * dEnt s k l e

theorem contDiff_cls {s : ℂ} (hs : s = 1 ∨ s = -1) (z : ℂ) (p q : ℕ) (R : MvPolynomial (Bool × Fin n × Fin n) ℂ) :
    ContDiff ℝ (⊤ : ℕ∞) (cls s z p q R) :=
  (((contDiff_dPpow z).mul ((contDiff_detU hs).pow p)).mul ((contDiff_detV hs).pow q)).mul (contDiff_evUV hs R)

theorem dirC_cls {s : ℂ} (hs : s = 1 ∨ s = -1) (z : ℂ) (p q : ℕ) (R : MvPolynomial (Bool × Fin n × Fin n) ℂ)
    (y : E n) (k l : Fin n) : dirC (cls s z p q R) (vkl k l) y = cls s z p q (dR s z p q k l R) y := by
  have h1 := diffAt_of (contDiff_dPpow (n := n) z) y
  have h2 := diffAt_of ((contDiff_detU (n := n) hs).pow p) y
  have h3 := diffAt_of ((contDiff_detV (n := n) hs).pow q) y
  have h4 := diffAt_of (contDiff_evUV hs R) y
  rw [show cls s z p q R = fun y => ((dP y : ℝ) : ℂ) ^ (-z) * (uM s y).det ^ p * (vM s y).det ^ q * evUV s R y from rfl]
  rw [dirC_mul (f := fun y => ((dP y : ℝ) : ℂ) ^ (-z) * (uM s y).det ^ p * (vM s y).det ^ q) (g := evUV s R)
      ((h1.mul h2).mul h3) h4,
    dirC_mul (f := fun y => ((dP y : ℝ) : ℂ) ^ (-z) * (uM s y).det ^ p) (g := fun y => (vM s y).det ^ q)
      (h1.mul h2) h3,
    dirC_mul (f := fun y => ((dP y : ℝ) : ℂ) ^ (-z)) (g := fun y => (uM s y).det ^ p) h1 h2, dirC_dPpow hs,
    dirC_pow (diffAt_of (contDiff_detU hs) y) p _ _ (dirC_detU hs y k l),
    dirC_pow (diffAt_of (contDiff_detV hs) y) q _ (-(Complex.I * s * vM s y k l)) (by rw [dirC_detV hs]; ring),
    dirC_evUV hs]
  simp only [cls, dR, evUV_eq, map_add, map_mul, map_sub, eval_C, eval_X, ent]
  simp only [Bool.false_eq_true, if_false, if_true]
  ring

theorem norm_eval_le {σ : Type} (x : σ → ℂ) (hx : ∀ i, ‖x i‖ ≤ 1) (R : MvPolynomial σ ℂ) :
    ‖MvPolynomial.eval x R‖ ≤ ∑ m ∈ R.support, ‖MvPolynomial.coeff m R‖ := by
  rw [MvPolynomial.eval_eq]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun m _ => ?_)
  rw [norm_mul]
  have : ‖∏ i ∈ m.support, x i ^ m i‖ ≤ 1 := by
    rw [norm_prod]
    exact Finset.prod_le_one (fun _ _ => norm_nonneg _) fun i _ => by
      rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) (hx i)
  calc ‖MvPolynomial.coeff m R‖ * ‖∏ i ∈ m.support, x i ^ m i‖ ≤ ‖MvPolynomial.coeff m R‖ * 1 :=
        mul_le_mul_of_nonneg_left this (norm_nonneg _)
    _ = _ := mul_one _

theorem norm_ent_le {s : ℂ} (hs : s = 1 ∨ s = -1) (y : E n) (e : Bool × Fin n × Fin n) : ‖ent s e y‖ ≤ 1 := by
  unfold ent; split_ifs
  · exact norm_vM_le hs y _ _
  · exact norm_uM_le hs y _ _

theorem cls_bound {s : ℂ} (hs : s = 1 ∨ s = -1) (z : ℂ) (p q : ℕ) (R : MvPolynomial (Bool × Fin n × Fin n) ℂ)
    (y : E n) : ‖cls s z p q R y‖ ≤
      (∑ m ∈ R.support, ‖MvPolynomial.coeff m R‖) * (dP y) ^ (-(z.re + (p + q : ℝ) / 2)) := by
  have hd := dP_pos y
  have e1 : ‖((dP y : ℝ) : ℂ) ^ (-z)‖ = (dP y) ^ (-z.re) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hd, Complex.neg_re]
  have e2 := norm_det_pow hd (norm_det_uM_sq hs y) p
  have e3 := norm_det_pow hd (norm_det_vM_sq hs y) q
  have e4 := norm_eval_le (fun e => ent s e y) (norm_ent_le hs y) R
  simp only [cls, norm_mul]
  rw [e1, e2, e3]
  have hC : 0 ≤ ∑ m ∈ R.support, ‖MvPolynomial.coeff m R‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hpos : 0 ≤ (dP y) ^ (-z.re) * (dP y) ^ (-(p : ℝ) / 2) * (dP y) ^ (-(q : ℝ) / 2) := by positivity
  calc (dP y) ^ (-z.re) * (dP y) ^ (-(p : ℝ) / 2) * (dP y) ^ (-(q : ℝ) / 2) * ‖evUV s R y‖
      ≤ (dP y) ^ (-z.re) * (dP y) ^ (-(p : ℝ) / 2) * (dP y) ^ (-(q : ℝ) / 2) *
          (∑ m ∈ R.support, ‖MvPolynomial.coeff m R‖) := mul_le_mul_of_nonneg_left (by rw [evUV_eq]; exact e4) hpos
    _ = _ := by
      rw [← Real.rpow_add hd, ← Real.rpow_add hd]
      rw [mul_comm]; congr 2; ring

theorem clsBound : ClsBound := by
  intro n s hs p q R z
  refine ⟨contDiff_cls hs z p q R, fun L => ?_⟩
  obtain ⟨R', hR'⟩ : ∃ R', L.foldr (fun kl g => Dkl kl.1 kl.2 g) (cls s z p q R) = cls s z p q R' := by
    induction L with
    | nil => exact ⟨R, rfl⟩
    | cons kl L ih =>
      obtain ⟨R', h⟩ := ih
      refine ⟨dR s z p q kl.1 kl.2 R', ?_⟩
      rw [List.foldr_cons, h]
      funext y
      exact dirC_cls hs z p q R' y kl.1 kl.2
  rw [hR']
  exact ⟨_, fun y => cls_bound hs z p q R' y⟩

end PositivityTheory.Rg.Sw.WR.B
