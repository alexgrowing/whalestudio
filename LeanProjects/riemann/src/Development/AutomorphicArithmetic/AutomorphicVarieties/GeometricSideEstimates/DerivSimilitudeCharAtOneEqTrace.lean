import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.ThStmt
open UpperTheory.V.Lit.Geo
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor
open scoped ContDiff

private theorem der_det {a : ℕ} (M : Matrix (Fin a) (Fin a) ℂ) :
    HasDerivAt (fun r : ℂ => (1 + r • M).det) M.trace 0 := by
  obtain ⟨p, hp⟩ : ∃ p : Polynomial ℂ, ∀ r : ℂ, (1 + r • M).det = 1 + M.trace * r + p.eval r * r ^ 2 :=
    ⟨_, fun r => Matrix.det_one_add_smul r M⟩
  have h1 := (((hasDerivAt_id (0 : ℂ)).const_mul M.trace).const_add 1).add
    ((p.hasDerivAt 0).mul ((hasDerivAt_id (0 : ℂ)).pow 2))
  rw [funext hp]
  exact HasDerivAt.congr_deriv h1 (by simp)

private theorem der_log {a : ℕ} (M : Matrix (Fin a) (Fin a) ℂ) :
    HasDerivAt (fun t : ℝ => Real.log ‖(1 + (t : ℂ) • M).det‖) M.trace.re 0 := by
  have h1 := (der_det M).clog (by simp)
  have h2 : HasDerivAt (fun r : ℂ => Complex.log (1 + r • M).det) M.trace ((0 : ℝ) : ℂ) := by
    simpa using h1
  have h3 := h2.real_of_complex
  simpa only [Complex.log_re] using h3

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

private theorem det_ne {y : Matrix (Fin a) (Fin a) (Cinf E)} (hy : IsUnit y) (w : InfinitePlace E) : y.det w ≠ 0 :=
  (((Matrix.isUnit_iff_isUnit_det y).1 hy).map (Pi.evalMonoidHom (fun _ : InfinitePlace E => ℂ) w)).ne_zero

private theorem sm_at {y : Lie E a} (hy : IsUnit (Matrix.of y)) :
    ContDiffAt ℝ ∞ (fun y : Lie E a => sc (Matrix.of y)) y := by
  unfold sc
  refine ((ContDiffAt.sum fun w _ => ?_).div_const _).neg.exp
  have h : ContDiff ℝ ∞ fun x : Lie E a => (Matrix.of x).det w :=
    (contDiff_apply ℝ ℂ w).comp GlobalTheory.CuspRep.contDiff_det
  exact (h.contDiffAt.norm ℝ (det_ne hy w)).log (norm_ne_zero_iff.2 (det_ne hy w))

private theorem det_line (X : Lie E a) (t : ℝ) (w : InfinitePlace E) :
    (Matrix.of (oneL E a + t • X)).det w = (1 + (t : ℂ) • Matrix.of fun i j => X i j w).det := by
  have h := (Pi.evalRingHom (fun _ : InfinitePlace E => ℂ) w).map_det (Matrix.of (oneL E a + t • X))
  refine h.trans (congrArg _ ?_)
  ext i j
  by_cases hij : i = j <;> simp [oneL, toL, Matrix.one_apply, hij]

private theorem der_sc (X : Lie E a) :
    HasDerivAt (fun t : ℝ => sc (Matrix.of (oneL E a + t • X))) (-ell E a X) 0 := by
  unfold sc
  simp only [det_line]
  have h := ((HasDerivAt.fun_sum (u := Finset.univ) fun (w : InfinitePlace E) _ =>
    der_log (Matrix.of fun i j => X i j w)).div_const ((a : ℝ) * Fintype.card (InfinitePlace E))).neg.exp
  exact HasDerivAt.congr_deriv h (by simp [ell, Matrix.trace])

private theorem sc_mul_star {y : Matrix (Fin a) (Fin a) (Cinf E)} : sc (y * star y) = sc y ^ 2 := by
  unfold sc
  rw [← Real.exp_nat_mul]
  congr 1
  have h : ∀ w, Real.log ‖(y * star y).det w‖ = 2 * Real.log ‖y.det w‖ := fun w => by
    rw [Matrix.det_mul, Matrix.star_eq_conjTranspose, Matrix.det_conjTranspose, Pi.mul_apply, Pi.star_apply,
      norm_mul, norm_star, ← sq, Real.log_pow]
    norm_num
  simp only [h, ← Finset.mul_sum]
  push_cast
  ring

private theorem sc_one : sc (1 : Matrix (Fin a) (Fin a) (Cinf E)) = 1 := by
  simp [sc]

theorem UpperTheory.deriv_similitudeChar_at_one_eq_trace :
    ScSm := by
  intro E _ _ a
  refine ⟨fun y hy => (sm_at hy).contDiffWithinAt, sc_one, fun X => ?_, fun h => sc_mul_star, fun k => ?_⟩
  · have h1 : IsUnit (Matrix.of (oneL E a)) := isUnit_one
    have hd := ((sm_at h1).differentiableAt (by simp)).hasFDerivAt
    have hl : HasDerivAt (fun t : ℝ => oneL E a + t • X) X 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const X).const_add (oneL E a)
    have h2 := HasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hd hl (by simp)
    exact h2.unique (der_sc X)
  · have h : sc k.1 ^ 2 = 1 := by
      rw [← sc_mul_star, Matrix.mem_unitaryGroup_iff.1 k.2, sc_one]
    have hp : 0 < sc k.1 := Real.exp_pos _
    exact (pow_eq_one_iff_of_nonneg hp.le two_ne_zero).1 h
