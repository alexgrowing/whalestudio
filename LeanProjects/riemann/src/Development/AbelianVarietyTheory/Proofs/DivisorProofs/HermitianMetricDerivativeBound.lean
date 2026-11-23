import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WirtConst
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DualGramInterpGram
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FderivDetEqTraceAdjugateStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianDerivWirtingerDecompositionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PositiveDefiniteLeadingMinorInverseBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianBoundedFormMulVecBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceProductSubmatrixNormBoundStatement

open GlobalTheory.MatDeriv GlobalTheory.GradedNorm Matrix ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexOrder Topology

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.GradedLogDeriv

theorem jacobi {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {n : ℕ} (B : E → Matrix (Fin n) (Fin n) ℂ) (w : E)
    (hB : ∀ a b, DifferentiableAt ℝ (fun w' => B w' a b) w) :
    DifferentiableAt ℝ (fun w' => (B w').det) w ∧
      ∀ ξ : E, fderiv ℝ (fun w' => (B w').det) w ξ = ((B w).adjugate * dMat B w ξ).trace  :=
  GlobalTheory.T.fderiv_det_eq_trace_adjugate B w hB

theorem dMat_eq {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {m : ℕ} (H : E → Matrix (Fin m) (Fin m) ℂ) (w : E)
    (hH : ∀ᶠ w' in 𝓝 w, (H w').IsHermitian) (hd : ∀ a b, DifferentiableAt ℝ (fun w' => H w' a b) w) (ξ : E) :
    dMat H w ξ = wirt H w ξ + (wirt H w ξ)ᴴ  :=
  GlobalTheory.T.hermitian_deriv_wirtinger_decomposition H w hH hd ξ

theorem inv_block_le {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) (k : Fin (m + 1)) (c : ℝ) (hc : 0 < c)
    (hu : IsUnit (M.submatrix (Fin.castLE (Nat.le_of_lt_succ k.isLt)) (Fin.castLE (Nat.le_of_lt_succ k.isLt))).det)
    (hM : ∀ v : Fin m → ℂ, c * ‖v‖ ^ 2 ≤ (star v ⬝ᵥ M *ᵥ v).re) (z : Fin k → ℂ) :
    ‖(M.submatrix (Fin.castLE (Nat.le_of_lt_succ k.isLt)) (Fin.castLE (Nat.le_of_lt_succ k.isLt)))⁻¹ *ᵥ z‖ ≤
      m / c * ‖z‖  :=
  GlobalTheory.T.positive_definite_leading_minor_inverse_bound M k c hc hu hM z

theorem mulVec_le {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (c : ℝ) (hM : M.IsHermitian)
    (hq : ∀ v : Fin n → ℂ, 0 ≤ (star v ⬝ᵥ M *ᵥ v).re ∧ (star v ⬝ᵥ M *ᵥ v).re ≤ c * ‖v‖ ^ 2) (x : Fin n → ℂ) :
    ‖M *ᵥ x‖ ≤ 4 * n * c * ‖x‖  :=
  GlobalTheory.T.hermitian_bounded_form_mulVec_bound M c hM hq x

theorem trace_le {m : ℕ} (k : Fin (m + 1)) (P : Matrix (Fin k) (Fin k) ℂ) (X : Matrix (Fin m) (Fin m) ℂ) (b g : ℝ)
    (hb : 0 ≤ b) (hg : 0 ≤ g) (hP : ∀ y, ‖P *ᵥ y‖ ≤ b * ‖y‖) (hX : ∀ x, ‖X *ᵥ x‖ ≤ g * ‖x‖) :
    ‖(P * X.submatrix (Fin.castLE (Nat.le_of_lt_succ k.isLt)) (Fin.castLE (Nat.le_of_lt_succ k.isLt))).trace‖ ≤
      m * (b * g)  :=
  GlobalTheory.T.trace_product_submatrix_norm_bound k P X b g hb hg hP hX

theorem log_lminor {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {m : ℕ} (H : E → Matrix (Fin m) (Fin m) ℂ)
    (w : E) (hH : ∀ᶠ w' in 𝓝 w, (H w').IsHermitian) (hp : (H w).PosDef)
    (hd : ∀ a b, DifferentiableAt ℝ (fun w' => H w' a b) w) (k : Fin (m + 1)) :
    DifferentiableAt ℝ (fun w' => Real.log (lminor (H w') k).re) w ∧ ∀ ξ : E,
      fderiv ℝ (fun w' => Real.log (lminor (H w') k).re) w ξ =
        2 * (((H w).submatrix (Fin.castLE (Nat.le_of_lt_succ k.isLt)) (Fin.castLE (Nat.le_of_lt_succ k.isLt)))⁻¹ *
          (wirt H w ξ).submatrix (Fin.castLE (Nat.le_of_lt_succ k.isLt))
            (Fin.castLE (Nat.le_of_lt_succ k.isLt))).trace.re := by
  set c := Fin.castLE (Nat.le_of_lt_succ k.isLt)
  set B : E → Matrix (Fin k) (Fin k) ℂ := fun w' => (H w').submatrix c c with hB
  have hBd : ∀ a b, DifferentiableAt ℝ (fun w' => B w' a b) w := fun a b => hd (c a) (c b)
  obtain ⟨hJd, hJ⟩ := jacobi B w hBd
  have hpos : 0 < (B w).det := lminor_pos hp k
  obtain ⟨hre, him⟩ := Complex.pos_iff.1 hpos
  have hF : HasFDerivAt (fun w' => (B w').det.re) (Complex.reCLM.comp (fderiv ℝ (fun w' => (B w').det) w)) w :=
    Complex.reCLM.hasFDerivAt.comp w hJd.hasFDerivAt
  have hL : HasFDerivAt (fun w' => Real.log (lminor (H w') k).re) _ w := hF.log hre.ne'
  refine ⟨hL.differentiableAt, fun ξ => ?_⟩
  rw [hL.fderiv]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, Complex.reCLM_apply, smul_eq_mul, hJ]
  have hdM : dMat B w ξ = (dMat H w ξ).submatrix c c := rfl
  have hne : (B w).det ≠ 0 := hpos.ne'
  have hadj : (B w).adjugate = (B w).det • (B w)⁻¹ := by
    rw [Matrix.inv_def, Ring.inverse_eq_inv', smul_smul, mul_inv_cancel₀ hne, one_smul]
  have hHerm : ((B w)⁻¹).IsHermitian := (hp.isHermitian.submatrix c).inv
  have hst : ((B w)⁻¹ * ((wirt H w ξ).submatrix c c)ᴴ).trace =
      star (((B w)⁻¹ * (wirt H w ξ).submatrix c c).trace) := by
    rw [← trace_conjTranspose, conjTranspose_mul, hHerm.eq, trace_mul_comm]
  have e1 : ((B w).det • ((B w)⁻¹ * (dMat H w ξ).submatrix c c)).trace.re =
      (B w).det.re * ((B w)⁻¹ * (dMat H w ξ).submatrix c c).trace.re := by
    rw [trace_smul, smul_eq_mul, Complex.mul_re, ← him, zero_mul, sub_zero]
  have hsub : (wirt H w ξ + (wirt H w ξ)ᴴ).submatrix c c =
      (wirt H w ξ).submatrix c c + ((wirt H w ξ).submatrix c c)ᴴ := by
    ext a b; simp
  rw [hdM, hadj, Matrix.smul_mul, e1, ← mul_assoc, inv_mul_cancel₀ hre.ne', one_mul, dMat_eq H w hH hd ξ,
    hsub, Matrix.mul_add, trace_add, hst, Complex.add_re, Complex.star_def,
    Complex.conj_re]
  ring

theorem log_grSq_eq {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) (hM : M.PosDef) (i : Fin m) :
    Real.log (grSq M i) = Real.log (lminor M i.succ).re - Real.log (lminor M i.castSucc).re := by
  obtain ⟨h1, h1'⟩ := Complex.pos_iff.1 (lminor_pos hM i.succ)
  obtain ⟨h2, h2'⟩ := Complex.pos_iff.1 (lminor_pos hM i.castSucc)
  have e : grSq M i = (lminor M i.succ).re / (lminor M i.castSucc).re := by
    rw [grSq, Complex.div_re, ← h1', ← h2', Complex.normSq_apply, ← h2']
    field_simp
    ring
  rw [e, Real.log_div h1.ne' h2.ne']

theorem nonneg_of_bound {m : ℕ} (hm : 0 < m) (X : Matrix (Fin m) (Fin m) ℂ) (a : ℝ)
    (h : ∀ x, ‖X *ᵥ x‖ ≤ a * ‖x‖) : 0 ≤ a := by
  have := h (Pi.single ⟨0, hm⟩ 1)
  have hn : ‖(Pi.single ⟨0, hm⟩ (1 : ℂ) : Fin m → ℂ)‖ = 1 := by
    rw [Pi.norm_single, norm_one]
  rw [hn, mul_one] at this
  exact (norm_nonneg _).trans this

theorem bound_key {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (m : ℕ) (Hh H0 : E → Matrix (Fin m) (Fin m) ℂ)
    (rr : E → ℝ) (q : E → E → ℝ) (μ K c₀ C₀ : ℝ) (hm : 0 < m) (hc₀ : 0 < c₀) (hμ : 0 ≤ μ) (w : E) (hr : 1 ≤ rr w)
    (hPh : (Hh w).PosDef) (hP0 : (H0 w).PosDef)
    (h2 : ∀ v : Fin m → ℂ, c₀ * ‖v‖ ^ 2 ≤ (star v ⬝ᵥ H0 w *ᵥ v).re ∧ (star v ⬝ᵥ H0 w *ᵥ v).re ≤ C₀ * ‖v‖ ^ 2 ∧
      rr w ^ (-μ) * (star v ⬝ᵥ H0 w *ᵥ v).re ≤ (star v ⬝ᵥ Hh w *ᵥ v).re ∧
      (star v ⬝ᵥ Hh w *ᵥ v).re ≤ rr w ^ μ * (star v ⬝ᵥ H0 w *ᵥ v).re) (ξ : E)
    (h3 : c₀ * ‖ξ‖ ≤ q w ξ ∧ ∀ v : Fin m → ℂ, ‖((H0 w)⁻¹ * wirt H0 w ξ) *ᵥ v‖ ≤ C₀ * ‖ξ‖ * ‖v‖ ∧
      ‖((Hh w)⁻¹ * wirt Hh w ξ - (H0 w)⁻¹ * wirt H0 w ξ) *ᵥ v‖ ≤ K * rr w ^ μ * Real.exp (rr w / 2) * q w ξ * ‖v‖) :
    0 ≤ C₀ ∧ ∀ k : Fin (m + 1),
      ‖(((Hh w).submatrix (Fin.castLE (Nat.le_of_lt_succ k.isLt)) (Fin.castLE (Nat.le_of_lt_succ k.isLt)))⁻¹ *
          (wirt Hh w ξ).submatrix (Fin.castLE (Nat.le_of_lt_succ k.isLt)) (Fin.castLE (Nat.le_of_lt_succ k.isLt))).trace -
        (((H0 w).submatrix (Fin.castLE (Nat.le_of_lt_succ k.isLt)) (Fin.castLE (Nat.le_of_lt_succ k.isLt)))⁻¹ *
          (wirt H0 w ξ).submatrix (Fin.castLE (Nat.le_of_lt_succ k.isLt)) (Fin.castLE (Nat.le_of_lt_succ k.isLt))).trace‖ ≤
      4 * m ^ 3 * C₀ / c₀ * (|K| + 2 * C₀ / c₀) * (rr w ^ μ) ^ 3 * Real.exp (rr w / 2) * q w ξ := by
  set R := rr w ^ μ with hR
  set e := Real.exp (rr w / 2) with he
  have hR1 : 1 ≤ R := Real.one_le_rpow hr hμ
  have hRneg : rr w ^ (-μ) = R⁻¹ := Real.rpow_neg (by linarith) μ
  have he1 : 1 ≤ e := Real.one_le_exp (by linarith)
  obtain ⟨hq, h3'⟩ := h3
  have hqn : 0 ≤ q w ξ := le_trans (by positivity) hq
  have hC : c₀ ≤ C₀ := by
    have := h2 (Pi.single ⟨0, hm⟩ 1)
    have hn : ‖(Pi.single ⟨0, hm⟩ (1 : ℂ) : Fin m → ℂ)‖ = 1 := by rw [Pi.norm_single, norm_one]
    rw [hn] at this
    linarith [this.1, this.2.1]
  have hC0 : 0 ≤ C₀ := hc₀.le.trans hC
  refine ⟨hC0, fun k => ?_⟩
  set c := Fin.castLE (Nat.le_of_lt_succ k.isLt)
  have huh : IsUnit (Hh w).det := (isUnit_iff_isUnit_det _).1 hPh.isUnit
  have hu0 : IsUnit (H0 w).det := (isUnit_iff_isUnit_det _).1 hP0.isUnit
  set θh := (Hh w)⁻¹ * wirt Hh w ξ
  set θ0 := (H0 w)⁻¹ * wirt H0 w ξ
  have eh : wirt Hh w ξ = Hh w * (θh - θ0) + Hh w * θ0 := by
    rw [← Matrix.mul_add, sub_add_cancel, Matrix.mul_nonsing_inv_cancel_left _ _ huh]
  have e0 : wirt H0 w ξ = H0 w * θ0 := (Matrix.mul_nonsing_inv_cancel_left _ _ hu0).symm
  have hsub : (Hh w * (θh - θ0) + Hh w * θ0).submatrix c c =
      (Hh w * (θh - θ0)).submatrix c c + (Hh w * θ0).submatrix c c := by ext a b; simp
  rw [eh, e0, hsub, Matrix.mul_add, trace_add]

  have qh_lo : ∀ v : Fin m → ℂ, R⁻¹ * c₀ * ‖v‖ ^ 2 ≤ (star v ⬝ᵥ Hh w *ᵥ v).re := fun v => by
    obtain ⟨a1, -, a3, -⟩ := h2 v
    rw [hRneg] at a3
    calc R⁻¹ * c₀ * ‖v‖ ^ 2 = R⁻¹ * (c₀ * ‖v‖ ^ 2) := by ring
      _ ≤ R⁻¹ * (star v ⬝ᵥ H0 w *ᵥ v).re := mul_le_mul_of_nonneg_left a1 (by positivity)
      _ ≤ _ := a3
  have bh : ∀ y : Fin k → ℂ, ‖((Hh w).submatrix c c)⁻¹ *ᵥ y‖ ≤ m * R / c₀ * ‖y‖ := fun y => by
    have := inv_block_le (Hh w) k (R⁻¹ * c₀) (by positivity)
      ((isUnit_iff_ne_zero).2 (lminor_pos hPh k).ne') qh_lo y
    have e' : (m : ℝ) / (R⁻¹ * c₀) = m * R / c₀ := by field_simp
    rwa [e'] at this
  have b0 : ∀ y : Fin k → ℂ, ‖((H0 w).submatrix c c)⁻¹ *ᵥ y‖ ≤ m / c₀ * ‖y‖ := fun y =>
    inv_block_le (H0 w) k c₀ hc₀ ((isUnit_iff_ne_zero).2 (lminor_pos hP0 k).ne') (fun v => (h2 v).1) y
  have opH : ∀ x, ‖Hh w *ᵥ x‖ ≤ 4 * m * (R * C₀) * ‖x‖ := mulVec_le (Hh w) (R * C₀) hPh.isHermitian fun v => by
    obtain ⟨a1, a2, -, a4⟩ := h2 v
    refine ⟨le_trans (by positivity) (qh_lo v), a4.trans ?_⟩
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_left a2 (by positivity)
  have op0 : ∀ x, ‖H0 w *ᵥ x‖ ≤ 4 * m * C₀ * ‖x‖ := mulVec_le (H0 w) C₀ hP0.isHermitian fun v =>
    ⟨le_trans (by positivity) (h2 v).1, (h2 v).2.1⟩
  have hΔ : ∀ x, ‖(θh - θ0) *ᵥ x‖ ≤ K * R * e * q w ξ * ‖x‖ := fun x => (h3' x).2
  have hθ : ∀ x, ‖θ0 *ᵥ x‖ ≤ C₀ * ‖ξ‖ * ‖x‖ := fun x => (h3' x).1
  have nΔ := nonneg_of_bound hm _ _ hΔ
  have comp : ∀ (A θ : Matrix (Fin m) (Fin m) ℂ) (h a : ℝ), 0 ≤ h → (∀ x, ‖A *ᵥ x‖ ≤ h * ‖x‖) →
      (∀ x, ‖θ *ᵥ x‖ ≤ a * ‖x‖) → ∀ x, ‖(A * θ) *ᵥ x‖ ≤ h * a * ‖x‖ := fun A θ h a hh hA hθ x => by
    rw [← Matrix.mulVec_mulVec, mul_assoc]
    exact (hA _).trans (mul_le_mul_of_nonneg_left (hθ x) hh)
  have t1 := trace_le k _ _ _ _ (by positivity) (by positivity) bh
    (comp _ _ _ _ (by positivity) opH hΔ)
  have t2 := trace_le k _ _ _ _ (by positivity) (by positivity) bh
    (comp _ _ _ _ (by positivity) opH hθ)
  have t3 := trace_le k _ _ _ _ (by positivity) (by positivity) b0
    (comp _ _ _ _ (by positivity) op0 hθ)
  have hξ : C₀ * ‖ξ‖ ≤ C₀ / c₀ * q w ξ := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hc₀, mul_assoc]
    exact mul_le_mul_of_nonneg_left (by linarith) hC0
  set P0 := 4 * (m : ℝ) ^ 3 * C₀ / c₀ with hP0def
  have hP0n : 0 ≤ P0 := by positivity
  have e1 : (m : ℝ) * (m * R / c₀ * (4 * m * (R * C₀) * (K * R * e * q w ξ))) = P0 * (K * R ^ 3 * e * q w ξ) := by
    rw [hP0def]; ring
  have e2 : (m : ℝ) * (m * R / c₀ * (4 * m * (R * C₀) * (C₀ * ‖ξ‖))) = P0 * (R ^ 2 * (C₀ * ‖ξ‖)) := by
    rw [hP0def]; ring
  have e3 : (m : ℝ) * (m / c₀ * (4 * m * C₀ * (C₀ * ‖ξ‖))) = P0 * (C₀ * ‖ξ‖) := by
    rw [hP0def]; ring
  rw [e1] at t1
  rw [e2] at t2
  rw [e3] at t3
  have hR3 : 1 ≤ R ^ 3 := one_le_pow₀ hR1
  have hR23 : R ^ 2 ≤ R ^ 3 := pow_le_pow_right₀ hR1 (by norm_num)
  have hRe : R ^ 3 ≤ R ^ 3 * e := le_mul_of_one_le_right (by positivity) he1
  have s1 : K * R ^ 3 * e * q w ξ ≤ |K| * R ^ 3 * e * q w ξ := by
    gcongr; exact le_abs_self K
  have s2 : R ^ 2 * (C₀ * ‖ξ‖) ≤ R ^ 3 * e * (C₀ / c₀ * q w ξ) :=
    mul_le_mul (hR23.trans hRe) hξ (by positivity) (by positivity)
  have s3 : C₀ * ‖ξ‖ ≤ R ^ 3 * e * (C₀ / c₀ * q w ξ) :=
    hξ.trans (le_mul_of_one_le_left (by positivity) (hR3.trans hRe))
  calc _ ≤ ‖_‖ + ‖_‖ + ‖_‖ := norm_sub_le_of_le (norm_add_le _ _) le_rfl
    _ ≤ P0 * (|K| * R ^ 3 * e * q w ξ) + P0 * (R ^ 3 * e * (C₀ / c₀ * q w ξ)) +
        P0 * (R ^ 3 * e * (C₀ / c₀ * q w ξ)) := by
      gcongr ?_ + ?_ + ?_
      · exact t1.trans (mul_le_mul_of_nonneg_left s1 hP0n)
      · exact t2.trans (mul_le_mul_of_nonneg_left s2 hP0n)
      · exact t3.trans (mul_le_mul_of_nonneg_left s3 hP0n)
    _ = _ := by rw [hP0def]; ring

theorem deriv_log_grSq_ratio : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (m : ℕ) (S : Set E)
    (Hh H0 : E → Matrix (Fin m) (Fin m) ℂ) (rr : E → ℝ) (q : E → E → ℝ) (μ K c₀ C₀ : ℝ), IsOpen S → 0 < c₀ → 0 ≤ μ →
  (∀ w ∈ S, 1 ≤ rr w ∧ (Hh w).PosDef ∧ (H0 w).PosDef ∧ ∀ a b, DifferentiableAt ℝ (fun w' => Hh w' a b) w ∧
    DifferentiableAt ℝ (fun w' => H0 w' a b) w) →
  (∀ w ∈ S, ∀ v : Fin m → ℂ, c₀ * ‖v‖ ^ 2 ≤ (star v ⬝ᵥ H0 w *ᵥ v).re ∧ (star v ⬝ᵥ H0 w *ᵥ v).re ≤ C₀ * ‖v‖ ^ 2 ∧
    rr w ^ (-μ) * (star v ⬝ᵥ H0 w *ᵥ v).re ≤ (star v ⬝ᵥ Hh w *ᵥ v).re ∧
    (star v ⬝ᵥ Hh w *ᵥ v).re ≤ rr w ^ μ * (star v ⬝ᵥ H0 w *ᵥ v).re) →
  (∀ w ∈ S, ∀ ξ : E, c₀ * ‖ξ‖ ≤ q w ξ ∧ ∀ v : Fin m → ℂ, ‖((H0 w)⁻¹ * wirt H0 w ξ) *ᵥ v‖ ≤ C₀ * ‖ξ‖ * ‖v‖ ∧
    ‖((Hh w)⁻¹ * wirt Hh w ξ - (H0 w)⁻¹ * wirt H0 w ξ) *ᵥ v‖ ≤ K * rr w ^ μ * Real.exp (rr w / 2) * q w ξ * ‖v‖) →
  ∃ K' : ℝ, 0 ≤ K' ∧ ∀ w ∈ S, ∀ i : Fin m,
    DifferentiableAt ℝ (fun w' => Real.log (grSq (Hh w') i) - Real.log (grSq (H0 w') i)) w ∧
    ∀ ξ : E, |fderiv ℝ (fun w' => Real.log (grSq (Hh w') i) - Real.log (grSq (H0 w') i)) w ξ| ≤
      K' * rr w ^ (3 * μ) * Real.exp (rr w / 2) * q w ξ := by
  intro E _ _ m S Hh H0 rr q μ K c₀ C₀ hS hc₀ hμ h1 h2 h3
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact ⟨0, le_rfl, fun _ _ i => i.elim0⟩
  refine ⟨4 * (4 * m ^ 3 * |C₀| / c₀ * (|K| + 2 * |C₀| / c₀)), by positivity, fun w hw i => ?_⟩
  obtain ⟨hr, hPh, hP0, hdiff⟩ := h1 w hw
  have hHh : ∀ᶠ w' in 𝓝 w, (Hh w').IsHermitian :=
    Filter.eventually_of_mem (hS.mem_nhds hw) fun w' hw' => (h1 w' hw').2.1.isHermitian
  have hH0 : ∀ᶠ w' in 𝓝 w, (H0 w').IsHermitian :=
    Filter.eventually_of_mem (hS.mem_nhds hw) fun w' hw' => (h1 w' hw').2.2.1.isHermitian
  have hdh : ∀ a b, DifferentiableAt ℝ (fun w' => Hh w' a b) w := fun a b => (hdiff a b).1
  have hd0 : ∀ a b, DifferentiableAt ℝ (fun w' => H0 w' a b) w := fun a b => (hdiff a b).2
  have hEq : (fun w' => Real.log (grSq (Hh w') i) - Real.log (grSq (H0 w') i)) =ᶠ[𝓝 w]
      fun w' => (Real.log (lminor (Hh w') i.succ).re - Real.log (lminor (Hh w') i.castSucc).re) -
        (Real.log (lminor (H0 w') i.succ).re - Real.log (lminor (H0 w') i.castSucc).re) :=
    Filter.eventually_of_mem (hS.mem_nhds hw) fun w' hw' => by
      simp only
      rw [log_grSq_eq _ (h1 w' hw').2.1, log_grSq_eq _ (h1 w' hw').2.2.1]
  obtain ⟨dh1, eh1⟩ := log_lminor Hh w hHh hPh hdh i.succ
  obtain ⟨dh2, eh2⟩ := log_lminor Hh w hHh hPh hdh i.castSucc
  obtain ⟨d01, e01⟩ := log_lminor H0 w hH0 hP0 hd0 i.succ
  obtain ⟨d02, e02⟩ := log_lminor H0 w hH0 hP0 hd0 i.castSucc
  have hF := ((dh1.hasFDerivAt.sub dh2.hasFDerivAt).sub (d01.hasFDerivAt.sub d02.hasFDerivAt)).congr_of_eventuallyEq hEq
  refine ⟨hF.differentiableAt, fun ξ => ?_⟩
  rw [hF.fderiv]
  simp only [ContinuousLinearMap.sub_apply, eh1, eh2, e01, e02]
  have key := bound_key m Hh H0 rr q μ K c₀ C₀ hm hc₀ hμ w hr hPh hP0 (h2 w hw) ξ (h3 w hw ξ)
  have hC : 0 ≤ C₀ := key.1
  have k1 := key.2 i.succ
  have k2 := key.2 i.castSucc
  set A1 := (((Hh w).submatrix (Fin.castLE (Nat.le_of_lt_succ i.succ.isLt)) (Fin.castLE (Nat.le_of_lt_succ i.succ.isLt)))⁻¹ *
    (wirt Hh w ξ).submatrix (Fin.castLE (Nat.le_of_lt_succ i.succ.isLt)) (Fin.castLE (Nat.le_of_lt_succ i.succ.isLt))).trace
  set B1 := (((H0 w).submatrix (Fin.castLE (Nat.le_of_lt_succ i.succ.isLt)) (Fin.castLE (Nat.le_of_lt_succ i.succ.isLt)))⁻¹ *
    (wirt H0 w ξ).submatrix (Fin.castLE (Nat.le_of_lt_succ i.succ.isLt)) (Fin.castLE (Nat.le_of_lt_succ i.succ.isLt))).trace
  set A2 := (((Hh w).submatrix (Fin.castLE (Nat.le_of_lt_succ i.castSucc.isLt)) (Fin.castLE (Nat.le_of_lt_succ i.castSucc.isLt)))⁻¹ *
    (wirt Hh w ξ).submatrix (Fin.castLE (Nat.le_of_lt_succ i.castSucc.isLt)) (Fin.castLE (Nat.le_of_lt_succ i.castSucc.isLt))).trace
  set B2 := (((H0 w).submatrix (Fin.castLE (Nat.le_of_lt_succ i.castSucc.isLt)) (Fin.castLE (Nat.le_of_lt_succ i.castSucc.isLt)))⁻¹ *
    (wirt H0 w ξ).submatrix (Fin.castLE (Nat.le_of_lt_succ i.castSucc.isLt)) (Fin.castLE (Nat.le_of_lt_succ i.castSucc.isLt))).trace
  have a1 := Complex.abs_re_le_norm (A1 - B1)
  have a2 := Complex.abs_re_le_norm (A2 - B2)
  rw [Complex.sub_re] at a1 a2
  have hR3 : rr w ^ (3 * μ) = (rr w ^ μ) ^ 3 := by
    rw [mul_comm, Real.rpow_mul (by linarith)]; norm_cast
  rw [hR3, abs_of_nonneg hC]
  rw [abs_le] at a1 a2 ⊢
  constructor <;> nlinarith [a1.1, a1.2, a2.1, a2.2, k1, k2]

end GlobalTheory.GradedLogDeriv
