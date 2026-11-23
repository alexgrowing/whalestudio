import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.PolynomialGaussianIntegrals.IteratedDerivPolyRealZero
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.PolynomialGaussianIntegrals.IntegrablePolyGauss

noncomputable section

open scoped SchwartzMap InnerProductSpace FourierTransform
open MeasureTheory

namespace PositivityTheory.SiegelWeilFormula.KFPB

variable {ι : Type} [Fintype ι]

def gW (c : ℝ) (h : EuclideanSpace ℝ ι → ℂ) (u : EuclideanSpace ℝ ι) : ℂ := h u * (Real.exp (-(c * ‖u‖ ^ 2)) : ℂ)

theorem gW_cont (c : ℝ) (h : 𝓢(EuclideanSpace ℝ ι, ℂ)) : Continuous (gW c h) := by
  unfold gW
  exact h.continuous.mul (Complex.continuous_ofReal.comp (by fun_prop))

theorem norm_gW_le {c : ℝ} (hc : 0 ≤ c) (h : EuclideanSpace ℝ ι → ℂ) (u : EuclideanSpace ℝ ι) :
    ‖gW c h u‖ ≤ ‖h u‖ := by
  unfold gW
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact mul_le_of_le_one_right (norm_nonneg _)
    (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hc (sq_nonneg _))))

theorem gW_int_pow {c : ℝ} (hc : 0 ≤ c) (h : 𝓢(EuclideanSpace ℝ ι, ℂ)) (n : ℕ) :
    Integrable (fun v => ‖v‖ ^ n * ‖gW c h v‖) := by
  refine (h.integrable_pow_mul volume n).mono
    (((continuous_norm.pow n).mul (gW_cont c h).norm).aestronglyMeasurable) ?_
  refine ae_of_all _ fun v => ?_
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
  exact mul_le_mul_of_nonneg_left (norm_gW_le hc _ v) (by positivity)

theorem gW_int {c : ℝ} (hc : 0 ≤ c) (h : 𝓢(EuclideanSpace ℝ ι, ℂ)) : Integrable (gW c h) := h.integrable.mono (gW_cont c h).aestronglyMeasurable (ae_of_all _ fun v => norm_gW_le hc h v)

theorem four_line (c : ℝ) (h : 𝓢(EuclideanSpace ℝ ι, ℂ)) (ξ : EuclideanSpace ℝ ι) (t : ℝ) :
    𝓕 (gW c h) (t • ξ) = ∫ u, h u * Real.exp (-(c * ‖u‖ ^ 2)) *
      Complex.exp ((-2 * Real.pi * Complex.I * t) * ⟪ξ, u⟫_ℝ) := by
  rw [Real.fourier_eq']
  refine integral_congr_ae (ae_of_all _ fun u => ?_)
  simp only [gW, smul_eq_mul, real_inner_smul_right, real_inner_comm u ξ]
  push_cast
  ring_nf

def Kf (c : ℝ) (h : EuclideanSpace ℝ ι → ℂ) (η : EuclideanSpace ℝ ι) : ℂ :=
  (Real.exp (Real.pi ^ 2 / (2 * c) * ‖η‖ ^ 2) : ℂ) * 𝓕 (gW c h) η

theorem Kf_contDiff {c : ℝ} (hc : 0 ≤ c) (h : 𝓢(EuclideanSpace ℝ ι, ℂ)) (N : ℕ) : ContDiff ℝ N (Kf c h) := by
  unfold Kf
  refine ContDiff.mul ?_ ?_
  · exact Complex.ofRealCLM.contDiff.comp
      (Real.contDiff_exp.comp (contDiff_const.mul (contDiff_norm_sq ℝ)))
  · exact (Real.contDiff_fourier (N := ⊤) (fun n _ => gW_int_pow hc h n)).of_le
      (by exact_mod_cast le_top)

theorem Kf_line {c : ℝ} (hc : 0 < c) (N : ℕ) (h : 𝓢(EuclideanSpace ℝ ι, ℂ))
    (H : ∀ ξ : EuclideanSpace ℝ ι, ∃ p : Polynomial ℂ, p.natDegree ≤ N ∧ ∀ z : ℂ,
      ∫ u, h u * Real.exp (-(c * ‖u‖ ^ 2)) * Complex.exp (z * ⟪ξ, u⟫_ℝ) =
        Complex.exp (z ^ 2 * ‖ξ‖ ^ 2 / (8 * c)) * p.eval z) (ξ : EuclideanSpace ℝ ι) :
    ∃ p : Polynomial ℂ, p.natDegree ≤ N ∧ ∀ t : ℝ, Kf c h (t • ξ) = p.eval (t : ℂ) := by
  obtain ⟨p, hp, hpz⟩ := H ξ
  refine ⟨p.comp (Polynomial.C (-2 * Real.pi * Complex.I) * Polynomial.X), ?_, fun t => ?_⟩
  · calc (p.comp (Polynomial.C (-2 * Real.pi * Complex.I) * Polynomial.X)).natDegree
        ≤ p.natDegree * (Polynomial.C (-2 * Real.pi * Complex.I) * Polynomial.X).natDegree :=
          Polynomial.natDegree_comp_le
      _ ≤ N * 1 := Nat.mul_le_mul hp ((Polynomial.natDegree_C_mul_le _ _).trans Polynomial.natDegree_X_le)
      _ = N := mul_one N
  · have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
    have e : ((Real.pi ^ 2 / (2 * c) * ‖t • ξ‖ ^ 2 : ℝ) : ℂ) +
        (-2 * Real.pi * Complex.I * t) ^ 2 * ‖ξ‖ ^ 2 / (8 * c) = 0 := by
      rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
      push_cast
      field_simp
      ring_nf
      rw [Complex.I_sq]
      ring
    rw [Kf, four_line, hpz, Complex.ofReal_exp, ← mul_assoc, ← Complex.exp_add, e, Complex.exp_zero,
      one_mul, Polynomial.eval_comp]
    simp

theorem four_eq {c : ℝ} (hc : 0 < c) (N : ℕ) (h : 𝓢(EuclideanSpace ℝ ι, ℂ))
    (H : ∀ ξ : EuclideanSpace ℝ ι, ∃ p : Polynomial ℂ, p.natDegree ≤ N ∧ ∀ z : ℂ,
      ∫ u, h u * Real.exp (-(c * ‖u‖ ^ 2)) * Complex.exp (z * ⟪ξ, u⟫_ℝ) =
        Complex.exp (z ^ 2 * ‖ξ‖ ^ 2 / (8 * c)) * p.eval z) :
    ∃ Q : MvPolynomial ι ℂ, Q.totalDegree ≤ N ∧ ∀ η, 𝓕 (gW c h) η =
      MvPolynomial.eval (fun i => ((η i : ℝ) : ℂ)) Q * (Real.exp (-(Real.pi ^ 2 / (2 * c) * ‖η‖ ^ 2)) : ℂ) := by
  obtain ⟨Q, hQ, hKQ⟩ := line_poly N (Kf c h) (Kf_contDiff hc.le h N) (Kf_line hc N h H)
  refine ⟨Q, hQ, fun η => ?_⟩
  rw [← hKQ, Kf, mul_right_comm, ← Complex.ofReal_mul, ← Real.exp_add, add_neg_cancel, Real.exp_zero,
    Complex.ofReal_one, one_mul]

theorem poly_gauss_of_lines (c : ℝ) (hc : 0 < c) (N : ℕ) (h : 𝓢(EuclideanSpace ℝ ι, ℂ))
    (H : ∀ ξ : EuclideanSpace ℝ ι, ∃ p : Polynomial ℂ, p.natDegree ≤ N ∧ ∀ z : ℂ,
      ∫ u, h u * Real.exp (-(c * ‖u‖ ^ 2)) * Complex.exp (z * ⟪ξ, u⟫_ℝ) =
        Complex.exp (z ^ 2 * ‖ξ‖ ^ 2 / (8 * c)) * p.eval z) :
    ∃ P : MvPolynomial ι ℂ, P.totalDegree ≤ N ∧
      ∀ u, h u = MvPolynomial.eval (fun i => ((u i : ℝ) : ℂ)) P * Real.exp (-(c * ‖u‖ ^ 2)) := by
  obtain ⟨Q, hQ, hF⟩ := four_eq hc N h H
  have hb : 0 < Real.pi ^ 2 / (2 * c) := by positivity
  obtain ⟨Q', hQ', hinv⟩ := fourierInv_poly_gauss _ hb Q
  refine ⟨Q', hQ'.trans hQ, fun u => ?_⟩
  have hFeq : 𝓕 (gW c h) = fun η : EuclideanSpace ℝ ι => MvPolynomial.eval (fun i => ((η i : ℝ) : ℂ)) Q *
      (Real.exp (-(Real.pi ^ 2 / (2 * c) * ‖η‖ ^ 2)) : ℂ) := funext hF
  have hint : Integrable (𝓕 (gW c h)) := by
    rw [hFeq]
    exact integrable_poly_gauss _ hb Q
  have key := (gW_int hc.le h).fourierInv_fourier_eq hint (gW_cont c h).continuousAt (v := u)
  rw [hFeq, hinv] at key
  have h2 : Real.pi ^ 2 / (Real.pi ^ 2 / (2 * c)) = 2 * c := by
    have : Real.pi ≠ 0 := Real.pi_ne_zero
    field_simp
  rw [h2] at key
  unfold gW at key
  have hE : (Real.exp (-(c * ‖u‖ ^ 2)) : ℂ) ≠ 0 := by exact_mod_cast (Real.exp_pos _).ne'
  apply mul_right_cancel₀ hE
  rw [← key, mul_assoc _ ((Real.exp (-(c * ‖u‖ ^ 2)) : ℂ)), ← Complex.ofReal_mul, ← Real.exp_add]
  congr 3
  ring

end PositivityTheory.SiegelWeilFormula.KFPB

end
