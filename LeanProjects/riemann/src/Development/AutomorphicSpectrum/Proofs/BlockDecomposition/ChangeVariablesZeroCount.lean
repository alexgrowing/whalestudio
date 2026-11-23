import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JoinCol
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IntegrableMonomialMulConjComplexGaussian
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PAreaMultiplicityWeight
open MeasureTheory ReciprocityTheory.L2DbarEstimates GlobalTheory.CompanionTheory.FSCrofton
open scoped ENNReal ComplexConjugate

noncomputable section

namespace GlobalTheory.CompanionTheory.FSCrofton

theorem clm_apply_eq_sum {d : ℕ} (T : V d →L[ℂ] ℂ) (v : V d) :
    T v = ∑ a, v a * T (EuclideanSpace.single a 1) := by
  conv_lhs => rw [← (EuclideanSpace.basisFun (Fin d) ℂ).sum_repr v]
  simp [map_sum]

theorem abs_det_restrictScalars_toEuclideanCLM {d : ℕ} (M : Matrix (Fin d) (Fin d) ℂ) :
    |((Matrix.toEuclideanCLM (𝕜 := ℂ) M : V d →L[ℂ] V d).restrictScalars ℝ).det| =
      ‖M.det‖ ^ 2 := by
  have h1 : ((Matrix.toEuclideanCLM (𝕜 := ℂ) M : V d →L[ℂ] V d).restrictScalars ℝ).det =
      Algebra.norm ℝ (LinearMap.det (Matrix.toEuclideanLin M : V d →ₗ[ℂ] V d)) := by
    rw [← LinearMap.det_restrictScalars]
    rfl
  rw [h1, Matrix.toEuclideanLin_eq_toLin, LinearMap.det_toLin, Algebra.norm_complex_eq]
  simp [Complex.normSq_eq_norm_sq]

theorem area_formula_neg_comb (d : ℕ) (β : Type) [Fintype β] (U A : Set (V d)) (f : β → V d → ℂ)
    (C : Fin d → β → ℂ) (h : (Fin d → ℂ) → ℝ≥0∞) (hU : IsOpen U)
    (hf : ∀ j, DifferentiableOn ℂ (f j) U) (hAU : A ⊆ U) (hA : MeasurableSet A)
    (hh : Measurable h) :
    ∫⁻ c : Fin d → ℂ, h c * (({z ∈ A | ∀ k, c k + ∑ j, C k j * f j z = 0}.encard : ℕ∞) : ℝ≥0∞) =
      ∫⁻ z in A, h (fun k => -∑ j, C k j * f j z) *
        ENNReal.ofReal (‖(Matrix.of C * (Matrix.of fun j a =>
          fderiv ℂ (f j) z (EuclideanSpace.single a 1) : Matrix β (Fin d) ℂ)).det‖ ^ 2) := by
  classical
  let F : V d → Matrix β (Fin d) ℂ := fun z =>
    Matrix.of fun j a => fderiv ℂ (f j) z (EuclideanSpace.single a 1)
  let M : V d → Matrix (Fin d) (Fin d) ℂ := fun z => -(Matrix.of C * F z)
  let g : V d → V d := fun z => WithLp.toLp 2 (fun k => -∑ j, C k j * f j z)
  let L : V d → V d →L[ℂ] V d := fun z => Matrix.toEuclideanCLM (𝕜 := ℂ) (M z)
  let f' : V d → V d →L[ℝ] V d := fun z => (L z).restrictScalars ℝ
  have hderC : ∀ z ∈ A, HasFDerivWithinAt g (L z) A z := by
    intro z hz
    rw [hasFDerivWithinAt_euclidean]
    intro k
    have hj : ∀ j, HasFDerivAt (f j) (fderiv ℂ (f j) z) z := fun j =>
      ((hf j).differentiableAt (hU.mem_nhds (hAU hz))).hasFDerivAt
    have hs : HasFDerivAt (fun w => -∑ j, C k j * f j w)
        (-∑ j, C k j • fderiv ℂ (f j) z) z :=
      (HasFDerivAt.fun_sum fun j _ => (hj j).const_mul (C k j)).neg
    have he : PiLp.proj 2 (fun _ : Fin d => ℂ) k ∘L L z = -∑ j, C k j • fderiv ℂ (f j) z := by
      ext v
      have hv : ∀ j, fderiv ℂ (f j) z v = ∑ a, v a * F z j a := fun j => clm_apply_eq_sum _ v
      change ((Matrix.toEuclideanCLM (𝕜 := ℂ) (M z)) v).ofLp k = _
      rw [Matrix.ofLp_toEuclideanCLM]
      simp only [ContinuousLinearMap.neg_apply, ContinuousLinearMap.sum_apply,
        ContinuousLinearMap.smul_apply, smul_eq_mul, hv]
      simp only [M, Matrix.mulVec, dotProduct, Matrix.neg_apply, Matrix.mul_apply, Matrix.of_apply,
        neg_mul, Finset.sum_neg_distrib, neg_inj]
      simp_rw [Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    rw [he]
    exact hs.hasFDerivWithinAt
  have hder : ∀ z ∈ A, HasFDerivWithinAt g (f' z) A z := fun z hz =>
    (hderC z hz).restrictScalars ℝ
  have hdet : ∀ z, |(f' z).det| = ‖(Matrix.of C * F z).det‖ ^ 2 := by
    intro z
    have := abs_det_restrictScalars_toEuclideanCLM (M z)
    rw [show (M z).det = (-1) ^ Fintype.card (Fin d) * (Matrix.of C * F z).det from
      Matrix.det_neg _] at this
    simpa using this
  have hp : MeasurePreserving (MeasurableEquiv.toLp 2 (Fin d → ℂ))
      (volume : Measure (Fin d → ℂ)) (volume : Measure (V d)) :=
    MeasurePreserving.symm (MeasurableEquiv.toLp 2 (Fin d → ℂ)).symm
      (GlobalTheory.volume_preserving_ofLp_complex (Fin d))
  have hw := (GroundTheory.Heights₂.Heights.AreaMultiplicityWeight.proof (V d) volume A g f' hA hder).2
    (fun y => h y.ofLp) (hh.comp (MeasurableEquiv.toLp 2 (Fin d → ℂ)).symm.measurable)
  have hfib : ∀ c : Fin d → ℂ, {z ∈ A | ∀ k, c k + ∑ j, C k j * f j z = 0} =
      {z ∈ A | g z = WithLp.toLp 2 c} := by
    intro c
    ext z
    simp only [Set.mem_setOf_eq, g]
    refine and_congr_right fun _ => ?_
    rw [(WithLp.toLp_injective 2).eq_iff, funext_iff]
    refine forall_congr' fun k => ?_
    rw [neg_eq_iff_add_eq_zero, add_comm]
  calc ∫⁻ c : Fin d → ℂ, h c * (({z ∈ A | ∀ k, c k + ∑ j, C k j * f j z = 0}.encard : ℕ∞) : ℝ≥0∞)
      = ∫⁻ c : Fin d → ℂ, (fun y : V d => (({z ∈ A | g z = y}.encard : ℕ∞) : ℝ≥0∞) * h y.ofLp)
          (MeasurableEquiv.toLp 2 (Fin d → ℂ) c) := by
        refine lintegral_congr fun c => ?_
        rw [hfib c, mul_comm]
        rfl
    _ = ∫⁻ y : V d, (({z ∈ A | g z = y}.encard : ℕ∞) : ℝ≥0∞) * h y.ofLp :=
        hp.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _)
          (fun y : V d => (({z ∈ A | g z = y}.encard : ℕ∞) : ℝ≥0∞) * h y.ofLp)
    _ = ∫⁻ z in A, h (g z).ofLp * ENNReal.ofReal |(f' z).det| := hw.symm
    _ = _ := by
        refine lintegral_congr fun z => ?_
        rw [hdet z]

end GlobalTheory.CompanionTheory.FSCrofton
