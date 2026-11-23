import ReciprocityTheory.L2DbarEstimates.LeviForms.BergmanExistsStatement
import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.MeasurableSetImageOfIsLocalHomeomorph

namespace ReciprocityTheory.L2DbarEstimates.I

open MeasureTheory Metric Filter Topology Set
open scoped ENNReal ContDiff

noncomputable section

def shG {M : Type*} (n : ℕ) (g : Fin n → M → ℂ) (s : V n → M) (y : V n) : V n :=
  WithLp.toLp 2 (fun i => g i (s y))

theorem shG_apply {M : Type*} (n : ℕ) (g : Fin n → M → ℂ) (s : V n → M) (y : V n) (i : Fin n) :
    shG n g s y i = g i (s y) := rfl

theorem shG_norm_sq {M : Type*} (n : ℕ) (g : Fin n → M → ℂ) (s : V n → M) (y : V n) :
    ‖shG n g s y‖ ^ 2 = ∑ i, ‖g i (s y)‖ ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  rfl

theorem shG_contDiffOn {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (g : Fin n → M → ℂ) (hg : ∀ i, Holo n z (g i)) (e : OpenPartialHomeomorph M (V n))
    (he : IsChart n z e) : ContDiffOn ℂ ∞ (shG n g e.symm) e.target := by
  rw [contDiffOn_euclidean]
  intro i
  exact contDiffOn_of_differentiableOn n _ _ e.open_target (hg i e he)

theorem sh_wd_eq (n : ℕ) (j : Fin n) (f : V n → ℂ) (y : V n) (hf : DifferentiableAt ℂ f y) :
    wd n j f y = fderiv ℂ f y (bas n j) := by
  have h := (hf.hasFDerivAt.restrictScalars ℝ).fderiv
  rw [wd, h]
  simp only [ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.map_smul, smul_eq_mul]
  ring_nf
  rw [Complex.I_sq]
  ring

theorem sh_jac {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (g : Fin n → M → ℂ) (hg : ∀ i, Holo n z (g i)) (e : OpenPartialHomeomorph M (V n))
    (he : IsChart n z e) (y : V n) (hy : y ∈ e.target) :
    jac n z g (e.symm y) = LinearMap.det (fderiv ℂ (shG n g e.symm) y : V n →ₗ[ℂ] V n) := by
  have hd : DifferentiableAt ℂ (shG n g e.symm) y :=
    ((shG_contDiffOn n z g hg e he).contDiffAt (e.open_target.mem_nhds hy)).differentiableAt
      (by simp)
  rw [← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin n) ℂ).toBasis]
  unfold jac
  congr 1
  ext i k
  rw [Matrix.of_apply, d_comp_symm n z e he k (g i) y hy, LinearMap.toMatrix_apply]
  have hdi : DifferentiableAt ℂ (g i ∘ e.symm) y :=
    (hg i e he).differentiableAt (e.open_target.mem_nhds hy)
  rw [sh_wd_eq n k _ y hdi]
  have hcomp : HasFDerivAt (g i ∘ e.symm)
      ((EuclideanSpace.proj i : V n →L[ℂ] ℂ).comp (fderiv ℂ (shG n g e.symm) y)) y :=
    (EuclideanSpace.proj i : V n →L[ℂ] ℂ).hasFDerivAt.comp y hd.hasFDerivAt
  rw [hcomp.fderiv]
  simp [bas]

theorem sh_local {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (g : Fin n → M → ℂ) (hg : ∀ i, Holo n z (g i)) (p : M) (hp : p ∈ zeroSet n g)
    (hJ : jac n z g p ≠ 0) (e : OpenPartialHomeomorph M (V n)) (he : IsChart n z e)
    (hpe : p ∈ e.source) :
    ∃ ρ > 0, ball (e p) ρ ⊆ e.target ∧ InjOn (shG n g e.symm) (ball (e p) ρ) ∧
      ∀ ρ' > 0, ∃ κ > 0, ∀ y ∈ ball (e p) ρ, ‖shG n g e.symm y‖ < κ → y ∈ ball (e p) ρ' := by
  have hy0 : e p ∈ e.target := e.map_source hpe
  have hcd : ContDiffAt ℂ ∞ (shG n g e.symm) (e p) :=
    (shG_contDiffOn n z g hg e he).contDiffAt (e.open_target.mem_nhds hy0)
  have hdet : (fderiv ℂ (shG n g e.symm) (e p)).det ≠ 0 := by
    have h := sh_jac n z g hg e he (e p) hy0
    rw [e.left_inv hpe] at h
    rw [ContinuousLinearMap.det, ← h]
    exact hJ
  set f' := (fderiv ℂ (shG n g e.symm) (e p)).toContinuousLinearEquivOfDetNeZero hdet
  have hf' : HasFDerivAt (shG n g e.symm) (f' : V n →L[ℂ] V n) (e p) := by
    rw [ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero]
    exact (hcd.differentiableAt (by simp)).hasFDerivAt
  have hn0 : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  set Φ := hcd.toOpenPartialHomeomorph (shG n g e.symm) hf' hn0
  have hΦ : (Φ : V n → V n) = shG n g e.symm := rfl
  have hsrc : e p ∈ Φ.source := hcd.mem_toOpenPartialHomeomorph_source hf' hn0
  have htgt : shG n g e.symm (e p) ∈ Φ.target :=
    hcd.image_mem_toOpenPartialHomeomorph_target hf' hn0
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 (e.open_target.inter Φ.open_source) (e p)
    ⟨hy0, hsrc⟩
  refine ⟨ρ, hρ, fun y hy => (hball hy).1, ?_, ?_⟩
  · rw [← hΦ]
    exact Φ.injOn.mono fun y hy => (hball hy).2
  intro ρ' hρ'
  have hG0 : shG n g e.symm (e p) = 0 := by
    ext i
    rw [shG_apply, e.left_inv hpe]
    exact hp i
  have hsymm : Φ.symm (shG n g e.symm (e p)) = e p := by
    rw [← hΦ]
    exact Φ.left_inv hsrc
  have hc : ContinuousAt Φ.symm (shG n g e.symm (e p)) := Φ.continuousAt_symm htgt
  have hmem : Φ.symm ⁻¹' ball (e p) ρ' ∈ 𝓝 (shG n g e.symm (e p)) :=
    hc.preimage_mem_nhds (by rw [hsymm]; exact ball_mem_nhds _ hρ')
  obtain ⟨κ, hκ, hκb⟩ := Metric.mem_nhds_iff.1 hmem
  refine ⟨κ, hκ, fun y hy hGy => ?_⟩
  have h1 : shG n g e.symm y ∈ ball (shG n g e.symm (e p)) κ := by
    rw [hG0, mem_ball_zero_iff]
    exact hGy
  have h2 := hκb h1
  simp only [mem_preimage] at h2
  rwa [← hΦ, Φ.left_inv (hball hy).2] at h2

theorem sh_num (τ : ℝ) (hτ : 0 < τ) :
    Real.exp (min (τ / 10) (1 / 4)) * (Real.log 2 + 2 * min (τ / 10) (1 / 4)) ≤
      (1 + τ) * Real.log 2 := by
  set θ := min (τ / 10) (1 / 4) with hθ
  have h0 : 0 < θ := lt_min (by positivity) (by norm_num)
  have h1 : θ ≤ τ / 10 := min_le_left _ _
  have h2 : θ ≤ 1 / 4 := min_le_right _ _
  have hexp : Real.exp θ ≤ 1 + 2 * θ := by
    have := Real.exp_bound_div_one_sub_of_interval' h0 (by linarith)
    have h3 : 1 / (1 - θ) ≤ 1 + 2 * θ := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith
    linarith
  have hl1 := Real.log_two_gt_d9
  have hl2 := Real.log_two_lt_d9
  have hpos : 0 ≤ Real.log 2 + 2 * θ := by linarith
  calc Real.exp θ * (Real.log 2 + 2 * θ) ≤ (1 + 2 * θ) * (Real.log 2 + 2 * θ) :=
        mul_le_mul_of_nonneg_right hexp hpos
    _ ≤ (1 + τ) * Real.log 2 := by nlinarith

theorem sh_val (n j : ℕ) (S r a b : ℝ) (hS : 0 < S) (hr : 0 < r) :
    Real.exp (-b - ((n : ℝ) + j) * a) * (S * Real.exp (-a) / r ^ 2) ^ (-(n : ℝ)) =
      r ^ (2 * n) * Real.exp (-b - (j : ℝ) * a) * S ^ (-(n : ℝ)) := by
  have hX : 0 < Real.exp (-a) / r ^ 2 := by positivity
  rw [mul_div_assoc, Real.mul_rpow hS.le hX.le, Real.rpow_neg hX.le, Real.rpow_natCast,
    div_pow, ← Real.exp_nat_mul, pow_mul]
  have hE : Real.exp (-b - ((n : ℝ) + j) * a) =
      Real.exp (-b - (j : ℝ) * a) * Real.exp (↑n * -a) := by
    rw [← Real.exp_add]
    ring_nf
  rw [hE]
  have h1 : 0 < Real.exp (↑n * -a) := Real.exp_pos _
  have h2 : 0 < (r ^ 2) ^ n := by positivity
  field_simp

end

end ReciprocityTheory.L2DbarEstimates.I
