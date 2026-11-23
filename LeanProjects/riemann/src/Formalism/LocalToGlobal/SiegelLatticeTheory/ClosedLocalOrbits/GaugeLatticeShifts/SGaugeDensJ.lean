import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SGaugeDensB

open MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace Formalism.MainNotions.S.Gauge

variable {n : ℕ}

section JacInvSec

variable {N : ℕ}

def lmulP (Z : Matrix (Fin n) (Fin n) ℂ) : MP n →L[ℝ] MP n :=
  LinearMap.toContinuousLinearMap
    { toFun := fun X => Matrix.of.symm (Z * Matrix.of X)
      map_add' := fun X Y => by
        funext i j
        simp [Matrix.mul_apply, Finset.sum_add_distrib, mul_add]
      map_smul' := fun c X => by
        funext i j
        simp [Matrix.mul_apply, Finset.smul_sum, mul_left_comm] }

theorem lmulP_apply (Z : Matrix (Fin n) (Fin n) ℂ) (X : MP n) : lmulP Z X = Matrix.of.symm (Z * Matrix.of X) := rfl

theorem of_sum_smul (c : Fin N → ℝ) (X : Fin N → MP n) :
    Matrix.of (∑ k, c k • X k) = ∑ k, c k • Matrix.of (X k) := by
  ext i j
  simp [Matrix.sum_apply, Finset.sum_apply]

theorem sum_single (v : EuclideanSpace ℝ (Fin N)) : v = ∑ k, v k • EuclideanSpace.single k (1 : ℝ) := by
  conv_lhs => rw [← (EuclideanSpace.basisFun (Fin N) ℝ).sum_repr v]
  simp [EuclideanSpace.basisFun_apply]

theorem mul_dPart {Θ : EuclideanSpace ℝ (Fin N) → MP n} {U : Set (EuclideanSpace ℝ (Fin N))}
    {φ : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N)} {Z : Matrix (Fin n) (Fin n) ℂ}
    (hΘ : Differentiable ℝ Θ) (hU : IsOpen U) (hφ : DifferentiableOn ℝ φ U)
    (h : ∀ t ∈ U, Matrix.of (Θ (φ t)) = Z * Matrix.of (Θ t)) {t : EuclideanSpace ℝ (Fin N)} (ht : t ∈ U) (i : Fin N) :
    Z * Matrix.of (dPart Θ t i) =
      ∑ k, (fderiv ℝ φ t (EuclideanSpace.single i 1) k) • Matrix.of (dPart Θ (φ t) k) := by
  have hφt : DifferentiableAt ℝ φ t := hφ.differentiableAt (hU.mem_nhds ht)
  have heq : (Θ ∘ φ) =ᶠ[𝓝 t] (lmulP Z ∘ Θ) := by
    filter_upwards [hU.mem_nhds ht] with s hs
    simp only [Function.comp_apply, lmulP_apply, ← h s hs, Equiv.symm_apply_apply]
  have h1 : fderiv ℝ (Θ ∘ φ) t = (fderiv ℝ Θ (φ t)).comp (fderiv ℝ φ t) := fderiv_comp t (hΘ _) hφt
  have h2 : fderiv ℝ (lmulP Z ∘ Θ) t = (lmulP Z).comp (fderiv ℝ Θ t) := by
    rw [fderiv_comp t (lmulP Z).differentiableAt (hΘ t), ContinuousLinearMap.fderiv]
  have h3 := heq.fderiv_eq (𝕜 := ℝ)
  rw [h1, h2] at h3
  have h4 := congrArg (fun L => L (EuclideanSpace.single i 1)) h3
  simp only [ContinuousLinearMap.comp_apply, lmulP_apply] at h4
  rw [sum_single (fderiv ℝ φ t (EuclideanSpace.single i 1)), map_sum] at h4
  simp only [map_smul] at h4
  have h5 := congrArg Matrix.of h4
  rw [Equiv.apply_symm_apply] at h5
  simp only [dPart]
  exact h5.symm.trans (of_sum_smul _ _)

theorem chartJac_mul_det {Θ : EuclideanSpace ℝ (Fin N) → MP n} {U : Set (EuclideanSpace ℝ (Fin N))}
    {φ : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N)} {Z : Matrix (Fin n) (Fin n) ℂ}
    (hΘ : Differentiable ℝ Θ) (hinv : ∀ s, IsUnit (Matrix.of (Θ s)).det) (hU : IsOpen U) (hφ : DifferentiableOn ℝ φ U)
    (h : ∀ t ∈ U, Matrix.of (Θ (φ t)) = Z * Matrix.of (Θ t)) {t : EuclideanSpace ℝ (Fin N)} (ht : t ∈ U) :
    chartJac Θ (φ t) * |(fderiv ℝ φ t).det| = chartJac Θ t := by
  set D : Matrix (Fin N) (Fin N) ℝ := Matrix.of fun k i => fderiv ℝ φ t (EuclideanSpace.single i 1) k with hDdef
  set M := Matrix.of (Θ t)
  set M' := Matrix.of (Θ (φ t))
  have hM' : M' = Z * M := h t ht
  have hZ : IsUnit Z.det := by
    have := hinv (φ t)
    change IsUnit M'.det at this
    rw [hM', Matrix.det_mul] at this
    exact isUnit_of_mul_isUnit_left this
  have hMinv : M⁻¹ = M'⁻¹ * Z := by
    rw [hM', Matrix.mul_inv_rev, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hZ, Matrix.mul_one]
  set w : EuclideanSpace ℝ (Fin N) → Fin N → EuclideanSpace ℝ (Fin n × Fin n × Bool) :=
    fun s i => realV ((Matrix.of (Θ s))⁻¹ * Matrix.of (dPart Θ s i)) with hwdef
  have hw : ∀ i, w t i = ∑ k, D k i • w (φ t) k := by
    intro i
    have e1 : w t i = realV (M'⁻¹ * (Z * Matrix.of (dPart Θ t i))) := by
      simp only [hwdef]
      change realV (M⁻¹ * _) = _
      rw [hMinv, Matrix.mul_assoc]
    rw [e1, mul_dPart hΘ hU hφ h ht i, Matrix.mul_sum]
    simp only [Matrix.mul_smul]
    change realL n (∑ k, _) = _
    rw [map_sum]
    simp only [map_smul]
    rfl
  have hG : (Matrix.of fun i j : Fin N => @inner ℝ _ _ (w t i) (w t j)) =
      D.transpose * (Matrix.of fun k l : Fin N => @inner ℝ _ _ (w (φ t) k) (w (φ t) l)) * D := by
    ext i j
    rw [Matrix.of_apply, hw i, hw j]
    simp only [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right, Matrix.mul_apply,
      Matrix.transpose_apply, Matrix.of_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    ring
  have hdet : (fderiv ℝ φ t).det = D.det := by
    rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin N) ℝ).toBasis]
    congr 1
  have hJ : chartJac Θ t = Real.sqrt (Matrix.det (Matrix.of fun i j : Fin N => @inner ℝ _ _ (w t i) (w t j))) := rfl
  have hJ' : chartJac Θ (φ t) =
      Real.sqrt (Matrix.det (Matrix.of fun i j : Fin N => @inner ℝ _ _ (w (φ t) i) (w (φ t) j))) := rfl
  rw [hJ, hJ', hG, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hdet,
    show D.det * Matrix.det (Matrix.of fun k l : Fin N => @inner ℝ _ _ (w (φ t) k) (w (φ t) l)) * D.det =
      (D.det * D.det) * Matrix.det (Matrix.of fun k l : Fin N => @inner ℝ _ _ (w (φ t) k) (w (φ t) l)) by ring,
    Real.sqrt_mul (mul_self_nonneg _), Real.sqrt_mul_self_eq_abs, mul_comm]

end JacInvSec

theorem jacInv (ε : Fin n → Bool) : JacInv ε := by
  intro U φ Z hU hφ h t ht
  refine chartJac_mul_det ((contDiff_thetaExp ε).differentiable (by simp)) (fun s => ?_) hU hφ h ht
  rw [of_thetaExp]
  exact (Matrix.isUnit_iff_isUnit_det _).1 (Matrix.isUnit_exp _)

end Formalism.MainNotions.S.Gauge
