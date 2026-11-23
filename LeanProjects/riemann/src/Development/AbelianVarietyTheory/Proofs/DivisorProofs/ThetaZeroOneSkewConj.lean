import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgeFrameGram

open Matrix Complex ComplexConjugate GlobalTheory.HermFrame GlobalTheory.IndefiniteRowSideFullHecke.HodgeFrameGram
open scoped ComplexOrder ContDiff

namespace GlobalTheory.HermFrame

theorem thetaZeroOne_eq_neg_conj_thetaOneZero :
    ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
    [FiniteDimensional ℂ E] (ι : Type) [Fintype ι] (n : ℕ) (U : Set (ι → ℂ))
    (H : (ι → ℂ) → Matrix (Fin n) (Fin n) ℂ) (Y : Set E) (π : E → ι → ℂ)
    (A e : E → Matrix (Fin n) (Fin n) ℂ),
    IsPosFrame U H → IsFlagFamily Y U π A → IsUnitaryFlagFrame Y H π A e → ∀ y ∈ Y, ∀ k l η,
      thetaZeroOne e y η k l = -conj (thetaOneZero H π e y η l k) := by
  intro E _ _ _ _ _ ι _ n U H Y π A e hH hA he y hy k l η
  have hY := hA.isOpen.mem_nhds hy
  have hπ : ContDiffAt ℂ ∞ π y := hA.hol_proj.contDiffAt hY
  have hπd : DifferentiableAt ℂ π y := hπ.differentiableAt (by simp)
  have hπr : ContDiffAt ℝ 1 π y := (hπ.restrict_scalars ℝ).of_le (by norm_cast)
  have hH1 : MContDiffAt 1 H (π y) := hH.isHermFrame.one (hA.mapsTo hy)
  have hu : IsUnit (H (π y)).det := hH.isHermFrame.isUnit _ (hA.mapsTo hy)
  have hK : MContDiffAt 1 (fun x => H (π x)) y := fun a b => (hH1 a b).comp y hπr
  have he1 : MContDiffAt 1 e y := fun a b =>
    ((he.smooth a b).contDiffAt hY).of_le (by norm_cast)
  have hone : ∀ x ∈ Y, (e x)ᵀ * H (π x) * (e x)ᴴᵀ = 1 := fun x hx => by
    ext a b
    rw [Matrix.one_apply, ← he.unitary x hx a b, form_eq_sum, Finset.sum_comm]
    simp [mul_apply, Finset.sum_mul]
  have heu : IsUnit (e y).det := by
    have h := congrArg det (hone y hy)
    rw [det_mul, det_mul, det_transpose, det_one, mul_assoc] at h
    exact IsUnit.of_mul_eq_one _ h
  have h := mdel_mul (he1.transpose.mul hK) he1.conjTranspose.transpose η
  rw [mdel_congr (B := fun _ => 1) (Filter.mem_of_superset hY hone), mdel_const,
    mdel_mul he1.transpose hK, mdel_transpose (fun x => (e x)ᴴ), mdel_conjTranspose,
    mdel_transpose, ← conn_transpose_mul (H := fun x => H (π x)) hu,
    conn_comp_holo hH1 hπd] at h
  have hS : mdbar e y η = e y * thetaZeroOne e y η := by
    rw [thetaZeroOne, mul_nonsing_inv_cancel_left _ _ heu]
  have hT : mdel e y η =
      e y * thetaOneZero H π e y η - conn H (π y) (fderiv ℂ π y η) * e y := by
    rw [thetaOneZero, mul_nonsing_inv_cancel_left _ _ heu, add_sub_cancel_right]
  have h2 : (thetaZeroOne e y η)ᴴᵀ + (thetaOneZero H π e y η)ᵀ = 0 := by
    have h3 : (e y)ᵀ * H (π y) * (e y)ᴴᵀ * (thetaZeroOne e y η)ᴴᵀ +
        (thetaOneZero H π e y η)ᵀ * ((e y)ᵀ * H (π y) * (e y)ᴴᵀ) = 0 := by
      rw [h, hS, hT]
      simp only [conjTranspose_mul, transpose_mul, transpose_sub]
      noncomm_ring
    rwa [hone y hy, Matrix.one_mul, Matrix.mul_one] at h3
  have h4 := congrArg conj (congrFun (congrFun h2 k) l)
  simp only [Matrix.add_apply, transpose_apply, conjTranspose_apply, Matrix.zero_apply, map_add,
    map_zero, star_def, conj_conj] at h4
  exact eq_neg_of_add_eq_zero_left h4

end GlobalTheory.HermFrame
