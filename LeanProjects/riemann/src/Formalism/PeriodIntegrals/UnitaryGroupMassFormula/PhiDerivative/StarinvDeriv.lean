import Mathlib
import Formalism.PeriodIntegrals.LongWeylElementSquare

noncomputable section

open Matrix

namespace PI.SwBig.PhiDerivW

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace
  Matrix.frobeniusNormedRing Matrix.frobeniusNormedAlgebra

theorem starinv_deriv :
    HasStrictFDerivAt (fun z : ℂ => (star (1 + z))⁻¹) (-(Complex.conjCLE : ℂ →L[ℝ] ℂ)) 0 := by
  have h1 : HasStrictFDerivAt (fun z : ℂ => 1 + (Complex.conjCLE : ℂ →L[ℝ] ℂ) z)
      (Complex.conjCLE : ℂ →L[ℝ] ℂ) 0 :=
    (Complex.conjCLE : ℂ →L[ℝ] ℂ).hasStrictFDerivAt.const_add 1
  have h2 : ∀ y : ℂ, y = 1 → HasStrictFDerivAt (fun w : ℂ => w⁻¹)
      ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (-((1 : ℂ) ^ 2)⁻¹)).restrictScalars ℝ) y := by
    rintro y rfl
    exact (hasStrictDerivAt_inv (𝕜 := ℂ) (x := 1) one_ne_zero).hasStrictFDerivAt.restrictScalars ℝ
  have h3 := (h2 _ (by simp)).comp 0 h1
  have hf : (fun z : ℂ => (star (1 + z))⁻¹) = (fun w : ℂ => w⁻¹) ∘
      (fun z : ℂ => 1 + (Complex.conjCLE : ℂ →L[ℝ] ℂ) z) := by
    funext z; simp [star_add]
  rw [hf]
  refine h3.congr_fderiv ?_
  refine ContinuousLinearMap.ext fun z => ?_
  simp

variable (k r : ℕ)

def dvC : (Fin r → ℂ) →L[ℝ] (Fin (2 * r + k + 1) → ℂ) :=
  ContinuousLinearMap.pi fun i =>
    if h : i.val < r then ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin r => ℂ) ⟨i.val, h⟩
    else if h2 : i.val ≤ r + k then 0
    else -((Complex.conjCLE : ℂ →L[ℝ] ℂ).comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin r => ℂ)
        ⟨2 * r + k - i.val, by have := i.isLt; omega⟩))

theorem dvC_apply (x : Fin r → ℂ) : dvC k r x = dv k r x := by
  funext i
  unfold dvC dv
  simp only [ContinuousLinearMap.pi_apply]
  split_ifs <;> simp

theorem tv_deriv : HasStrictFDerivAt (fun x : Fin r → ℂ => tv k r (1 + x)) (dvC k r) 0 := by
  rw [hasStrictFDerivAt_pi']
  intro i
  unfold dvC
  rw [ContinuousLinearMap.proj_pi]
  unfold tv
  by_cases h : i.val < r
  · simp only [h, ↓reduceDIte, Pi.add_apply, Pi.one_apply]
    exact (hasStrictFDerivAt_apply (𝕜 := ℝ) (i := (⟨i.val, h⟩ : Fin r)) (f := (0 : Fin r → ℂ))).const_add 1
  · by_cases h2 : i.val ≤ r + k
    · simp only [h, h2, ↓reduceDIte]
      exact hasStrictFDerivAt_const _ _
    · simp only [h, h2, ↓reduceDIte, Pi.add_apply, Pi.one_apply]
      have ha := hasStrictFDerivAt_apply (𝕜 := ℝ)
        (i := (⟨2 * r + k - i.val, by have := i.isLt; omega⟩ : Fin r)) (f := (0 : Fin r → ℂ))
      have hs : ∀ y : ℂ, y = 0 → HasStrictFDerivAt (fun z : ℂ => (star (1 + z))⁻¹)
          (-(Complex.conjCLE : ℂ →L[ℝ] ℂ)) y := by
        rintro y rfl; exact starinv_deriv
      refine ((hs _ (by simp)).comp 0 ha).congr_fderiv ?_
      refine ContinuousLinearMap.ext fun z => ?_
      simp

def diagC : (Fin (2 * r + k + 1) → ℂ) →L[ℝ] Mat k r :=
  LinearMap.toContinuousLinearMap (Matrix.diagonalLinearMap (Fin (2 * r + k + 1)) ℝ ℂ)

theorem diagC_apply (v : Fin (2 * r + k + 1) → ℂ) : diagC k r v = Matrix.diagonal v := by
  simp [diagC]

theorem tv_one : tv k r 1 = 1 := by
  funext i
  unfold tv
  split_ifs <;> simp

theorem diag1 : Matrix.diagonal (1 : Fin (2 * r + k + 1) → ℂ) = 1 := Matrix.diagonal_one

theorem main (hW : LongWeylElementSquare) :
    HasStrictFDerivAt
      (fun p : Mat k r × (Fin r → ℂ) × Mat k r × Mat k r => Phi k r p.1 p.2.1 p.2.2.1 p.2.2.2)
      (Lm k r) 0 := by
  have e0 : ∀ y : Mat k r, y = 0 →
      HasStrictFDerivAt (NormedSpace.exp : Mat k r → Mat k r) (1 : Mat k r →L[ℝ] Mat k r) y := by
    rintro y rfl; exact hasStrictFDerivAt_exp_zero
  have c0 : ∀ (f : Mat k r × (Fin r → ℂ) × Mat k r × Mat k r → Mat k r) f',
      HasStrictFDerivAt f f' 0 → f 0 = 0 →
      HasStrictFDerivAt (fun p => NormedSpace.exp (f p)) ((1 : Mat k r →L[ℝ] Mat k r).comp f') 0 :=
    fun f f' hf h0 => (e0 _ h0).comp 0 hf
  have hX := c0 _ _ (hasStrictFDerivAt_fst (𝕜 := ℝ)
    (p := (0 : Mat k r × (Fin r → ℂ) × Mat k r × Mat k r))) (by simp)
  have hZ := c0 _ _ (hasStrictFDerivAt_snd (𝕜 := ℝ)
    (p := (0 : Mat k r × (Fin r → ℂ) × Mat k r × Mat k r))).snd.fst (by simp)
  have hX' := c0 _ _ (hasStrictFDerivAt_snd (𝕜 := ℝ)
    (p := (0 : Mat k r × (Fin r → ℂ) × Mat k r × Mat k r))).snd.snd.neg (by simp)
  have hT := (diagC k r).hasStrictFDerivAt.comp 0 ((tv_deriv k r).comp 0
    (hasStrictFDerivAt_snd (𝕜 := ℝ) (p := (0 : Mat k r × (Fin r → ℂ) × Mat k r × Mat k r))).fst)
  have h1 := (hX.const_mul (w0B k r)).mul_const' (w0B k r)
  have h5 := ((h1.mul' hT).mul' hZ).mul' hX'
  apply h5.congr_fderiv
  refine ContinuousLinearMap.ext fun p => ?_
  simp only [Pi.mul_apply, Prod.fst_zero, Prod.snd_zero, NormedSpace.exp_zero, mul_one, hW k r,
    add_zero, neg_zero, Pi.neg_apply, diagC_apply, tv_one]
  change (1 * diagonal 1) * (-p.2.2.2) + ((1 * diagonal 1) * p.2.2.1 +
      (1 * diagC k r (dvC k r p.2.1) + w0B k r * p.1 * w0B k r * diagonal 1) * 1) * 1 =
    w0B k r * p.1 * w0B k r + diagonal (dv k r p.2.1) + p.2.2.1 - p.2.2.2
  rw [diagC_apply, dvC_apply, diag1]
  simp only [one_mul, mul_one]
  abel

end PI.SwBig.PhiDerivW
