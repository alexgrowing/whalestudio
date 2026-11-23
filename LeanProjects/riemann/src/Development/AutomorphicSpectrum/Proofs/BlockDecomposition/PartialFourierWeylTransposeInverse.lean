import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Lpart
import GroundTheory.HeightsAndTheta.Theta.WeilNonarchProps
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData GlobalTheory.CompanionTheory.GL2DualWhittakerPair
open scoped ValuativeRel

namespace GlobalTheory.CompanionTheory.GL2DualWhittakerPair.Jac

open scoped NNReal

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

theorem det_ne (h : GL (Fin 2) F) : (h.val).det ≠ 0 :=
  ((Matrix.isUnit_iff_isUnit_det _).1 h.isUnit).ne_zero

def kr (a b : Matrix (Fin 2) (Fin 2) F) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) F :=
  Matrix.kroneckerMap (· * ·) a bᵀ

theorem toM_kr (a b : Matrix (Fin 2) (Fin 2) F) (X : Fin 2 × Fin 2 → F) :
    toM (kr a b *ᵥ X) = a * toM X * b := by
  ext i j
  simp only [toM, kr, Matrix.of_apply, Matrix.mulVec, dotProduct, Matrix.mul_apply,
    Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.kroneckerMap_apply, Matrix.transpose_apply]
  ring

theorem det_kr (a b : Matrix (Fin 2) (Fin 2) F) : (kr a b).det = a.det ^ 2 * b.det ^ 2 := by
  have := Matrix.det_kronecker a bᵀ
  simpa [kr, Matrix.kronecker, Matrix.det_transpose] using this

theorem pair_eq (N A : Matrix (Fin 2) (Fin 2) F) :
    ∑ i, ∑ j, N i j * A i j = Matrix.trace (N * Aᵀ) := by
  simp [Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two]

theorem c_val : (dg2 (-1) (-1) : GL (Fin 2) F).val = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dg2]

theorem c_inv : (dg2 (-1) (-1) : GL (Fin 2) F)⁻¹ = dg2 (-1) (-1) := by
  apply inv_eq_of_mul_eq_one_left
  apply Units.ext
  rw [Units.val_mul, c_val]
  simp

theorem first_val (h z : GL (Fin 2) F) :
    (tinv (dg2 (-1) (-1) * z)⁻¹ * w2 * h).val = -(z.valᵀ * w2.val * h.val) := by
  have : (tinv (dg2 (-1) (-1) * z)⁻¹ : GL (Fin 2) F).val = -z.valᵀ := by
    show (((dg2 (-1) (-1) * z)⁻¹)⁻¹ : GL (Fin 2) F).valᵀ = _
    rw [inv_inv, Units.val_mul, c_val]
    simp
  rw [Units.val_mul, Units.val_mul, this]
  simp

theorem second_val (z : GL (Fin 2) F) :
    ((dg2 (-1) (-1) * z)⁻¹ : GL (Fin 2) F).val = -(z⁻¹ : GL (Fin 2) F).val := by
  rw [_root_.mul_inv_rev, c_inv, Units.val_mul, c_val]
  simp

theorem tinv_mul_transpose (h : GL (Fin 2) F) : (tinv h).val * h.valᵀ = 1 := by
  show (h⁻¹ : GL (Fin 2) F).valᵀ * h.valᵀ = 1
  rw [← Matrix.transpose_mul, ← Units.val_mul, mul_inv_cancel]
  simp

theorem pair_sub (h z : GL (Fin 2) F) (M : Matrix (Fin 2) (Fin 2) F) :
    Matrix.trace (((z⁻¹ : GL (Fin 2) F).val * M * (tinv h).val) * (-(z.valᵀ * w2.val * h.val))ᵀ)
      = -(M 0 1 + M 1 0) := by
  have e : ((z⁻¹ : GL (Fin 2) F).val * M * (tinv h).val) * (-(z.valᵀ * w2.val * h.val))ᵀ
      = -((z⁻¹ : GL (Fin 2) F).val * (M * w2.val * z.val)) := by
    have : (z.valᵀ * w2.val * h.val)ᵀ = h.valᵀ * (w2.valᵀ * z.val) := by
      simp [Matrix.transpose_mul, Matrix.mul_assoc]
    rw [Matrix.transpose_neg, this, Matrix.mul_neg]
    congr 1
    have w2t : (w2 : GL (Fin 2) F).valᵀ = w2.val := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [w2]
    rw [w2t]
    calc _ = (z⁻¹ : GL (Fin 2) F).val * M * ((tinv h).val * h.valᵀ) * (w2.val * z.val) := by
            simp only [Matrix.mul_assoc]
      _ = _ := by rw [tinv_mul_transpose]; simp only [Matrix.mul_assoc, Matrix.mul_one]
  rw [e, Matrix.trace_neg, Matrix.trace_mul_comm, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel]
  simp [Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two, w2]

theorem modulus_inv_det (z : GL (Fin 2) F) :
    modulus ((z⁻¹ : GL (Fin 2) F).val).det = (modulus (z.val).det)⁻¹ := by
  have h : ((z⁻¹ : GL (Fin 2) F).val).det = ((z.val).det)⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel]
    simp
  rw [h, modulus_inv]

theorem modulus_tinv_det (h : GL (Fin 2) F) :
    modulus ((tinv h).val).det = (modulus (h.val).det)⁻¹ := by
  show modulus ((h⁻¹ : GL (Fin 2) F).valᵀ).det = _
  rw [Matrix.det_transpose, modulus_inv_det]

theorem mp_neg_two (g : GL (Fin 2) F) :
    mp (GeneralLinearGroup.det g) (-2) = ((((modulus (g.val).det)⁻¹ ^ 2 : ℝ≥0) : ℝ) : ℂ) := by
  have : ((GeneralLinearGroup.det g : Fˣ) : F) = (g.val).det := by
    simp only [GeneralLinearGroup.val_det_apply]
  unfold mp
  rw [this, Complex.cpow_neg, Complex.cpow_ofNat]
  push_cast
  rw [inv_pow]

noncomputable def gI (ψ : AddChar F Circle) (Φ : Matrix (Fin 2) (Fin 3) F → ℂ) (Y : Matrix (Fin 2) (Fin 2) F)
    (y : Fin 2 → F) (N : Fin 2 × Fin 2 → F) : ℂ :=
  Φ (cat3 (toM N) y) * (ψ (∑ i, ∑ j, N (i, j) * Y i j) : ℂ)

theorem dFT_eq (ψ : AddChar F Circle) (Φ : Matrix (Fin 2) (Fin 3) F → ℂ) (h z : GL (Fin 2) F) :
    dFT ψ Φ (tinv (dg2 (-1) (-1) * z)⁻¹ * w2 * h).val
        (((dg2 (-1) (-1) * z)⁻¹ : GL (Fin 2) F).val *ᵥ e1) =
      ∫ N, gI ψ Φ (-(z.valᵀ * w2.val * h.val)) ((z⁻¹ : GL (Fin 2) F).val *ᵥ e1) N
        ∂GroundTheory.Heights₂.Theta.selfDualPi (Fin 2 × Fin 2) ψ := by
  rw [first_val, second_val, Matrix.neg_mulVec]
  unfold dFT
  simp only [neg_neg]
  rfl

theorem Rpart_eq (ψ : AddChar F Circle) (Φ : Matrix (Fin 2) (Fin 3) F → ℂ) (h z : GL (Fin 2) F) :
    Rpart ψ (Pf Φ h z) =
      ∫ X, gI ψ Φ (-(z.valᵀ * w2.val * h.val)) ((z⁻¹ : GL (Fin 2) F).val *ᵥ e1)
          (kr (z⁻¹ : GL (Fin 2) F).val (tinv h).val *ᵥ X)
        ∂GroundTheory.Heights₂.Theta.selfDualPi (Fin 2 × Fin 2) ψ := by
  unfold Rpart
  refine integral_congr_ae (Filter.Eventually.of_forall fun X => ?_)
  have hM := toM_kr (z⁻¹ : GL (Fin 2) F).val (tinv h).val X
  have hp : ∑ i, ∑ j, (kr (z⁻¹ : GL (Fin 2) F).val (tinv h).val *ᵥ X) (i, j) *
        (-(z.valᵀ * w2.val * h.val) : Matrix (Fin 2) (Fin 2) F) i j = -(X (0, 1) + X (1, 0)) := by
    have h1 : ∑ i, ∑ j, toM (kr (z⁻¹ : GL (Fin 2) F).val (tinv h).val *ᵥ X) i j *
        (-(z.valᵀ * w2.val * h.val) : Matrix (Fin 2) (Fin 2) F) i j = -(X (0, 1) + X (1, 0)) := by
      rw [pair_eq, hM, pair_sub]
      rfl
    exact h1
  simp only [gI, Pf, hM, hp]

theorem main : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (ψ : AddChar F Circle),
    IsStd ψ → ∀ (Φ : Matrix (Fin 2) (Fin 3) F → ℂ) (h z : GL (Fin 2) F),
    dFT ψ Φ (tinv (dg2 (-1) (-1) * z)⁻¹ * w2 * h).val
        (((dg2 (-1) (-1) * z)⁻¹ : GL (Fin 2) F).val *ᵥ e1) =
      mp (GeneralLinearGroup.det z) (-2) * mp (GeneralLinearGroup.det h) (-2) *
        Rpart ψ (Pf Φ h z) := by
  intro F _ _ _ _ _ _ ψ _ Φ h z
  have hP : (kr (z⁻¹ : GL (Fin 2) F).val (tinv h).val).det ≠ 0 := by
    rw [det_kr]
    exact mul_ne_zero (pow_ne_zero _ (det_ne _)) (pow_ne_zero _ (det_ne _))
  have key := GroundTheory.Heights₂.Theta.integral_comp_mulVec (ψ := ψ) hP
    (gI ψ Φ (-(z.valᵀ * w2.val * h.val)) ((z⁻¹ : GL (Fin 2) F).val *ᵥ e1))
  have hm : modulus (kr (z⁻¹ : GL (Fin 2) F).val (tinv h).val).det =
      (modulus (z.val).det)⁻¹ ^ 2 * (modulus (h.val).det)⁻¹ ^ 2 := by
    rw [det_kr, modulus_mul, pow_two, pow_two, modulus_mul, modulus_mul, modulus_inv_det,
      modulus_tinv_det, pow_two, pow_two]
  rw [dFT_eq, Rpart_eq, key, mp_neg_two, mp_neg_two, ← mul_assoc]
  have hc : (((((modulus (z.val).det)⁻¹ ^ 2 : ℝ≥0) : ℝ) : ℂ) *
      ((((modulus (h.val).det)⁻¹ ^ 2 : ℝ≥0) : ℝ) : ℂ)) *
      ((((modulus (kr (z⁻¹ : GL (Fin 2) F).val (tinv h).val).det)⁻¹ : ℝ≥0) : ℝ) : ℂ) = 1 := by
    have h0 : (modulus (z.val).det)⁻¹ ^ 2 * (modulus (h.val).det)⁻¹ ^ 2 ≠ 0 :=
      hm ▸ modulus_ne_zero hP
    have h1 := mul_inv_cancel₀ h0
    rw [hm]
    exact_mod_cast h1
  rw [hc, one_mul]

end GlobalTheory.CompanionTheory.GL2DualWhittakerPair.Jac
