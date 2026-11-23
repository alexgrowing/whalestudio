import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsArea
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

noncomputable section

theorem realForm_mul {p q r : ℕ} (A : Matrix (Fin p) (Fin q) ℂ) (B : Matrix (Fin q) (Fin r) ℂ) :
    realForm (A * B) = realForm A * realForm B := by
  ext ⟨i, a⟩ ⟨k, c⟩
  simp only [realForm, Matrix.mul_apply, Matrix.of_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
    Complex.re_sum, Complex.im_sum]
  fin_cases a <;> fin_cases c <;>
    simp only [Complex.mul_re, Complex.mul_im, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib,
      ← Finset.sum_neg_distrib, Fin.zero_eta, Fin.mk_one, Fin.isValue, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.head_cons] <;>
    refine Finset.sum_congr rfl fun j _ => by ring

theorem realForm_add {p q : ℕ} (A B : Matrix (Fin p) (Fin q) ℂ) :
    realForm (A + B) = realForm A + realForm B := by
  ext ⟨i, a⟩ ⟨k, c⟩
  fin_cases a <;> fin_cases c <;> simp [realForm] <;> ring

theorem realForm_one {q : ℕ} : realForm (1 : Matrix (Fin q) (Fin q) ℂ) = 1 := by
  ext ⟨i, a⟩ ⟨k, c⟩
  by_cases h : i = k <;> fin_cases a <;> fin_cases c <;> simp [realForm, Matrix.one_apply, h]

theorem realForm_conjTranspose {p q : ℕ} (A : Matrix (Fin p) (Fin q) ℂ) :
    realForm Aᴴ = (realForm A)ᵀ := by
  ext ⟨i, a⟩ ⟨k, c⟩
  fin_cases a <;> fin_cases c <;> simp [realForm]

theorem det_realForm {q : ℕ} (A : Matrix (Fin q) (Fin q) ℂ) :
    (realForm A).det = Complex.normSq A.det := by
  let B : Module.Basis (Fin q × Fin 2) ℝ (Fin q → ℂ) :=
    Complex.basisOneI.smulTower' (Pi.basisFun ℂ (Fin q))
  have hM : LinearMap.toMatrix B B ((Matrix.toLin' A).restrictScalars ℝ) = realForm A := by
    ext ⟨i, a⟩ ⟨j, b⟩
    rw [LinearMap.toMatrix_apply]
    simp only [B, Module.Basis.smulTower'_repr_mk, Module.Basis.smulTower'_apply,
      LinearMap.restrictScalars_apply, Pi.basisFun_repr, Pi.basisFun_apply]
    fin_cases a <;> fin_cases b <;>
      simp [realForm, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [← hM, LinearMap.det_toMatrix, LinearMap.det_restrictScalars, LinearMap.det_toLin',
    Algebra.norm_complex_apply]

theorem ComplexJacobian.proof : ComplexJacobian.Statement := by
  intro p q M
  have hR : 1 + (realForm M)ᵀ * realForm M = realForm (1 + Mᴴ * M) := by
    rw [realForm_add, realForm_one, realForm_mul, realForm_conjTranspose]
  set z := (1 + Mᴴ * M).det with hz
  have hstar : star z = z := by
    rw [hz, ← Matrix.det_conjTranspose, Matrix.conjTranspose_add, Matrix.conjTranspose_one,
      Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  have him : z.im = 0 := by
    have := congrArg Complex.im hstar
    simp only [Complex.star_def, Complex.conj_im] at this
    linarith
  rw [hR, det_realForm, Complex.normSq_apply, him]
  apply Complex.ext <;> simp [sq, him, ← hz]

end

end GroundTheory.Heights₂.Heights
