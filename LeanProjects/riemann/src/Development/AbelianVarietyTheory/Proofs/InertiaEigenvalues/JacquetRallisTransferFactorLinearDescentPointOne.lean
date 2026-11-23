import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LeftMulTau
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisTransferFactorKrylovDetStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedValuationParitySignCharacterKernelNormStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleHermitianPairStructureFactsStatement

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.LinDesc

theorem eta_inv_eq {F : Type} [NormedField F] (x : F) : eta x⁻¹ = eta x := by
  have key : (∃ y : F, ‖x⁻¹‖ = ‖y‖ ^ 2) ↔ ∃ y : F, ‖x‖ = ‖y‖ ^ 2 := by
    constructor
    · rintro ⟨y, hy⟩
      refine ⟨y⁻¹, ?_⟩
      rw [norm_inv] at hy
      rw [norm_inv, inv_pow, ← hy, inv_inv]
    · rintro ⟨y, hy⟩
      exact ⟨y⁻¹, by rw [norm_inv, norm_inv, inv_pow, hy]⟩
  unfold eta
  by_cases h : ∃ y : F, ‖x‖ = ‖y‖ ^ 2
  · rw [if_pos (key.mpr h), if_pos h]
  · rw [if_neg (fun h' => h (key.mp h')), if_neg h]

theorem eta_neg_one_pow {F : Type} [NormedField F] (r : ℕ) : eta ((-1 : F) ^ r) = 1 := by
  unfold eta
  rw [if_pos]
  exact ⟨1, by simp⟩

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
  (A : Et F E) {r : ℕ} {τ : A.K} {p : Fin r → F}

theorem row_pow (hG : A.IsGen τ p) (c : A.K) (n : ℕ) :
    (fun i : Fin r => Algebra.trace F A.K (τ ^ (i : ℕ) * c)) ᵥ* (companion p) ^ n =
      fun j : Fin r => Algebra.trace F A.K (τ ^ (j : ℕ) * (τ ^ n * c)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ← Matrix.vecMul_vecMul, ih, ← leftMul_tau A hG, row_mul]
    funext j
    congr 2
    ring

theorem Cm_pt_one (hG : A.IsGen τ p) (lam : F) (a : A.K) :
    Cm (pt A hG lam 1 a) = Algebra.traceMatrix F (bas A hG) * Algebra.leftMulMatrix (bas A hG) a := by
  ext i j
  have h1 : Cm (pt A hG lam 1 a) i j = Algebra.trace F A.K (τ ^ (j : ℕ) * (τ ^ (i : ℕ) * a)) := by
    simp only [Cm, pt, Matrix.of_apply]
    rw [row_pow A hG]
  have h2 := congrFun (row_mul A hG a (τ ^ (i : ℕ))) j
  simp only [Matrix.vecMul, dotProduct] at h2
  rw [h1, Matrix.mul_apply]
  simp only [Algebra.traceMatrix_apply, Algebra.traceForm_apply, bas_apply]
  rw [mul_comm (τ ^ (i : ℕ)) a, ← h2]
  exact Finset.sum_congr rfl fun k _ => by rw [mul_comm (τ ^ (i : ℕ))]

end GlobalTheory.JR.LinDesc

namespace GlobalTheory.JR.LinDesc

theorem omega_pt_one : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (A : Et F E) (r : ℕ) (τ : A.K) (p : Fin r → F) (hG : A.IsGen τ p) (lam : F),
    ∃ κ₀ : ℂ, ∀ a : A.K, IsUnit a → ∀ g : GL (Fin r) F,
      omega (act g (LinDesc.pt A hG lam 1 a)) = κ₀ * eta ((g : Matrix (Fin r) (Fin r) F).det) * A.etaK a := by
  intro F E _ _ _ _ _ A r τ p hG lam
  obtain ⟨hmul, -, -, -⟩ := GlobalTheory.T.unramifiedValuationParitySign_character_kernel_norms F E
  have hnd := (GlobalTheory.T.etaleHermitianPair_structure_facts F E A).2.2.1
  have hT : (Algebra.traceMatrix F (bas A hG)).det ≠ 0 := by
    rw [LinearMap.BilinForm.nondegenerate_iff_det_ne_zero (bas A hG)] at hnd
    convert hnd using 2
    ext i j
    rw [Algebra.traceForm_toMatrix, Algebra.traceMatrix_apply, Algebra.traceForm_apply]
  refine ⟨eta (Algebra.traceMatrix F (bas A hG)).det, fun a ha g => ?_⟩
  have hL := GlobalTheory.T.jacquetRallis_transfer_factor_krylov_det F r
  have hdet : (g : Matrix (Fin r) (Fin r) F).det * ((g⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F).det = 1 := by
    rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
  have hg : (g : Matrix (Fin r) (Fin r) F).det ≠ 0 := left_ne_zero_of_mul_eq_one hdet
  have hginv := eq_inv_of_mul_eq_one_right hdet
  have hna : Algebra.norm F a ≠ 0 := (ha.map (Algebra.norm F)).ne_zero
  have hr : (-1 : F) ^ r ≠ 0 := pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
  unfold omega Et.etaK
  rw [hL.1, hL.2, Cm_pt_one, Matrix.det_mul, Matrix.det_mul, ← Algebra.norm_eq_matrix_det, hginv,
    hmul _ _ hr (mul_ne_zero (mul_ne_zero hT hna) (inv_ne_zero hg)),
    hmul _ _ (mul_ne_zero hT hna) (inv_ne_zero hg), hmul _ _ hT hna, eta_neg_one_pow, eta_inv_eq]
  ring

end GlobalTheory.JR.LinDesc
