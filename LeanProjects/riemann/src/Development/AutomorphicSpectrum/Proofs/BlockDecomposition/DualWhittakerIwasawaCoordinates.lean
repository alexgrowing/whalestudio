import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.RationalPrimesBelowPlaces
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.SquareIntegrable.SSmooth
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TemperedBoundGL2
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open scoped ValuativeRel
open GlobalTheory.CompanionTheory.DualHol

noncomputable section

namespace GlobalTheory.CompanionTheory.DualHol.Coord

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem det_blk (h : GL (Fin 2) F) :
    (!![h.val 0 0, h.val 0 1, 0; h.val 1 0, h.val 1 1, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) F).det
      = (h.val).det := by
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Matrix.det_fin_two, Fin.succAbove]

theorem em_coe (h : GL (Fin 2) F) : (GL2LocalData.em h).val =
    !![h.val 0 0, h.val 0 1, 0; h.val 1 0, h.val 1 1, 0; 0, 0, 1] := by
  have hd : (!![h.val 0 0, h.val 0 1, 0; h.val 1 0, h.val 1 1, 0; 0, 0, 1] :
      Matrix (Fin 3) (Fin 3) F).det ≠ 0 := by
    rw [det_blk]
    exact ((Matrix.isUnit_iff_isUnit_det _).1 h.isUnit).ne_zero
  unfold GL2LocalData.em
  rw [dif_pos hd]
  rfl

theorem em_mul (g h : GL (Fin 2) F) : GL2LocalData.em (g * h) = GL2LocalData.em g * GL2LocalData.em h := by
  apply Units.ext
  rw [Units.val_mul, em_coe, em_coe, em_coe, Units.val_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_three]

theorem em_one : GL2LocalData.em (1 : GL (Fin 2) F) = 1 := by
  apply Units.ext
  rw [em_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem em_inv (g : GL (Fin 2) F) : (GL2LocalData.em g)⁻¹ = GL2LocalData.em g⁻¹ := by
  apply inv_eq_of_mul_eq_one_right
  rw [← em_mul, mul_inv_cancel, em_one]

theorem tinv_mul' {n : ℕ} (g h : GL (Fin n) F) : GL2LocalData.tinv (g * h) = GL2LocalData.tinv g * GL2LocalData.tinv h := by
  apply Units.ext
  show ((g * h)⁻¹ : GL (Fin n) F).val.transpose =
    (g⁻¹ : GL (Fin n) F).val.transpose * (h⁻¹ : GL (Fin n) F).val.transpose
  rw [_root_.mul_inv_rev, Units.val_mul, Matrix.transpose_mul]

theorem tinv_mem' {n : ℕ} {k : GL (Fin n) F} (hk : k ∈ GLnLocal.integralGL F n) :
    GL2LocalData.tinv k ∈ GLnLocal.integralGL F n := by
  obtain ⟨h1, h2⟩ := (GLnLocal.mem_integralGL_iff F n).1 hk
  exact (GLnLocal.mem_integralGL_iff F n).2 ⟨fun i j => h2 j i, fun i j => h1 j i⟩

theorem long_weyl2_mem_integral_GL : (GL2LocalData.w2 : GL (Fin 2) F) ∈ GLnLocal.integralGL F 2 := by
  refine (GLnLocal.mem_integralGL_iff F 2).2 ⟨fun i j => ?_, fun i j => ?_⟩
  · show (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) F) i j ∈ 𝒪[F]
    fin_cases i <;> fin_cases j <;> simp [zero_mem, one_mem]
  · show (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) F) i j ∈ 𝒪[F]
    fin_cases i <;> fin_cases j <;> simp [zero_mem, one_mem]

theorem long_weyl3_mem_integral_GL : (GL2LocalData.w3 : GL (Fin 3) F) ∈ GLnLocal.integralGL F 3 := by
  refine (GLnLocal.mem_integralGL_iff F 3).2 ⟨fun i j => ?_, fun i j => ?_⟩
  · show (!![0, 0, 1; 0, 1, 0; 1, 0, 0] : Matrix (Fin 3) (Fin 3) F) i j ∈ 𝒪[F]
    fin_cases i <;> fin_cases j <;> simp [zero_mem, one_mem]
  · show (!![0, 0, 1; 0, 1, 0; 1, 0, 0] : Matrix (Fin 3) (Fin 3) F) i j ∈ 𝒪[F]
    fin_cases i <;> fin_cases j <;> simp [zero_mem, one_mem]

theorem em_mem {k : GL (Fin 2) F} (hk : k ∈ GLnLocal.integralGL F 2) :
    GL2LocalData.em k ∈ GLnLocal.integralGL F 3 := by
  have key : ∀ {g : GL (Fin 2) F}, (∀ i j, g.val i j ∈ 𝒪[F]) → ∀ i j, (GL2LocalData.em g).val i j ∈ 𝒪[F] := by
    intro g hg i j
    rw [em_coe]
    fin_cases i <;> fin_cases j <;> simp [zero_mem, one_mem, hg]
  obtain ⟨h1, h2⟩ := (GLnLocal.mem_integralGL_iff F 2).1 hk
  refine (GLnLocal.mem_integralGL_iff F 3).2 ⟨key h1, ?_⟩
  rw [em_inv]
  exact key h2

theorem diag_pair_inv (x y : Fˣ) : (dg2 x y)⁻¹ = dg2 x⁻¹ y⁻¹ := by
  apply Units.ext
  rfl

theorem long_weyl3_mul_transpose_inv_embed_diag (x y : Fˣ) :
    (GL2LocalData.w3 : GL (Fin 3) F) * GL2LocalData.tinv (GL2LocalData.em (dg2 x y)) = dg 1 y⁻¹ x⁻¹ * GL2LocalData.w3 := by
  apply Units.ext
  have h : (GL2LocalData.tinv (GL2LocalData.em (dg2 x y))).val = (GL2LocalData.em (dg2 x⁻¹ y⁻¹)).val.transpose := by
    show ((GL2LocalData.em (dg2 x y))⁻¹ : GL (Fin 3) F).val.transpose = _
    rw [em_inv, diag_pair_inv]
  rw [Units.val_mul, Units.val_mul, h, em_coe]
  show (!![0, 0, 1; 0, 1, 0; 1, 0, 0] : Matrix (Fin 3) (Fin 3) F) * _ =
    (!![((1 : Fˣ) : F), 0, 0; 0, ((y⁻¹ : Fˣ) : F), 0; 0, 0, ((x⁻¹ : Fˣ) : F)] : Matrix (Fin 3) (Fin 3) F) *
      !![0, 0, 1; 0, 1, 0; 1, 0, 0]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, dg2]

theorem long_weyl2_mul_transpose_inv_diag_pair (x y : Fˣ) :
    (GL2LocalData.w2 : GL (Fin 2) F) * GL2LocalData.tinv (dg2 x y) = dg2 y⁻¹ x⁻¹ * GL2LocalData.w2 := by
  apply Units.ext
  have h : (GL2LocalData.tinv (dg2 x y)).val = (dg2 x⁻¹ y⁻¹).val.transpose := by
    show ((dg2 x y)⁻¹ : GL (Fin 2) F).val.transpose = _
    rw [diag_pair_inv]
  rw [Units.val_mul, Units.val_mul, h]
  show (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) F) * _ =
    (!![((y⁻¹ : Fˣ) : F), 0; 0, ((x⁻¹ : Fˣ) : F)] : Matrix (Fin 2) (Fin 2) F) * !![0, 1; 1, 0]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, dg2]

theorem coords : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (a b : Fˣ) (k : GL (Fin 2) F), k ∈ GLnLocal.integralGL F 2 → ∃ k₃ ∈ GLnLocal.integralGL F 3, ∃ k₂ ∈ GLnLocal.integralGL F 2, (∀ W : GL (Fin 3) F → ℂ, GL2LocalData.dW3 W (GL2LocalData.em (dg2 (a * b) b * k)) = W (dg 1 b⁻¹ (a * b)⁻¹ * k₃)) ∧ (∀ W' : GL (Fin 2) F → ℂ, GL2LocalData.dW2 W' (dg2 (a * b) b * k) = W' (dg2 b⁻¹ (a * b)⁻¹ * k₂)) := by
  intro F _ _ _ _ a b k hk
  refine ⟨GL2LocalData.w3 * GL2LocalData.tinv (GL2LocalData.em k), mul_mem long_weyl3_mem_integral_GL (tinv_mem' (em_mem hk)),
    GL2LocalData.w2 * GL2LocalData.tinv k, mul_mem long_weyl2_mem_integral_GL (tinv_mem' hk), fun W => ?_, fun W' => ?_⟩
  · show W (GL2LocalData.w3 * GL2LocalData.tinv (GL2LocalData.em (dg2 (a * b) b * k))) = _
    rw [em_mul, tinv_mul', ← mul_assoc, long_weyl3_mul_transpose_inv_embed_diag, mul_assoc]
  · show W' (GL2LocalData.w2 * GL2LocalData.tinv (dg2 (a * b) b * k)) = _
    rw [tinv_mul', ← mul_assoc, long_weyl2_mul_transpose_inv_diag_pair, mul_assoc]

end GlobalTheory.CompanionTheory.DualHol.Coord
