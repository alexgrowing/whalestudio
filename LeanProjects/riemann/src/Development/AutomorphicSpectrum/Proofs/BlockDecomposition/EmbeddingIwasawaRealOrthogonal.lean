import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.CasselmanShalikaStandardVector
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BndIUnits
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrablePowerWeightUnits
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ValMeasurableEmbedding
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open Ad3.R (G2 Jd md KA lc)
open scoped NumberField.AdeleRing ValuativeRel
open GlobalTheory.CompanionTheory.GL2Factorization

noncomputable section

namespace GlobalTheory.CompanionTheory.GL2Factorization.EmC

theorem emR_coe (h : GL (Fin 2) ℝ) :
    ((GL2LocalData.emR h : GL (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) =
      !![h.val 0 0, h.val 0 1, 0; h.val 1 0, h.val 1 1, 0; 0, 0, 1] := by
  have hd : (!![h.val 0 0, h.val 0 1, 0; h.val 1 0, h.val 1 1, 0; 0, 0, 1] :
      Matrix (Fin 3) (Fin 3) ℝ).det ≠ 0 := by
    have h0 : h.val.det ≠ 0 := (Matrix.isUnits_det_units h).ne_zero
    rw [Matrix.det_fin_two] at h0
    rw [Matrix.det_fin_three]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val, Matrix.cons_val_fin_one]
    intro hh
    apply h0
    linarith
  rw [GL2LocalData.emR, dif_pos hd]
  rfl

theorem emR_iwasawa : ∀ (a b : ℝˣ) (k : GL (Fin 2) ℝ), k.val * k.valᵀ = 1 →
    GL2LocalData.emR (dg2 (a * b) b * k) = dg (a * b) b 1 * GL2LocalData.emR k ∧ GL2LocalData.emR k ∈ O3 := by
  intro a b k hk
  constructor
  · apply Units.ext
    rw [Units.val_mul, emR_coe, emR_coe]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [dg, dg2, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_three]
  · have e00 := congrFun (congrFun hk 0) 0
    have e01 := congrFun (congrFun hk 0) 1
    have e10 := congrFun (congrFun hk 1) 0
    have e11 := congrFun (congrFun hk 1) 1
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply, Matrix.one_apply] at e00 e01 e10 e11
    show ((GL2LocalData.emR k : GL (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) *
      ((GL2LocalData.emR k : GL (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ)ᵀ = 1
    rw [emR_coe]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three] <;> simp_all

end GlobalTheory.CompanionTheory.GL2Factorization.EmC
