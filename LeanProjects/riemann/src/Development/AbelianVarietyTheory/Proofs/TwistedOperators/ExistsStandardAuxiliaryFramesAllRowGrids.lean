import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExtendByZeroTrivialDecomposition

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.AscFin

section Gen

variable {D : D7} {A B : HSp D} {c σ : ℕ}

theorem isAuxiliaryVectorWittDec_evenFourierJacobiRescale (d : HermitianOrthogonalExtensionData A B c (-1)) (h : c = 2 * σ) :
    IsAuxiliaryVectorWittDec d (GlobalTheory.AscInh.rescale (GlobalTheory.RowUnf.jacDec d h) (fun p => (-D.host.xi0) ^ (p.1 + 1))
      fun _ => GlobalTheory.AscInh.xiPow_ne D _) := by
  refine ⟨by omega, ?_, fun p => (star ((-D.host.xi0) ^ (p.1 + 1)))⁻¹, ?_⟩
  · ext i p
    simp only [GlobalTheory.AscInh.rescale, GlobalTheory.RowUnf.jacDec, HermitianOrthogonalExtensionData.iso, colsOf, Matrix.mul_diagonal, Matrix.submatrix_apply, id]
    exact mul_comm _ _
  · ext i p
    simp only [GlobalTheory.AscInh.rescale, GlobalTheory.RowUnf.jacDec, colsOf, Matrix.mul_diagonal, Matrix.submatrix_apply, id]
    exact mul_comm _ _

theorem isAuxiliaryVectorWittDec_oddBesselRescale (d : HermitianOrthogonalExtensionData A B c (-1)) (h : c = 2 * σ + 1) :
    IsAuxiliaryVectorWittDec d (GlobalTheory.AscInh.rescale (GlobalTheory.RowUnf.besDec d h) (fun p => (-D.host.xi0) ^ (p.1 + 1))
      fun _ => GlobalTheory.AscInh.xiPow_ne D _) := by
  refine ⟨by omega, ?_, fun p => (star ((-D.host.xi0) ^ (p.1 + 1)))⁻¹, ?_⟩
  · ext i p
    simp only [GlobalTheory.AscInh.rescale, GlobalTheory.RowUnf.besDec, HermitianOrthogonalExtensionData.iso, colsOf, Matrix.mul_diagonal, Matrix.submatrix_apply, id]
    exact mul_comm _ _
  · ext i p
    simp only [GlobalTheory.AscInh.rescale, GlobalTheory.RowUnf.besDec, colsOf, Matrix.mul_diagonal, Matrix.submatrix_apply, id]
    exact mul_comm _ _

theorem coreMat_iA (d : HermitianOrthogonalExtensionData A B c (-1)) (h : c = 2 * σ + 1) :
    GlobalTheory.RowUnf.coreMat d h * (GlobalTheory.OrthSumExists.orthDecHsum D A (GlobalTheory.SeeSaw.Model.nLine D)).iA = frameMat B A d.ι := by
  change (Matrix.fromCols (frameMat B A d.ι) (GlobalTheory.RowUnf.midCol d h)).submatrix id (finSumFinEquiv (m := A.rank) (n := 1)).symm *
    (Matrix.fromRows (1 : Matrix (Fin A.rank) (Fin A.rank) D.host.E) (0 : Matrix (Fin 1) (Fin A.rank) D.host.E)).submatrix
      finSumFinEquiv.symm id = _
  rw [Matrix.submatrix_mul_equiv, Matrix.fromCols_mul_fromRows, Matrix.mul_one, Matrix.mul_zero, add_zero, Matrix.submatrix_id_id]

theorem coreMat_iB (d : HermitianOrthogonalExtensionData A B c (-1)) (h : c = 2 * σ + 1) :
    (GlobalTheory.RowUnf.coreMat d h * (GlobalTheory.OrthSumExists.orthDecHsum D A (GlobalTheory.SeeSaw.Model.nLine D)).iB) *ᵥ
      (fun _ => (-D.host.xi0) ^ 0) = fun i => d.a i ⟨σ, by omega⟩ := by
  have e : GlobalTheory.RowUnf.coreMat d h * (GlobalTheory.OrthSumExists.orthDecHsum D A (GlobalTheory.SeeSaw.Model.nLine D)).iB = GlobalTheory.RowUnf.midCol d h := by
    change (Matrix.fromCols (frameMat B A d.ι) (GlobalTheory.RowUnf.midCol d h)).submatrix id (finSumFinEquiv (m := A.rank) (n := 1)).symm *
      (Matrix.fromRows (0 : Matrix (Fin A.rank) (Fin 1) D.host.E) (1 : Matrix (Fin 1) (Fin 1) D.host.E)).submatrix
        finSumFinEquiv.symm id = _
    rw [Matrix.submatrix_mul_equiv, Matrix.fromCols_mul_fromRows, Matrix.mul_one, Matrix.mul_zero, zero_add,
      Matrix.submatrix_id_id]
  rw [e]
  funext i
  change ∑ j : Fin 1, GlobalTheory.RowUnf.midCol d h i j * (-D.host.xi0) ^ 0 = _
  rw [Fin.sum_univ_one, pow_zero, mul_one]
  rfl

end Gen

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc)

theorem auxiliaryFrames_standard : Std (GlobalTheory.AscInh.auxiliaryFrames G) where
  zA := rfl
  zB := by
    funext i
    simp only [GlobalTheory.AscInh.auxiliaryFrames, GlobalTheory.AscInh.lineDec, Matrix.mulVec, dotProduct, pow_zero, mul_one]
    exact Fin.sum_univ_one _
  ζ ρ := by
    funext i
    show (-D.host.xi0) ^ ρ = (-D.host.xi0) ^ ρ * (-D.host.xi0) ^ 0
    rw [pow_zero, mul_one]
  hB ρ h := isAuxiliaryVectorWittDec_oddBesselRescale _ _
  aB ρ h := coreMat_iA _ _
  zB' ρ h := coreMat_iB _ _
  hJ ρ h := isAuxiliaryVectorWittDec_evenFourierJacobiRescale _ _
  aJ ρ h := rfl

theorem exists_std_frames : All fun {_} _ _ _ {G} _ _ => ∃ F : Frames G, Std F :=
  fun _ _ _ _ _ _ _ G _ _ _ => ⟨_, auxiliaryFrames_standard G⟩

end GlobalTheory.AscFin

end
