import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SigmaFiniteParameterProductMeasure
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralShiftHerm
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.ColumnSplitting
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.CompanionTheory.ColumnSplitting.ShiftP
section Generic
variable {R : Type} [CommRing R] {r t n : ℕ}

theorem upperUnipotent_mul (hn : r + t = n) (y y' : Matrix (Fin r) (Fin t) R) :
    bl hn 1 y 0 1 * bl hn 1 y' 0 1 = bl hn 1 (y + y') 0 1 := by
  unfold bl
  rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  simp [add_comm]

theorem upperUnipotent_zero (hn : r + t = n) : bl hn (1 : Matrix (Fin r) (Fin r) R) 0 0 1 = 1 := by
  unfold bl
  rw [Matrix.fromBlocks_one]
  exact Matrix.submatrix_one_equiv _

theorem det_bl_one (hn : r + t = n) (y : Matrix (Fin r) (Fin t) R) : (bl hn 1 y 0 1).det = 1 := by
  unfold bl
  rw [Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁]
  simp

end Generic

variable {D : D7} {n t : ℕ} {B W : HSp D}

def shear {r : ℕ} (hn : r + t = n) (y : Mx D r t) : GL (Fin n) (AE D) where
  val := bl hn 1 y 0 1
  inv := bl hn 1 (-y) 0 1
  val_inv := by rw [upperUnipotent_mul, add_neg_cancel, upperUnipotent_zero]
  inv_val := by rw [upperUnipotent_mul, neg_add_cancel, upperUnipotent_zero]

theorem det_shear {r : ℕ} (hn : r + t = n) (y : Mx D r t) :
    Matrix.GeneralLinearGroup.det (shear (D := D) hn y : GL (Fin n) (AE D)) = 1 :=
  Units.ext (det_bl_one hn y)

theorem integral_shear {r : ℕ} (hn : r + t = n) (y : Mx D r t) {m : ℕ} (μ : Measure (Mx D m n)) (hμ : μ.IsAddHaarMeasure)
    (f : Mx D m n → ℂ) : ∫ U, f (mm U (bl hn 1 y 0 1)) ∂μ = ∫ U, f U ∂μ := by
  have h := GlobalTheory.CompanionTheory.IwaAd.integral_mul_right m μ hμ (shear hn y) f
  rw [det_shear, map_one, one_npow, one_mul] at h
  exact h

end GlobalTheory.CompanionTheory.ColumnSplitting.ShiftP

namespace GlobalTheory.CompanionTheory.ColumnSplitting

theorem shift : Shift := by
  intro D n t B W d hn I Φ y a
  obtain ⟨𝓕, hf⟩ := I.cov₁
  have e := ShiftP.integral_shear hn y I.μ₁ hf.1
    (fun U => projS I.νK Φ (d.jX ⬝ U + d.j0 ⬝ (mm a (bl hn 1 y 0 1))))
  simp only [ikp, ikS]
  rw [← e]
  refine integral_congr_ae (Eventually.of_forall fun U => ?_)
  simp only [projS]
  refine integral_congr_ae (Eventually.of_forall fun k => ?_)
  simp only [mm, Matrix.mul_assoc, Matrix.add_mul]

end GlobalTheory.CompanionTheory.ColumnSplitting
end
