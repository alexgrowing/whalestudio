import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PhaseApply
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.UnitaryDetAbs

open GlobalTheory.MixModel

theorem absE_det_matHom (D : D7) (W : HSp D) (h : GA D W) :
    GlobalTheory.Doubling.absE D.host.F D.host.E (Matrix.GeneralLinearGroup.det (matHom W h)) = 1 := by
  have hM := GlobalTheory.MixModel.mt_unitary W h
  have hdet := congrArg Matrix.det hM
  rw [Matrix.det_mul, Matrix.det_mul] at hdet
  have hadj : (GlobalTheory.MixModel.adj (mt W h)).det = cA D (mt W h).det := by
    rw [GlobalTheory.MixModel.adj, Matrix.det_transpose, RingHom.map_det]; rfl
  have hG : IsUnit (GlobalTheory.MixModel.gA W).det := by
    have e : (GlobalTheory.MixModel.gA W).det = incA D W.gram.det := by
      rw [GlobalTheory.MixModel.gA, GlobalTheory.MixModel.rat, RingHom.map_det]; rfl
    rw [e]
    exact (GlobalTheory.MixModel.gram_isUnit_det W).map _
  rw [hadj] at hdet
  have key : cA D (mt W h).det * (mt W h).det = 1 := by
    have e2 : cA D (mt W h).det * (mt W h).det * (GlobalTheory.MixModel.gA W).det = 1 * (GlobalTheory.MixModel.gA W).det := by
      rw [one_mul]; nth_rewrite 2 [← hdet]; ring
    exact hG.mul_right_cancel e2
  have hu : GlobalTheory.Doubling.conjUnit D.sp.cm.sig (Matrix.GeneralLinearGroup.det (matHom W h)) *
      Matrix.GeneralLinearGroup.det (matHom W h) = 1 := by
    ext
    exact key
  have h2 := congrArg (GlobalTheory.Doubling.absE D.host.F D.host.E) hu
  rw [map_mul, GlobalTheory.Doubling.absE_conjUnit, map_one, ← sq] at h2
  exact (pow_eq_one_iff_of_nonneg (by positivity) two_ne_zero).1 h2

end GlobalTheory.UnitaryDetAbs
