import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhitKA
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.WhitNDgOfLocalOfSteps
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.CoefDataExists
import Development.WeilBound.CoreStatements.PublishedTheorems.SiegelWeilSchrodinger.SiegelWeilUnitarySchrodingerLit
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaDecompositionUnitary
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelParabolicUnnMatrixBlockUpperTriangular
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.EisensteinMaximalParabolic
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianMeasureConjugationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsAUNeZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaCoefficientOfConvergence
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinRationalPoints
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HolomorphicContinuationValueNnrealPowFactor
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.IwaRedHand

open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

theorem mod_of_cg : ∀ (D : D7) (n : ℕ) (lam : Measure (PositivityTheory.GramSchwartzFunctions.BC.hermA D n)), lam.IsAddHaarMeasure → ∀ (a : GL (Fin n) (AE D)) (f : Mx D n n → ℂ), ∫ b, f b.1 ∂lam = ((GlobalTheory.Doubling.absA D (Matrix.GeneralLinearGroup.det a) : ℝ) : ℂ) ^ n * ∫ c, f (a.1 * c.1 * GlobalTheory.MixModel.adj a.1) ∂lam := by
  intro D n lam hlam a f
  have h := GlobalTheory.T.hermitian_measure_conjugation D n lam hlam a (fun c => f c.1)
  have hr0 : 0 < absA D (Matrix.GeneralLinearGroup.det a) :=
    pos_iff_ne_zero.2 (GlobalTheory.ResAniso.ResProp.absAU_ne_zero _)
  have e : ∫ c, f (a.1 * c.1 * adj a.1) ∂lam =
      npow (absA D (Matrix.GeneralLinearGroup.det a)) (-(n : ℂ)) * ∫ b, f b.1 ∂lam := h
  have key : ((absA D (Matrix.GeneralLinearGroup.det a) : ℝ) : ℂ) ^ n *
      npow (absA D (Matrix.GeneralLinearGroup.det a)) (-(n : ℂ)) = 1 := by
    have hne : ((absA D (Matrix.GeneralLinearGroup.det a) : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast hr0.ne'
    unfold npow
    rw [← Complex.cpow_natCast, ← Complex.cpow_add _ _ hne]
    simp
  rw [e, ← mul_assoc, key, one_mul]

end GlobalTheory.CompanionTheory.IwaRedHand
