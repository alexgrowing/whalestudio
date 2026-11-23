import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.TheoremOfCubeOfAdditionFormulas
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OddThetaFunctionExistenceUniqueness
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DifferentiableSqTh
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TaylorSeriesInParameterRescaleOfAlgebraic
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SigmaStarSquareQuotientInModelParameter
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

noncomputable section

namespace GlobalTheory.FrobStick

open PowerSeries

def colA (Λ : AddSubgroup ℂ) (z : ℂ) : ℂ := sgStar Λ z ^ 3

def colB (Λ : AddSubgroup ℂ) (v z : ℂ) : ℂ := sgStar Λ z * (sqTh Λ v z + wpF Λ v * sgStar Λ z ^ 2)

def colC (Λ : AddSubgroup ℂ) (v z : ℂ) : ℂ :=
  sgStar Λ z * deriv (sqTh Λ v) z - 2 * deriv (sgStar Λ) z * sqTh Λ v z

def tay (F : ℂ → ℂ) : PowerSeries ℂ := PowerSeries.mk (coef1 F)

def defect {R : Type*} [CommRing R] (f : Fin 3 → PowerSeries R) (s : PowerSeries R) :
    MvPowerSeries (Fin 3) R :=
  Matrix.det (Matrix.of fun i j =>
      (PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries (Fin 3) R) (f j) : MvPowerSeries (Fin 3) R)) -
    2 * PowerSeries.subst (MvPowerSeries.X 0 + MvPowerSeries.X 1 + MvPowerSeries.X 2 : MvPowerSeries (Fin 3) R) s *
      PowerSeries.subst (MvPowerSeries.X 0 - MvPowerSeries.X 1 : MvPowerSeries (Fin 3) R) s *
      PowerSeries.subst (MvPowerSeries.X 1 - MvPowerSeries.X 2 : MvPowerSeries (Fin 3) R) s *
      PowerSeries.subst (MvPowerSeries.X 2 - MvPowerSeries.X 0 : MvPowerSeries (Fin 3) R) s

end GlobalTheory.FrobStick
