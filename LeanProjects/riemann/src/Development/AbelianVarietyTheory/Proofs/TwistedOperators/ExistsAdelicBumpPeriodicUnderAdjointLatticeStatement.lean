import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsAdelicBumpPeriodicUnderAdjointLattice
import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousReprSymm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfPartOneSubEInfSmul
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergOperatorThetaFunctionalMixedSourceMode
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergThetaMixedModelTargetOfMixedModel
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsThetaFunctionMixedCoordinateBumpMulCoreStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MixedModelTargetBumpMulCoreThetaExistsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaFunctionDeterminedByMixedCoordinatesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_adelicBump_periodic_under_adjointLattice : ∀ (D : D7) (V₀ W W₀ : HSp D) (σ : ℕ) (dW : HypDec W W₀ σ) (B₂ : AddSubgroup (Mx D σ V₀.rank)), FinLat B₂ → ∀ y : Mx D V₀.rank σ, ∃ β : Mx D V₀.rank σ → ℂ, IsBump β ∧ β y ≠ 0 ∧ (∀ η ∈ B₂, ∀ b, dW.incAdj V₀ b = dW.incY V₀ η → ∀ z, β (z + b) = β z) ∧ ∀ z, β z ≠ 0 → ∃ r : Mx D V₀.rank σ, r.map (finPart D) = 0 ∧ ∃ η ∈ B₂, dW.incAdj V₀ (z - (y + r)) = dW.incY V₀ η := by
  first | exact @GlobalTheory.AscFinBumpAdj.exists_bump_adj | exact GlobalTheory.AscFinBumpAdj.exists_bump_adj | (intros; apply GlobalTheory.AscFinBumpAdj.exists_bump_adj <;> assumption)
