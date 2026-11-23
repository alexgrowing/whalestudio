import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnfoldingConditionsFromSecondMixedCoordinate
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
theorem _root_.GlobalTheory.T.unfolding_conditions_from_second_mixedCoordinate : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (V V₀ W W₀ : HSp D) (ρ σ : ℕ) (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ) (vT : VolM D σ V₀.rank) (p : Pieces V₀ W W₀ ρ σ) (x : Mx D W.rank ρ) (y : Mx D V₀.rank σ), p.Is dV dW x ψ → ∀ (β₂ : Mx D V₀.rank σ → ℂ) (g : WO V₀ W₀ → ℂ) (g' : WO V₀ W → ℂ), VacG ψ V₀ W₀ p.Γ₀ g → IsThetaFunO ψ V₀ W g' → (∀ y', dW.mixT V₀ ψ vT.μ vT.𝓕 g' y' = β₂ y' • g) → (∀ η ∈ p.B₂, ∀ b, dW.incAdj V₀ b = dW.incY V₀ η → ∀ z, β₂ (z + b) = β₂ z) → (∀ z, β₂ z ≠ 0 → ∃ r : Mx D V₀.rank σ, r.map (finPart D) = 0 ∧ ∃ η ∈ p.B₂, dW.incAdj V₀ (z - (y + r)) = dW.incY V₀ η) → (∀ ξ ∈ p.B₁, heisO ψ V₀ W (dW.incX V₀ ξ) g' = ψ (symplO V₀ W (dW.incAdj V₀ y) (dW.incX V₀ ξ)) • g') ∧ (∀ η ∈ p.B₂, heisO ψ V₀ W (dW.incY V₀ η) g' = g') ∧ IsLatVac (heisO ψ V₀ W) (p.Γ₀.map (dW.inc0 V₀)) g' := by
  first | exact @GlobalTheory.MixCondT.main | exact GlobalTheory.MixCondT.main | (intros; apply GlobalTheory.MixCondT.main <;> assumption)
