import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RealSizeNonneg
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergOperatorThetaFunctionalMixedSourceModeStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergThetaMixedModelTargetOfMixedModelStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedCoordinatesOfThetaFunctionAreThetaFunctionsStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff

namespace GlobalTheory.FlatHeis

theorem flatAt_heisO : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (V V₀ W W₀ : HSp D) (ρ σ : ℕ) (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ) (vS : VolM D W.rank ρ) (vT : VolM D σ V₀.rank) (vU : VolU D ρ) (x : Mx D W.rank ρ) (y : Mx D V₀.rank σ) (Ψ : WO V W → ℂ), IsThetaFunO ψ V W Ψ → (∀ w, evalAt ψ dV dW vS.μ vS.𝓕 vT.μ vT.𝓕 (heisO ψ V W (dV.ext0 W (dW.inc0 V₀ w)) Ψ) x y = heisO ψ V₀ W₀ w (evalAt ψ dV dW vS.μ vS.𝓕 vT.μ vT.𝓕 Ψ x y)) ∧ (∀ w, flatAt ψ dV dW vS.μ vS.𝓕 vT.μ vT.𝓕 vU.ν x y (heisO ψ V W (dV.ext0 W (dW.inc0 V₀ w)) Ψ) = heisO ψ V₀ W₀ w (flatAt ψ dV dW vS.μ vS.𝓕 vT.μ vT.𝓕 vU.ν x y Ψ)) ∧ ∀ γ, flatAt ψ dV dW vS.μ vS.𝓕 vT.μ vT.𝓕 vU.ν x y Ψ (ratW W₀ V₀ γ) = flatAt ψ dV dW vS.μ vS.𝓕 vT.μ vT.𝓕 vU.ν x y Ψ 0 := by
  intro D ψ hψ V V₀ W W₀ ρ σ dV dW vS vT vU x y Ψ hΨ
  have hMV := GlobalTheory.T.mixedCoordinates_of_thetaFunction_are_thetaFunctions D ψ hψ
  have hHT := GlobalTheory.T.heisenbergThetaMixedModelTarget_of_mixedModel D ψ hψ
  have hS : ∀ x', IsThetaFunO ψ V₀ W (dV.mixS W ψ vS.μ vS.𝓕 Ψ x') := fun x' =>
    hMV.1 V V₀ W ρ dV vS.μ vS.𝓕 vS.covol Ψ hΨ x'
  have hE : ∀ x', IsThetaFunO ψ V₀ W₀ (evalAt ψ dV dW vS.μ vS.𝓕 vT.μ vT.𝓕 Ψ x' y) := fun x' =>
    hMV.2 V₀ W W₀ σ dW vT.μ vT.𝓕 vT.covol _ (hS x') y
  have h1 : ∀ x' w, evalAt ψ dV dW vS.μ vS.𝓕 vT.μ vT.𝓕 (heisO ψ V W (dV.ext0 W (dW.inc0 V₀ w)) Ψ) x' y =
      heisO ψ V₀ W₀ w (evalAt ψ dV dW vS.μ vS.𝓕 vT.μ vT.𝓕 Ψ x' y) := by
    intro x' w
    have a := (GlobalTheory.T.heisenbergOperator_thetaFunctional_mixedSourceModel D ψ hψ V V₀ W ρ dV vS Ψ hΨ).2.2.1 x' (dW.inc0 V₀ w)
    have b := (hHT V₀ W W₀ σ dW vT.μ vT.𝓕 vT.covol _ (hS x')).2.1 w y
    unfold evalAt
    rw [a, b]
  refine ⟨fun w => h1 x w, fun w => ?_, fun γ => ?_⟩
  · funext w'
    show ∫ u, flatFun ψ dV dW vS.μ vS.𝓕 vT.μ vT.𝓕 x y (heisO ψ V W (dV.ext0 W (dW.inc0 V₀ w)) Ψ) w' u ∂vU.ν =
      ψ (symplOH V₀ W₀ w' w) * ∫ u, flatFun ψ dV dW vS.μ vS.𝓕 vT.μ vT.𝓕 x y Ψ (w' + w) u ∂vU.ν
    rw [← integral_const_mul]
    refine congrArg (fun F : UX D ρ → ℂ => ∫ u, F u ∂vU.ν) (funext fun u => ?_)
    simp only [flatFun, h1, heisO]
    ring
  · show ∫ u, flatFun ψ dV dW vS.μ vS.𝓕 vT.μ vT.𝓕 x y Ψ (ratW W₀ V₀ γ) u ∂vU.ν =
      ∫ u, flatFun ψ dV dW vS.μ vS.𝓕 vT.μ vT.𝓕 x y Ψ 0 u ∂vU.ν
    refine congrArg (fun F : UX D ρ → ℂ => ∫ u, F u ∂vU.ν) (funext fun u => ?_)
    have q := (hE (x ⬝ u.1.1)).quasi γ 0
    rw [add_zero, symplOH_zero_right, neg_zero, AddChar.map_zero_eq_one, one_mul] at q
    unfold flatFun
    rw [q]

end GlobalTheory.FlatHeis

end
