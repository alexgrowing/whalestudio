import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaOfHeisenbergIntertwinerBoundedAtZeroStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapIntertwinesCoreHeisenbergOperatorsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapIntegrableAndBoundedLinearFormStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsArchEquivEq
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.Unf.Flat

variable {D : D7}

def coreMap {V V₀ W W₀ : HSp D} {ρ σ : ℕ} (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ) : WO V₀ W₀ →+ WO V W :=
  (dV.ext0 W).comp (dW.inc0 V₀)

theorem coreMap_eq {V V₀ W W₀ : HSp D} {ρ σ : ℕ} (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ) :
    ⇑(coreMap dV dW) = fun w => (dW.j0 * w) * dV.p0 := by
  funext w; rfl

theorem continuous_coreMap {V V₀ W W₀ : HSp D} {ρ σ : ℕ} (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ) :
    Continuous (coreMap dV dW) := by
  rw [coreMap_eq]
  exact (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const

theorem coreMap_finPart {V V₀ W W₀ : HSp D} {ρ σ : ℕ} (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ) (w : WO V₀ W₀)
    (h : w.map (finPart D) = 0) : (coreMap dV dW w).map (finPart D) = 0 := by
  show ((dW.j0 * w) * dV.p0).map (finPart D) = 0
  rw [Matrix.map_mul, Matrix.map_mul, h, Matrix.mul_zero, Matrix.zero_mul]

theorem coreMap_infPart {V V₀ W W₀ : HSp D} {ρ σ : ℕ} (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ) (w : WO V₀ W₀)
    (h : w.map (infPart D) = 0) : (coreMap dV dW w).map (infPart D) = 0 := by
  show ((dW.j0 * w) * dV.p0).map (infPart D) = 0
  rw [Matrix.map_mul, Matrix.map_mul, h, Matrix.mul_zero, Matrix.zero_mul]

theorem flatLaw : ∀ D : D7, FlatLaw D := by
  intro D ψ hψ V V₀ W W₀ ρ σ dV dW vS vT vU x hx y Ψ hΨ
  obtain ⟨θ, hθ⟩ := GlobalTheory.AdelicU.exists_isInfFam D
  have hF := GlobalTheory.T.flatMap_integrable_and_bounded_linearForm D ψ hψ θ hθ V V₀ W W₀ ρ σ dV dW vS vT vU x hx y
  refine ⟨hF.1 Ψ hΨ, ?_⟩
  exact GlobalTheory.T.theta_of_heisenberg_intertwiner_bounded_at_zero D ψ hψ θ hθ V W V₀ W₀ (coreMap dV dW) (continuous_coreMap dV dW)
    (coreMap_finPart dV dW) (coreMap_infPart dV dW)
    (fun f => flatAt ψ dV dW vS.μ vS.𝓕 vT.μ vT.𝓕 vU.ν (rat x) y f) (hF.2 0)
    (fun f w hf => ((GlobalTheory.T.flatMap_intertwines_core_heisenbergOperators D ψ hψ V V₀ W W₀ ρ σ dV dW vS vT vU (rat x) y f hf).2.1 w))
    (fun f γ hf => ((GlobalTheory.T.flatMap_intertwines_core_heisenbergOperators D ψ hψ V V₀ W W₀ ρ σ dV dW vS vT vU (rat x) y f hf).2.2 γ)) Ψ hΨ

end GlobalTheory.Unf.Flat
