import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RealSizeNonneg
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittMixedCoordinateWeilTranslateCompactMajorantStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegrableSchwartzMajorantPullbackUnitriangularStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsArchEquivEq
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff

noncomputable section
namespace GlobalTheory.Unf

theorem flatFun_majorant : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V V₀ W W₀ : HSp D) (ρ σ : ℕ) (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ) (vS : VolM D W.rank ρ) (vT : VolM D σ V₀.rank) (χV χW : (AE D)ˣ →* Circle) (om : Om V W), IsWeilDatumO ψ V W χV χW om → ∀ (vU : VolU D ρ) (x : Matrix (Fin W.rank) (Fin ρ) D.host.E), LinearIndependent D.host.E x.transpose → ∀ Φ, IsThetaFunO ψ V W Φ → ∀ K : Set (GA D V × GA D W), IsCompact K → ∃ M : UX D ρ → ℝ, Integrable M vU.ν ∧ ∀ p ∈ K, ∀ y w u, ‖flatFun ψ dV dW vS.μ vS.𝓕 vT.μ vT.𝓕 (rat x) y (om p Φ) w u‖ ≤ M u := by
  intro D ψ V V₀ W W₀ ρ σ dV dW vS vT χV χW om hW vU x hx Φ hΦ K hK
  have hn : ∀ a, ‖ψ a‖ = 1 := hW.std.1.2.1
  obtain ⟨θ, hθ⟩ := GlobalTheory.AdelicU.exists_isInfFam D
  obtain ⟨K', hK', hC⟩ := GlobalTheory.T.wittMixedCoordinate_weilTranslate_compact_majorant D ψ V W χV χW om hW θ hθ V₀ ρ dV vS Φ hΦ K hK
  obtain ⟨N, hN⟩ := GlobalTheory.T.integrable_schwartzMajorant_pullback_unitriangular D θ hθ W.rank ρ vU x hx
  obtain ⟨C, hC⟩ := hC N
  refine ⟨fun u => C * maj θ K' N ((rat x : Mx D W.rank ρ) ⬝ u.1.1), (hN K' hK').const_mul C, ?_⟩
  intro p hp y w u
  have hT := vT.covol
  unfold flatFun evalAt
  rw [norm_mul, norm_star]
  have h1 : ‖psiUni ψ u.1‖ = 1 := hn _
  rw [h1, one_mul]
  unfold GlobalTheory.MixModel.HypDec.mixT
  have hb : ∀ ξ ∈ vT.𝓕, ‖heisO ψ V₀ W (dW.incX V₀ ξ) (heisO ψ V₀ W (dW.incAdj V₀ y) (heisO ψ V₀ W (dW.inc0 V₀ w)
      (dV.mixS W ψ vS.μ vS.𝓕 (om p Φ) ((rat x : Mx D W.rank ρ) ⬝ u.1.1)))) 0‖ ≤ C * maj θ K' N ((rat x : Mx D W.rank ρ) ⬝ u.1.1) := by
    intro ξ _
    rw [dW.integrandT_eq, norm_mul, hn, one_mul]
    exact hC p hp _ _
  have := norm_setIntegral_le_of_norm_le_const (by rw [hT.2.2]; exact ENNReal.one_lt_top) hb
  rw [measureReal_def, hT.2.2, ENNReal.toReal_one, mul_one] at this
  exact this
end GlobalTheory.Unf
