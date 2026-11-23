import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RealSizeNonneg
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SupNormWordSumSubLeAndDerivativeCost

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff

namespace GlobalTheory.Unf.SupFin

theorem supSob_laws : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ (S T : HSp D), (∀ k (f : WO S T → ℂ), IsThetaFunO ψ S T f → supSob ψ θ k f ≠ ⊤) ∧ (∀ (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ), (∀ U : AddSubgroup (WO S T), ∀ f ∈ GlobalTheory.Size.thetaLevel ψ S T U, dRho (heisO ψ S T) θ τ z f ∈ GlobalTheory.Size.thetaLevel ψ S T U) ∧ ∃ C : ℝ≥0, ∀ k (f : WO S T → ℂ), IsThetaFunO ψ S T f → supSob ψ θ k (dRho (heisO ψ S T) θ τ z f) ≤ C * supSob ψ θ (k + 1) f) ∧ ∀ k (f g : WO S T → ℂ) (c : ℂ), IsThetaFunO ψ S T f → IsThetaFunO ψ S T g → supSob ψ θ k (f + g) ≤ supSob ψ θ k f + supSob ψ θ k g ∧ supSob ψ θ k (c • f) = ‖c‖ₑ * supSob ψ θ k f := by
  intro D ψ hψ θ hθ S T
  have ha : ∀ g g' : WO S T → ℂ, (fun φ : WO S T → ℂ => ⨆ w, ‖φ w‖ₑ) (g + g') ≤
      (fun φ : WO S T → ℂ => ⨆ w, ‖φ w‖ₑ) g + (fun φ : WO S T → ℂ => ⨆ w, ‖φ w‖ₑ) g' :=
    GlobalTheory.Size.SupWord.supN_add_le
  have hs : ∀ (c : ℂ) (g : WO S T → ℂ), (fun φ : WO S T → ℂ => ⨆ w, ‖φ w‖ₑ) (c • g) =
      ‖c‖ₑ * (fun φ : WO S T → ℂ => ⨆ w, ‖φ w‖ₑ) g := GlobalTheory.Size.SupWord.supN_smul
  refine ⟨fun k f hf => ?_, fun τ z => ⟨fun U f hf => GlobalTheory.Size.dRho_mem_thetaLevel hψ hθ hf τ z, ?_⟩,
    fun k f g c hf hg => ⟨GlobalTheory.Size.SupWord.ws_add_le hψ hθ ha hf hg k, GlobalTheory.Size.SupWord.ws_smul hs k c f⟩⟩
  · refine GlobalTheory.Size.wordSum_ne_top_iff.2 fun l _ => ?_
    obtain ⟨C, hC⟩ := GlobalTheory.OrientedHeis.theta_bounded hψ (GlobalTheory.Size.theta_word hψ hθ l hf)
    refine ne_top_of_le_ne_top (ENNReal.ofReal_ne_top (r := C)) (iSup_le fun w => ?_)
    rw [← ofReal_norm_eq_enorm]
    exact ENNReal.ofReal_le_ofReal (hC w)
  · refine ⟨Real.toNNReal (∑ i, ∑ j, (|(z i j).re| + |(z i j).im|)), fun k f hf => ?_⟩
    exact GlobalTheory.Size.SupWord.ws_dRho_le hψ hθ ha hs hf τ z k

end GlobalTheory.Unf.SupFin
