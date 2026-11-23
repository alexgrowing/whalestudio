import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaSubmoduleSupNeTop
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HypothesesAbsDet
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSubAug

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_submodule_sup_ne_top : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.Published.MinguezThetaGL → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n m : ℕ), 1 ≤ n → 1 ≤ m → ∀ χ : GL (Fin n) k →* ℂˣ, IsOpen {g | χ g = 1} →
    ∀ N N' : Submodule ℂ (Matrix (Fin n) (Fin m) k → ℂ), GlobalTheory.ThetaGLSub.IsSub χ N → GlobalTheory.ThetaGLSub.IsSub χ N' →
      N ≠ GlobalTheory.SplitWeil.SB _ → N' ≠ GlobalTheory.SplitWeil.SB _ → N ⊔ N' ≠ GlobalTheory.SplitWeil.SB _ := by
  first | exact @GlobalTheory.ThetaGLSub.SumProper.main | exact GlobalTheory.ThetaGLSub.SumProper.main | (intros; apply GlobalTheory.ThetaGLSub.SumProper.main <;> assumption)
