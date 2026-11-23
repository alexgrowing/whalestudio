import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaSubmoduleChainBounded
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HypothesesAbsDet
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSubAug

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_submodule_chain_bounded : GlobalTheory.FunPr.Hypotheses₂ → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n m : ℕ) (χ : GL (Fin n) k →* ℂˣ), IsOpen {g | χ g = 1} →
    ∃ L : ℕ, ∀ (r : ℕ) (N : Fin r → Submodule ℂ (Matrix (Fin n) (Fin m) k → ℂ)),
      StrictMono N → (∀ i, GlobalTheory.ThetaGLSub.IsSub χ (N i)) → r ≤ L := by
  first | exact @GlobalTheory.ThetaGLRank.boundedChains_thetaGL | exact GlobalTheory.ThetaGLRank.boundedChains_thetaGL | (intros; apply GlobalTheory.ThetaGLRank.boundedChains_thetaGL <;> assumption)
