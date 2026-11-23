import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaRankSubmoduleChainBounded
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HypothesesAbsDet
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSubAug
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RkSubSuccLe

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_rank_submodule_chain_bounded : GlobalTheory.FunPr.Hypotheses₂ → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n m : ℕ) (χ : GL (Fin n) k →* ℂˣ), IsOpen {g | χ g = 1} → ∀ ρ : ℕ,
    ∃ L : ℕ, ∀ (r : ℕ) (N : Fin r → Submodule ℂ (Matrix (Fin n) (Fin m) k → ℂ)),
      StrictMono N → (∀ i, GlobalTheory.ThetaGLSub.IsSub χ (N i) ∧
        GlobalTheory.ThetaGLSub.aug m χ ⊔ GlobalTheory.ThetaGLRank.rkSub k n m (ρ + 1) ≤ N i ∧
        N i ≤ GlobalTheory.ThetaGLSub.aug m χ ⊔ GlobalTheory.ThetaGLRank.rkSub k n m ρ) → r ≤ L := by
  first | exact @GlobalTheory.ThetaGLLayer.layer_bound | exact GlobalTheory.ThetaGLLayer.layer_bound | (intros; apply GlobalTheory.ThetaGLLayer.layer_bound <;> assumption)
