import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KFacDifferentiable
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

namespace GlobalTheory

theorem upperHalf_prodImPow_contDiffOn : ∀ (F : Type) [Field F] [NumberField F] (σ : ℂ), ContDiffOn ℝ ∞ (fun z : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℂ => ∏ τ : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F, (((z τ).im : ℝ) : ℂ) ^ (-1 - 2 * σ)) (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.upperHalf F) := by
  intro F _ _ σ
  apply contDiffOn_prod
  intro τ _
  intro z hz
  apply ContDiffAt.contDiffWithinAt
  have hpos : 0 < (z τ).im := hz τ
  have hL : ContDiff ℝ ∞ (fun w : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℂ => (((w τ).im : ℝ) : ℂ)) := by
    have : (fun w : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℂ => (((w τ).im : ℝ) : ℂ)) =
        (Complex.ofRealCLM.comp (Complex.imCLM.comp (ContinuousLinearMap.proj τ))) := by
      ext w; simp
    rw [this]; exact ContinuousLinearMap.contDiff _
  have hslit : (((z τ).im : ℝ) : ℂ) ∈ Complex.slitPlane := Complex.ofReal_mem_slitPlane.2 hpos
  have hg : ContDiffAt ℂ ∞ (fun s : ℂ => s ^ (-1 - 2 * σ)) (((z τ).im : ℝ) : ℂ) :=
    (analyticAt_id.cpow analyticAt_const hslit).contDiffAt
  exact (hg.restrict_scalars ℝ).comp z hL.contDiffAt

end GlobalTheory
