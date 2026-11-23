import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThPr

noncomputable section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GroundTheory.Global PositivityTheory.Rg.Base1 GlobalTheory.CompanionTheory.BasePsi
open scoped ENNReal NNReal Classical

namespace GlobalTheory.CompanionTheory.BasePsi

theorem md_ray : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ (θ : ℝ →+* Ainf F) (r : ℝ → (AF F)ˣ), IsRay θ r →
    ∀ δ : ℝ, 0 < δ → md (r δ) = δ ^ Module.finrank ℚ F := by
  intro F _ _ hF θ r hr δ hδ
  obtain ⟨h1, h2⟩ := hr δ hδ
  have hw : ∀ w : InfinitePlace F, ‖(θ δ) w‖ = δ := by
    intro w
    have hreal : w.IsReal := hF.isReal w
    have hu := congrArg (fun f : ℝ →+* ℝ => f δ)
      (Subsingleton.elim ((InfinitePlace.Completion.extensionEmbeddingOfIsReal hreal).comp
        ((Pi.evalRingHom (fun v : InfinitePlace F => v.Completion) w).comp θ)) (RingHom.id ℝ))
    have hu' : InfinitePlace.Completion.extensionEmbeddingOfIsReal hreal ((θ δ) w) = δ := hu
    have hn := (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hreal).norm_map_of_map_zero
      (map_zero _) ((θ δ) w)
    rw [hu', Real.norm_eq_abs, abs_of_pos hδ] at hn
    exact hn.symm
  change (∏ w, ‖((r δ : AF F)).1 w‖ ^ w.mult) * (∏ᶠ v, ‖((r δ : AF F)).2 v‖) = δ ^ Module.finrank ℚ F
  rw [h1, h2]
  simp only [hw]
  rw [Finset.prod_pow_eq_pow_sum, InfinitePlace.sum_mult_eq]
  simp

end GlobalTheory.CompanionTheory.BasePsi

end
