import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.IntegralityGoodReduction
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.AltSmooth
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.ApplySmooth

noncomputable section

open scoped ContDiff

namespace UpperTheory.V.Lit.Dr

theorem pullB : PullB := by
  intro V F _ _ _ _ _ _ Y hY hC l hl q w hw
  obtain ⟨hlsm, hlpos, _⟩ := hl
  have hφY : ∀ p ∈ Y, l p • p ∈ Y := fun p hp => hC _ (hlpos p hp) p hp
  have hφ : ∀ p ∈ Y, ContDiffAt ℝ ∞ (fun x => l x • x) p := fun p hp =>
    (hlsm.contDiffAt (hY.mem_nhds hp)).smul contDiffAt_id
  have hwat : ∀ p ∈ Y, ContDiffAt ℝ ∞ w (l p • p) := fun p hp =>
    hw.contDiffAt (hY.mem_nhds (hφY p hp))
  refine ⟨?_, ?_⟩
  · intro p hp
    apply ContDiffAt.contDiffWithinAt
    apply altSmooth V V F q (pull l w) p
    intro v
    have hcomp : ContDiffAt ℝ ∞ (fun y => w (l y • y)) p :=
      ContDiffAt.comp (g := w) (f := fun x => l x • x) p (hwat p hp) (hφ p hp)
    have h := applySmooth V V F q (fun y => w (l y • y))
      (fun i y => fderiv ℝ (fun x => l x • x) y (v i)) p hcomp
      (fun i => ((hφ p hp).fderiv_right (by simp)).clm_apply contDiffAt_const)
    exact h
  · intro p hp
    exact extDeriv_pullback ((hwat p hp).differentiableAt (by simp)) (hφ p hp)
      (by simpa using (WithTop.coe_le_coe.mpr le_top : (2 : WithTop ℕ∞) ≤ ∞))

end UpperTheory.V.Lit.Dr
