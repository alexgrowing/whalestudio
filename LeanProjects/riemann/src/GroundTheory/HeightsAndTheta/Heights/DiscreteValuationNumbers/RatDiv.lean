import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.CutIdentityRightSideCongrOfSubMem
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

theorem CommonFactorRemoval.proof (hmul : DivCycleMul.Statement.{u}) : CommonFactorRemoval.Statement.{u} := by
  intro O _ _ _ ϖ _ K _ _ ι _ P d hP b f g q s hf hg hq _ hH c L

  have hrat : ∀ W : Ideal (MRing ι O), W.IsPrime → f ∉ W → g ∉ W → q ∉ W →
      ratDiv W (f * q) (g * q) = ratDiv W f g := by
    intro W hW hfW hgW hqW
    funext G
    simp only [ratDiv, hmul O K ι W f q hW hfW hqW, hmul O K ι W g q hW hgW hqW, Pi.add_apply]
    ring
  refine ⟨?_, ?_⟩
  · unfold cutIdentityLeftSide
    rw [hrat P hP.multiProj.isPrime hf hg hq]
  · unfold cutIdentityRightSide cycEval
    congr 1
    funext W
    by_cases hW : divCycle P s W = 0
    · simp [hW]
    · dsimp only
      split_ifs with hϖ
      · rfl
      · obtain ⟨h1, h2, h3⟩ := hH W hW hϖ
        rw [hrat W (isPrime_of_divCycle_ne_zero hW) h1 h2 h3]

end GroundTheory.Heights₂.Heights.NumbersDVR
