import Formalism.WachLatticeTwists.CharacterSplitJumps.WachTwistSplitTheoremFromTorsionBound
import Formalism.WachLatticeTwists.CharacterSplitJumps.CharacterJumpProofs.HZeroInvariantsKilled
import Formalism.WachLatticeTwists.TorsionKernelSplitting.TorsionKernelProofs.SplitText
import Formalism.WachLatticeTwists.TorsionKernelSplitting.TorsionKernelProofs.TheoremNFiveTopSplitOfSplit
import Formalism.WachLatticeTwists.TheoremNFiveSplit

open Finset Classical

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.JT

open Formalism.NG Formalism.RepresentationBoundsCohomology.BR Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic Formalism.RepresentationBoundsCohomology.JS

theorem HZeroHypothesesJumps.toIn {ℓ : ℕ} [Fact ℓ.Prime] {D : InvariantsCohomologyData ℓ} {w : ℤ_[ℓ]ˣ} {m : ℕ} {J : Multiset ℤ}
    (h : HZeroHypothesesJumps D w m J) : HZeroHypotheses D w m (jumpsDualTwist J) := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩ := h
  exact ⟨a3, a4, a5, (jumps_of_dual_twist J).1.2 a1, (jumps_of_dual_twist J).2.2 a2, a6, a7, a8, a9, a10⟩

end Formalism.RepresentationBoundsCohomology.JT
