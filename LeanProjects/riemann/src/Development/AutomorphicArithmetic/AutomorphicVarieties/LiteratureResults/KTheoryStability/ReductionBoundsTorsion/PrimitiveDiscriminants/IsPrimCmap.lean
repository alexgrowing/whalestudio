import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.SBridgeAlt
import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.PrimitiveDiscriminants.ResRing

noncomputable section

open NumberField NumberField.InfinitePlace Matrix UpperTheory.V.KT UpperTheory.V.KL

namespace PositivityTheory.KB

namespace LargePrimeDiscriminant

theorem isCyc_cmap (hC : SChain) {G H : Type} [Group G] [Group H] (f : G →* H) {m : ℕ}
    {z : Chn G (m + 1)} (hz : IsCyc z) : IsCyc (cmap f (m + 1) z) := by
  unfold IsCyc at hz ⊢
  rw [hC.2.1 G H f m z, hz, map_zero]

end LargePrimeDiscriminant

end PositivityTheory.KB

end
