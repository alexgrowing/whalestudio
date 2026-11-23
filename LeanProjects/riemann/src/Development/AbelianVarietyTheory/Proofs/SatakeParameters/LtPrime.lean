import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Alternates
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.FrobeniusOrbits.HostCorollaries
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory.InertPrimeLarge

theorem lt_prime : ∀ {D : D7} (L : SizeData₂ D) (l : ℕ), l.Prime → l ≠ 2 →
    jacobiSym (-(D.host.d : ℤ)) l ≠ 1 → L.sc.x ^ (L.sc.ez / 5) < l := by
  intro D L l hl h2 hj
  by_contra hlt
  push_neg at hlt
  have hle : l ≤ D.host.splitBound := le_trans (Nat.le_floor hlt) L.split_tie
  exact hj (D.host.split_small l hl h2 hle)

end GlobalTheory.InertPrimeLarge
