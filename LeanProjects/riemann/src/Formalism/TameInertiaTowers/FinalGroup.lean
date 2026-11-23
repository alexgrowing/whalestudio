import Formalism.TameInertiaTowers.CentralOrderTwo.OrderOfThreeUnitsTwoPow
import Formalism.TameInertiaTowers.CentralOrderTwo.TwoAdic
import Formalism.TameInertiaTowers.CentralOrderTwo.MemDecompositionSubgroupIff
import Formalism.TameInertiaTowers.CentralOrderTwo.NegOneNeOneUnitsZmodFour
import Formalism.TameInertiaTowers.CentralOrderTwo.Groups
import Formalism.TameInertiaTowers.CentralOrderTwo.NormalOrderTwoCentral

namespace Formalism.TwoAdicCyclotomicDecomposition

theorem tower_group_foundations :
    UnitsTwoPow ∧ QuotCyclic ∧ TwoAdicOrder ∧ TwoAdicVal ∧ DecompModel ∧ GmRank ∧ GensModel ∧
    GamEModel ∧ GGModel ∧ CentralExtAbelian ∧ CommGen ∧ RankBound ∧
    NormalOrderTwoCentral ∧ TwistVal ∧ CoinvLength ∧ PGroupGen ∧ GenusModel ∧ GenusAbelian :=
  ⟨unitsTwoPow, quotCyclic, twoAdicOrder, twoAdicVal, decompModel, gmRank, gensModel,
   gamEModel, ggModel, centralExtAbelian, commGen, rankBound,
   normalOrderTwoCentral, twistVal, coinvLength, pGroupGen, genusModel, genusAbelian⟩

end Formalism.TwoAdicCyclotomicDecomposition
