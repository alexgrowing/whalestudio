import Mathlib
import Development.AutomorphicArithmetic.ThetaCorrespondence.GoodReduction.NeronOggShafarevich
import Development.AutomorphicArithmetic.ThetaCorrespondence.GoodReduction.CMGood

namespace UpperTheory.Lit

theorem neronOggShafarevich : GlobalTheory.Published.NeronOggShafarevichSt := UpperTheory.Lit.Nos.Nos.neronOggShafarevich

theorem potentialGoodReduction : GlobalTheory.Published.PotentialGoodReductionSt :=
  GlobalTheory.potentialGoodReduction_of_neronOggShafarevich neronOggShafarevich

theorem cmPotentialGoodReduction : GlobalTheory.Published.CMPotentialGoodReductionSt :=
  cmPotentialGoodReduction_of_nos neronOggShafarevich

theorem serreTateGoodReduction : GlobalTheory.Published.SerreTateGoodReductionSt :=
  ⟨neronOggShafarevich, potentialGoodReduction, cmPotentialGoodReduction⟩

end UpperTheory.Lit
