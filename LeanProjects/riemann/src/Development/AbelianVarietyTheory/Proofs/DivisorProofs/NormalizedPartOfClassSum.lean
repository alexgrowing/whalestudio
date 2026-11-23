import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.RowSideOfCompatibleThetaPair
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ClassSumPin
import Formalism.LocalRingCardinality.DataNChTie
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeFamilyAdoptionFourthStatement

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Fc GlobalTheory.Fc.Ind GlobalTheory.BigTop

namespace GlobalTheory.Fc.Ind

theorem pNmj_of_pDiv_of_classSumPin :
    ∀ (D : D7) (O : Obj D) (c : ℝ) (b : Part D O c),
      PDiv D O c b → GlobalTheory.ExportPin.ClassSumPin b.pt → PNmj D O c b :=
  fun D O _ b hdiv hpin =>
    GlobalTheory.T.lattice_family_adoption_fourth D _ _ _ _ _ _ _ O.ex _ _ _ _ _ _ b.B b.pins b.Rr O.ex.nch_tie hdiv hpin

end GlobalTheory.Fc.Ind
