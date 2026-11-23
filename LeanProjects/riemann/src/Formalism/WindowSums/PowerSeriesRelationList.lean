import Formalism.WindowSums.AnnihilatorPolynomials.DistinctTerms
import Formalism.WindowSums.AnnihilatorPolynomials.LeOfPowMemIdealOfDistinctTerms
import Formalism.WindowSums.AnnihilatorPolynomials.FirstCoefficientBoundHolds
import Formalism.WindowSums.AnnihilatorPolynomials.EvalOneSmulDecomposition
import Formalism.WindowSums.AnnihilatorPolynomials.ZpowVal
import Formalism.WindowSums.AnnihilatorPolynomials.ValProd
import Formalism.WindowSums.AnnihilatorPolynomials.WindowSum
import Formalism.WindowSums.AnnihilatorPolynomials.Lagrange
import Formalism.WindowSums.StatementRelay

namespace Formalism.WindowSums

theorem arc_C2Lower : PowMemIdealOfLe := pow_mem_ideal_of_le
theorem arc_ZpowVal : ZpowVal := valuation_zpow_sub_one
theorem arc_ValProd : ValProd := valProd_of valuation_zpow_sub_one
theorem arc_KillerVal : KillerVal := killerVal_of valuation_zpow_sub_one
theorem arc_KillerKills : KillerKills := annihilatorPoly_kills
theorem arc_WindowSum : WindowSum := sum_padicValInt_le
theorem arc_Lagrange : Lagrange := lagrange_annihilation

end Formalism.WindowSums
