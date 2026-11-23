import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GCauchyStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.ColEmpty
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.HfNormLeTwo
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.PerFactor
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.LemmaN
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.ContDiffOfDifferentiableFd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GCauchy
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.PaThDiffLe
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.LemmaS
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.DimStatement
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.ExtAllInputs
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.GreedySplittingPrincipalTorusExistsStatement
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.CharStatementHolds

open ReciprocityTheory.ChartRestriction.G.I2

namespace GlobalTheory.ThetaTorus

theorem gSup_holds : GSupStatement := gSup GlobalTheory.packingCount

theorem propA_holds : PropAStatement := propA GlobalTheory.packingCount GlobalTheory.gaussTail_of_card_le

theorem dim_holds : DimStatement := dim

theorem J_holds : JStatement :=
  jOf GlobalTheory.ext_all_inputs GlobalTheory.T.greedy_splitting_principal_torus_exists GlobalTheory.charStatement_holds
    (colTorus GlobalTheory.ext_all_inputs propA_holds gSup_holds)
    (colAbel GlobalTheory.ext_all_inputs propA_holds gSup_holds)
    (colEmpty GlobalTheory.ext_all_inputs propA_holds gSup_holds)

theorem N_holds : NStatement := lemmaN dim_holds

theorem I_holds : IStatement := iOf J_holds N_holds

end GlobalTheory.ThetaTorus
