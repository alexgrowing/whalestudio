import Formalism.LocalToGlobal.GenusGluing.GenusApproximation.GenusApproximationProofs.CommensurableHolds
import Formalism.LocalToGlobal.GenusGluing.GenusApproximation.GenusApproximationProofs.IdempotentCalculationHolds
import Formalism.LocalToGlobal.GenusGluing.GenusApproximation.GenusApproximationProofs.GlueSmulSame
import Formalism.LocalToGlobal.GenusGluing.GenusApproximation.GenusApproximationProofs.AsmOfMemComplF
import Formalism.LocalToGlobal.Columns.RecLevelHost

noncomputable section

namespace Formalism.L2.GenusGluing.Gen

open NumberField IsDedekindDomain Matrix Formalism.L2.Col
open scoped TensorProduct

theorem glueExists_holds : GlueExists := glueExists_of idempotentCalculation_holds

theorem genusToPoint_holds : GenusToPoint :=
  genusToPoint_of localEquality_holds memLocalizedStd_holds idempotentCofinite_holds idempotentCalculation_holds glueExists_holds commensurable_holds

theorem pointToGenus_holds : PointToGenus :=
  pointToGenus_of localEquality_holds memLocalizedStd_holds idempotentDenominator_holds idempotentCalculation_holds

theorem localToAdelic_holds : LocToAd := locToAd_of genusToPoint_holds

theorem adelicToLocal_holds : AdToLoc := adToLoc_of pointToGenus_holds

theorem localAdelicEquiv_holds : Bridge := bridge_of localToAdelic_holds adelicToLocal_holds

end Formalism.L2.GenusGluing.Gen
