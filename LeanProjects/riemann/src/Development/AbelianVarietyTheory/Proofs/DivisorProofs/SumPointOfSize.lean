import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ESmall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumPointOfWeightNumericalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NumericalPointOfSizeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightPointOfSizeStatement
open GlobalTheory.RefSum GlobalTheory.CovTop GlobalTheory.BigTop

namespace GlobalTheory.RefSum

theorem sumPt_of_size : Size → SumPt := fun h => GlobalTheory.T.sum_point_of_weight_numerical (GlobalTheory.T.weight_point_of_size h) (GlobalTheory.T.numerical_point_of_size h)

end GlobalTheory.RefSum
