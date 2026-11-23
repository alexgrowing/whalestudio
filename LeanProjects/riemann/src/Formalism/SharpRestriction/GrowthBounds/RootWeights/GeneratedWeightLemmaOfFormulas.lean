import Formalism.SharpRestriction.GrowthBounds.RootWeights.IsotypicProjectionCommutesOperators
import Formalism.SharpRestriction.GrowthBounds.RootWeights.V2repResIsGLRep
import Formalism.SharpRestriction.GrowthBounds.RootWeights.MonomialsAreWeightVectors

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

theorem generated_weight_lemma_of_formulas (D : Formalism.BasicNotions.D7) (h2 : adm2 D) (hV1 : ValuationsAdditive D) (hDP : DividedPowerFormulaCharZero) (hBin : BinomialFormulaCharZero) :
    ShaLengthVersionTwo D :=
  generated_weight_lemma_char_zero D hV1 (stable_subspace_complete_reducibility D h2) highest_weight_module_bounds polynomial_operators_gl_relations monomials_are_weight_vectors polynomial_locally_finite hDP hBin

end Formalism.MainNotions.G.GLWeightTheory
