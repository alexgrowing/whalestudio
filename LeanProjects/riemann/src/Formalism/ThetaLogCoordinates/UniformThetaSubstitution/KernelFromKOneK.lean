import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.KernelFromKOne
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.WModel
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.WChain
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.EGaussK
import Mathlib
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.EdgeExponent

namespace Formalism.InvariantFactorPaths.G7.Top

open Formalism.InvariantFactorPaths.G7

theorem modelExists : ModelExists := modelExists_statement
theorem betaNonVacuous : BetaNonVacuous := BetaNonVacuous_of modelExists lawExists gcIsBeta gcUnique
theorem chainModel : ChainModel := chainModel_statement

theorem kernel_from_k_one_k : KernelBoundsGeneric := kernel_bounds_generic

end Formalism.InvariantFactorPaths.G7.Top
