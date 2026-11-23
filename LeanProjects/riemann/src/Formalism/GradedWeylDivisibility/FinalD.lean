import Formalism.GradedWeylDivisibility.FinalC
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.SSIdxFinite
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.SSBasis
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.RowActDiagWeight
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.RowActMul
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.NablaLLe
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.NablaLBasis
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.NablaLKBasis
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.NablaLDiag
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.NablaLTwist
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.NablaLTwMem
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.TensorBasis
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.BlockActTensor

namespace Formalism.GradedWeylDivisibility

theorem sSIdxFinite : SSIdxFinite := semistandard_index_finite
theorem sSBasis : SSBasis := semistandard_basis
theorem rowActDiagWeight : RowActDiagWeight := row_action_diagonal_weight
theorem rowActMul : RowActMul := row_action_mul
theorem nablaLLe : NablaLLe := nabla_weight_le
theorem nablaLBasis : NablaLBasis := nablaLBasis_of rowActMul
theorem nablaLKBasis : NablaLKBasis := nablaLKBasis_of rowActMul sSBasis
theorem nablaLDiag : NablaLDiag := nablaLDiag_of rowActMul rowActDiagWeight nablaLBasis
theorem nablaLTwMem : NablaLTwMem := nabla_twist_mem
theorem tensorBasis : TensorBasis := tensor_power_basis
theorem blockActTensor : BlockActTensor := block_action_tensor

end Formalism.GradedWeylDivisibility
