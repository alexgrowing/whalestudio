import Formalism.LogFactorialIndices.SignedSubspaceIndex.SumInterlacedBoundFails
import Mathlib
import Formalism.LogFactorialIndices.SignedSubspaceIndex.LogProductFormula
import Formalism.LogFactorialIndices.SignedSubspaceIndex.IdxBase
import Formalism.LogFactorialIndices.SignedSubspaceIndex.IdxDet
import Formalism.LogFactorialIndices.SignedSubspaceIndex.SubspaceLatticeIndex

namespace Formalism.LatticeIndexTer

theorem latFinite : LatFinite := lattice_quotient_finite
theorem latBasis : LatBasis := lattice_has_basis
theorem idxDet : IdxDet := lattice_index_eq_det_valuation

end Formalism.LatticeIndexTer
