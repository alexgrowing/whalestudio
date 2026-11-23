import Formalism.FormalDegreeBessel.FormalDegreeRatio.DSLowK
import Formalism.FormalDegreeBessel.FormalDegreeRatio.DSFdeg
import Formalism.FormalDegreeBessel.FormalDegreeRatio.DSRatio

namespace Formalism.QuantumDeterminants

theorem lowKInt : LowKInt := low_k_integrable_holds
theorem lowKDiff : LowKDiff := low_k_differentiable_holds
theorem lowKDom : LowKDom := low_k_dominant_holds
theorem holLowK : HolLowK := holomorphic_low_k_holds
theorem holHC : HolHC := holomorphic_harish_chandra_holds
theorem fdegPos : FdegPos := formal_degree_pos_holds
theorem fdegPerm : FdegPerm := formal_degree_perm_holds
theorem fdegVand : FdegVand := formal_degree_vandermonde_holds
theorem fdegWeyl : FdegWeyl := formal_degree_weyl_holds
theorem fdegRatio : FdegRatio := formalDegreeShiftRatio_holds
theorem formal_degree_unitary_facts : FormalDegreeTwoByTwo := formalDegreeTwoByTwo_holds
theorem holFdeg : HolFdeg := holomorphicFormalDegree_holds
theorem capelliHW : CapelliHW := capelliHighestWeight_holds
theorem capPPerm : CapPPerm := capelliPolynomialPermInvariant_holds

end Formalism.QuantumDeterminants
