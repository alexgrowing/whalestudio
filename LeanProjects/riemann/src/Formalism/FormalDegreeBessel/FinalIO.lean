import Formalism.FormalDegreeBessel.FormalDegreeRatio.IOLeft
import Formalism.FormalDegreeBessel.FormalDegreeRatio.IOCentral
import Formalism.FormalDegreeBessel.FormalDegreeRatio.CapelliHighestWeightConjugated

namespace Formalism.QuantumDeterminants

theorem glRelAd : GlRelAd := gl_relation_adjoint_holds
theorem capCentral : CapCentral := capelli_central_holds
theorem qMinorLeft : QMinorLeft := quantum_minor_left_holds
theorem capLeft : CapLeft := capelli_left_holds
theorem capHW : CapHW := capelli_highest_weight_holds
theorem capComatrix : CapComatrix := capelli_comatrix_holds
theorem eabHTransport : EabHTransport := conjugated_generator_transport
theorem eabHGl : EabHGl := conjugated_generator_gl_relation
theorem capCentralH : CapCentralH := capelli_central_conjugated
theorem capLeftH : CapLeftH := capelli_left_conjugated
theorem capHWH : CapHWH := capelli_highest_weight_conjugated

end Formalism.QuantumDeterminants
