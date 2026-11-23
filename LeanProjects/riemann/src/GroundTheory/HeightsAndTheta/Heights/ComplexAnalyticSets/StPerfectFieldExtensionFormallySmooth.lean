import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

def PerfectFieldExtensionFormallySmooth.Statement : Prop :=
  ∀ (F K : Type) [Field F] [Field K] [Algebra F K] [PerfectField F], Algebra.FormallySmooth F K

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
