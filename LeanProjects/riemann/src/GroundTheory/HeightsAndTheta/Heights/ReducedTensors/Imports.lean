import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open TensorProduct

namespace SectionsLattice

def BaseChangeReduced.Statement : Prop :=
  ∀ (k L A : Type) [Field k] [CharZero k] [Field L] [Algebra k L] [CommRing A] [Algebra k A],
    IsReduced A → IsReduced (L ⊗[k] A)

end SectionsLattice

end GroundTheory.Heights₂.Heights
