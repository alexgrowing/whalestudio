import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RelativeIndexFlags.Development
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RelativeIndexFlags.RelIndexUnipotentConjSymm

namespace Formalism.L2.SG.Pf.RelativeIndexFlags

theorem unipotent_conj_index_holds (n : ℕ) (K : Type*) [Field K] : UniConjIdx n K := by
  intro X g hg hX _ _
  exact Filt.relIndex_unipotent_conj_symm (loGen n K) Filt.closure_le_FG X g hg hX

end Formalism.L2.SG.Pf.RelativeIndexFlags
