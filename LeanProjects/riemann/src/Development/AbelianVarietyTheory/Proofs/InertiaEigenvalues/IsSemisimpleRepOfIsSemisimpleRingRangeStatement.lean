import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSemisimpleRepOfIsSemisimpleRingRange
import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
open Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSemisimpleRep_of_isSemisimpleRing_range : ∀ (Γ k : Type) [Group Γ] [Field k] (d : ℕ) (ρ : MonoidAlgebra k Γ →ₐ[k] Matrix (Fin d) (Fin d) k), IsSemisimpleRing ρ.range → IsSSRep ((ρ.toMonoidHom.comp (MonoidAlgebra.of k Γ)).toHomUnits) := by
  first | exact @GlobalTheory.isSSRep_of_isSemisimpleRing_range | exact GlobalTheory.isSSRep_of_isSemisimpleRing_range | (intros; apply GlobalTheory.isSSRep_of_isSemisimpleRing_range <;> assumption)
