import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsConjOfTraceEqResiduallyAbsIrreducibleDVR
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_conj_of_trace_eq_residually_absIrreducible_DVR : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Γ : Type) [Group Γ] (a : ℕ) (ρ ρ' : Γ →* GL (Fin a) O), Formalism.MainNotions.N.AbsIrrSub (Formalism.MainNotions.N.mapRep (IsLocalRing.residue O) ρ) ⊤ → (∀ g, ((ρ g : GL (Fin a) O) : Matrix (Fin a) (Fin a) O).trace = ((ρ' g : GL (Fin a) O) : Matrix (Fin a) (Fin a) O).trace) → ∃ U : GL (Fin a) O, ∀ g, ρ' g * U = U * ρ g := by
  first | exact @GlobalTheory.TraceConjugacy.exists_conj_of_trace_eq | exact GlobalTheory.TraceConjugacy.exists_conj_of_trace_eq | (intros; apply GlobalTheory.TraceConjugacy.exists_conj_of_trace_eq <;> assumption)
