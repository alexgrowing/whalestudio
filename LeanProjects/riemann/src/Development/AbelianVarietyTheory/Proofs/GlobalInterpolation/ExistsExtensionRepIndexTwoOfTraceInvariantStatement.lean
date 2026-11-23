import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsExtensionRepIndexTwoOfTraceInvariant
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
open Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_extension_rep_index_two_of_trace_invariant : ∀ (Γ k : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [Field k] [CharZero k] [IsAlgClosed k] [TopologicalSpace k] [IsTopologicalRing k] (n : ℕ) (η : Γ →* ℤˣ), IsOpen (η.ker : Set Γ) → ∀ r : η.ker →* GL (Fin n) k, Continuous r → IsSSRep r → (∀ (g : Γ) (h h' : η.ker), (h' : Γ) = g * h * g⁻¹ → ((r h' : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).trace = ((r h : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).trace) → ∃ ρ : Γ →* GL (Fin n) k, Continuous ρ ∧ IsSSRep ρ ∧ ∀ h : η.ker, ρ h = r h := by
  first | exact @GlobalTheory.IndexTwoExt.main | exact GlobalTheory.IndexTwoExt.main | (intros; apply GlobalTheory.IndexTwoExt.main <;> assumption)
