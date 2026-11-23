import Formalism.PieriBlockIdeals.JointTheoremALoc
import Formalism.RankGapBounds.RankGapProofs.FormsTensorLocalization

namespace Formalism.CohomologicalDescent

open TensorProduct Formalism.UG Formalism.RankGapBounds.FormsTensorLocalization

theorem exact_exponent_lattice_incl {k : Type} [CommRing k] {A : Type} [AddCommGroup A] [Module k A]
    (l : k) (B : Submodule k A) (h : ∃ e, LatIncl l B e) : LatIncl l B (exactExp l B) :=
  Nat.sInf_mem (s := {e : ℕ | LatIncl l B e}) h

theorem joint_theorem_a : JointTheoremA := by
  intro G _ Γ K k _ ι _ A _ _ B ρK l hex
  have h := theorem_a_of_lemma_a_holds G Γ K k ι A B ρK l (fun i => exactExp l (B i))
    (fun i => exact_exponent_lattice_incl l (B i) (hex i))
  exact ⟨h, Nat.sInf_le h⟩

theorem joint_theorem_a_local : JointTheoremALoc := by
  intro G _ Γ K k _ ι _ A _ _ B ρK l T _ _ _ _ S hex
  have h := TheoremA_loc_from_LemmaA G Γ K k ι A B ρK l (fun i => exactExp l (B i)) T S
    (fun i => exact_exponent_lattice_incl l (B i) (hex i))
  exact ⟨h, Nat.sInf_le h⟩

end Formalism.CohomologicalDescent
