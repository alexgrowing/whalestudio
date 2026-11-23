import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsRingEquivPadicOfResidueCardUniformizer
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl ValuativeRel NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ringEquiv_padic_of_residueCard_uniformizer : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [IsTopologicalRing k] [CharZero k] (T : ℕ) [Fact T.Prime], Nat.card (IsLocalRing.ResidueField 𝒪[k]) = T → Irreducible (T : 𝒪[k]) → ∃ φ : ℚ_[T] ≃+* k, Continuous φ ∧ Continuous φ.symm ∧ ∀ x : ℚ_[T], φ x ∈ 𝒪[k] ↔ ‖x‖ ≤ 1 := by
  first | exact @GlobalTheory.QpChar.exists_ringEquiv_padic | exact GlobalTheory.QpChar.exists_ringEquiv_padic | (intros; apply GlobalTheory.QpChar.exists_ringEquiv_padic <;> assumption)
