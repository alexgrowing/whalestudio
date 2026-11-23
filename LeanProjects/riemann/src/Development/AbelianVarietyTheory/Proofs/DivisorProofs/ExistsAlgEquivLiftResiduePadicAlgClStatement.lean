import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAlgEquivLiftResiduePadicAlgCl
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.KbIsAlgClosedAndConj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_algEquiv_lift_residue_padicAlgCl : ∀ (l : ℕ) [Fact l.Prime] (L : IntermediateField ℚ_[l] (PadicAlgCl l)) (φ : GlobalTheory.ZJ.kb l ≃+* GlobalTheory.ZJ.kb l), (∀ x : GlobalTheory.ZJ.OO l, (x : PadicAlgCl l) ∈ L → φ (IsLocalRing.residue (GlobalTheory.ZJ.OO l) x) = IsLocalRing.residue (GlobalTheory.ZJ.OO l) x) → ∃ g : PadicAlgCl l ≃ₐ[L] PadicAlgCl l, ∀ x y : GlobalTheory.ZJ.OO l, IsLocalRing.residue (GlobalTheory.ZJ.OO l) y = φ (IsLocalRing.residue (GlobalTheory.ZJ.OO l) x) → ‖g (x : PadicAlgCl l) - y‖ < 1 := by
  first | exact @GlobalTheory.ZJ.exists_algEquiv_lift_residue | exact GlobalTheory.ZJ.exists_algEquiv_lift_residue | (intros; apply GlobalTheory.ZJ.exists_algEquiv_lift_residue <;> assumption)
