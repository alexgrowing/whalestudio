import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CuspContragredientIsCMConjTwistOfPairedInvTransp
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DualIsConjByOne
open NumberField Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspContragredientIsCMConjTwist_of_paired_invTranspose : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (a : ℕ) (π : CuspSub L a) (ψ : HChar L), Paired (π.twist ψ⁻¹) (π.twist ψ⁻¹) invTOp → GlobalTheory.GalOfCusp.IsConjDualBy π ψ → DualIsConjBy π ψ := by
  first | exact @GlobalTheory.ConjDualPair.dualIsConjBy_of_paired_invT | exact GlobalTheory.ConjDualPair.dualIsConjBy_of_paired_invT | (intros; apply GlobalTheory.ConjDualPair.dualIsConjBy_of_paired_invT <;> assumption)
