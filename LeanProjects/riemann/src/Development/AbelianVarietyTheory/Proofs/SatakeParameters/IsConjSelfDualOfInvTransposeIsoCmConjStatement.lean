import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsConjSelfDualOfInvTransposeIsoCmConj
import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DualIsConjByOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub
open NumberField Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isConjSelfDual_of_invTranspose_iso_cmConj : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (a : ℕ) (π : CuspSub L a) (S : π.V ≃ₗ[ℂ] π.V), (∀ o φ, S (π.op (invTOp o) φ) = π.op (conjOp o) (S φ)) → π.IsCsd := by
  first | exact @GlobalTheory.CsdFromConj.isCsd_of_invT_conj | exact GlobalTheory.CsdFromConj.isCsd_of_invT_conj | (intros; apply GlobalTheory.CsdFromConj.isCsd_of_invT_conj <;> assumption)
