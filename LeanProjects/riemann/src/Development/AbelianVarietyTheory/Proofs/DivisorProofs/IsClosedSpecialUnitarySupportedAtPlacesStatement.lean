import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedSpecialUnitarySupportedAtPlaces
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.PlaneStrongApproxGeneratorImports
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModerateGrowthOfHasCompactSupport
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosureDivMem
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published
open scoped TensorProduct Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isClosed_specialUnitarySupportedAtPlaces : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (ε : AF F), IsClosed (SUSupp σ J ε) := by
  first | exact @GlobalTheory.SUSuppClosed.isClosed_SUSupp | exact GlobalTheory.SUSuppClosed.isClosed_SUSupp | (intros; apply GlobalTheory.SUSuppClosed.isClosed_SUSupp <;> assumption)
