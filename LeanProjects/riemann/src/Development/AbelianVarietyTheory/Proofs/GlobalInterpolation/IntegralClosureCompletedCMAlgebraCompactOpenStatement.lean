import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IntegralClosureCompletedCMAlgebraCompactOpen
import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralClosure_completedCMAlgebra_compact_open : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ v : HeightOneSpectrum (𝓞 F), IsCompact (integralClosure (v.adicCompletionIntegers F) (Fv F v ⊗[F] E) : Set (Fv F v ⊗[F] E)) ∧ IsOpen (integralClosure (v.adicCompletionIntegers F) (Fv F v ⊗[F] E) : Set (Fv F v ⊗[F] E)) := by
  first | exact @GlobalTheory.CompletedOrder.isCompact_isOpen_integralClosure | exact GlobalTheory.CompletedOrder.isCompact_isOpen_integralClosure | (intros; apply GlobalTheory.CompletedOrder.isCompact_isOpen_integralClosure <;> assumption)
