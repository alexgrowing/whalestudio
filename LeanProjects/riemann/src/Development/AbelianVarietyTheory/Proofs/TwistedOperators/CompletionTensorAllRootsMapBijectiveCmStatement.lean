import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompletionTensorAllRootsMapBijectiveCm
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CxRootsInjective
open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll GlobalTheory.TrEll.RealTorus
open scoped TensorProduct ComplexConjugate Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.completionTensorAllRootsMap_bijective_cm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (r : ℕ) (P : PPol σ r) (w : InfinitePlace F) (τ : EmbOver E w), Function.Bijective (PsiAll P τ) := by
  first | exact @GlobalTheory.TrEll.RealTorus.PsiAll_bijective | exact GlobalTheory.TrEll.RealTorus.PsiAll_bijective | (intros; apply GlobalTheory.TrEll.RealTorus.PsiAll_bijective <;> assumption)
