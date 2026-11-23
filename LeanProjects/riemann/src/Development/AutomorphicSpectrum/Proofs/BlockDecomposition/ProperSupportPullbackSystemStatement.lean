import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProperSupportPullbackSystem
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PowIdeal
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.proper_support_pullback_system : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X Z : Scheme.{0}} [X.Over (Spec (.of A))] [Z.Over (Spec (.of A))] [IsLocallyNoetherian X] (φ : Z ⟶ X), IsProper φ → φ ≫ (X ↘ Spec (.of A)) = (Z ↘ Spec (.of A)) → ∀ {E : X.Modules}, IsCoherent E → ∀ {S : ℕ → Subobject E}, ClosedSys I E S → PropSupp A (S 0) → PropSupp A (pullSys I φ E S 0) := by
  first | exact @GlobalTheory.CompanionTheory.GE.PullSupp.propSupp_pullSys | exact GlobalTheory.CompanionTheory.GE.PullSupp.propSupp_pullSys | (intros; apply GlobalTheory.CompanionTheory.GE.PullSupp.propSupp_pullSys <;> assumption)
