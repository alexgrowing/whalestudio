import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClosedSystemPullback
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PowIdeal
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.closed_system_pullback : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X Z : Scheme.{0}} [X.Over (Spec (.of A))] [Z.Over (Spec (.of A))] [IsLocallyNoetherian X] (φ : Z ⟶ X), φ ≫ (X ↘ Spec (.of A)) = (Z ↘ Spec (.of A)) → ∀ {E : X.Modules}, IsCoherent E → ∀ {S : ℕ → Subobject E}, ClosedSys I E S → ClosedSys I ((Scheme.Modules.pullback φ).obj E) (pullSys I φ E S) := by
  first | exact @GlobalTheory.CompanionTheory.GE.closedSys_pullSys | exact GlobalTheory.CompanionTheory.GE.closedSys_pullSys | (intros; apply GlobalTheory.CompanionTheory.GE.closedSys_pullSys <;> assumption)
