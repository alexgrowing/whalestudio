import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PushforwardSystemAffineSections
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PowIdeal
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pushforward_system_affine_sections : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X Z : Scheme.{0}} [X.Over (Spec (.of A))] [Z.Over (Spec (.of A))] [IsLocallyNoetherian X] (φ : Z ⟶ X), φ ≫ (X ↘ Spec (.of A)) = (Z ↘ Spec (.of A)) → ∀ {E : X.Modules}, IsCoherent E → ∀ {S : ℕ → Subobject E}, ClosedSys I E S → ∀ (B : Subobject ((Scheme.Modules.pullback φ).obj E)), (∀ e, B ⊔ powSub I _ (e + 1) = pullSys I φ E S e) → ∀ (V : X.Opens), IsAffineOpen V → ∀ x ∈ secs (adjKer φ B) V, ∀ n, ChartIn φ V (secsSub (S n) V) x := by
  first | exact @GlobalTheory.CompanionTheory.GE.Chart.chartIn_adjKer | exact GlobalTheory.CompanionTheory.GE.Chart.chartIn_adjKer | (intros; apply GlobalTheory.CompanionTheory.GE.Chart.chartIn_adjKer <;> assumption)
