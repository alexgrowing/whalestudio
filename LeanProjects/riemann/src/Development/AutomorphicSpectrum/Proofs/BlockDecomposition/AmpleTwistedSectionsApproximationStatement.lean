import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AmpleTwistedSectionsApproximation
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformVanishing
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ample_twisted_sections_approximation : UniformGen → ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{0}} [X.Over (Spec (.of A))] [IsProper (X ↘ Spec (.of A))] (H : ReciprocityTheory.ChartRestriction.G.Semi.LB X), GlobalTheory.IsAmpleLB H → ∀ {P : X.Modules}, IsCoherent P → ∀ S : ℕ → Subobject P, ClosedSys I P S → ∃ n₁ : ℤ, ∀ n, n₁ ≤ n → ∀ e, ∀ x ∈ twSecs H n (S e), ∃ y ∈ twSecs H n (S (e + 1)), x - y ∈ twPow I H n P (e + 1) := by
  first | exact @GlobalTheory.CompanionTheory.GE.Step.step_uniform | exact GlobalTheory.CompanionTheory.GE.Step.step_uniform | (intros; apply GlobalTheory.CompanionTheory.GE.Step.step_uniform <;> assumption)
