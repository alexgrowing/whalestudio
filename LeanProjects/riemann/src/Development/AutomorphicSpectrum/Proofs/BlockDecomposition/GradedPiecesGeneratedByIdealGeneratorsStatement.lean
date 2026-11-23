import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedPiecesGeneratedByIdealGenerators
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistSmulHomApp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubobjectLeIffAffineSectionsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuasicoherentSupSectionsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdealPowerSubobjectSectionsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoherentSubobjectCoherentStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE GlobalTheory.CompanionTheory.GE.Step
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.graded_pieces_generated_by_ideal_generators : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{0}} [X.Over (Spec (.of A))] {P : X.Modules}, P.IsQuasicoherent → ∀ (S : ℕ → Subobject P) (hS : ClosedSys I P S) {k : ℕ} (g : Fin k → A), Ideal.span (Set.range g) = I → ∀ (hr : ∀ i, MapsDown S (toFunctions (X := X) (A := A) ⊤ (g i))) (e : ℕ) (U : X.affineOpens), Submodule.span Γ(X, U) (⋃ i, Set.range ((grT (anti hS) (hr i) e).app U)) = ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.GE.Step.span_grT_eq_top | exact GlobalTheory.CompanionTheory.GE.Step.span_grT_eq_top | (intros; apply GlobalTheory.CompanionTheory.GE.Step.span_grT_eq_top <;> assumption)
