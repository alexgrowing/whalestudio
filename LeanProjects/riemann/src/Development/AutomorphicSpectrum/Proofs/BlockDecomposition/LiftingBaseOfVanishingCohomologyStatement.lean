import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LiftingBaseOfVanishingCohomology
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistSmulHomApp
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE GlobalTheory.CompanionTheory.GE.Step
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lifting_base_of_vanishing_cohomology : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{0}} [X.Over (Spec (.of A))] (H : ReciprocityTheory.ChartRestriction.G.Semi.LB X), H.IsLB → ∀ {P : X.Modules} (S : ℕ → Subobject P) (hS : ClosedSys I P S) (n : ℤ), Subsingleton (GlobalTheory.coh (GlobalTheory.twistZ (S 0 : X.Modules) H n) 1) → Lifts I H hS n 0 := by
  first | exact @GlobalTheory.CompanionTheory.GE.Step.lifts_zero | exact GlobalTheory.CompanionTheory.GE.Step.lifts_zero | (intros; apply GlobalTheory.CompanionTheory.GE.Step.lifts_zero <;> assumption)
