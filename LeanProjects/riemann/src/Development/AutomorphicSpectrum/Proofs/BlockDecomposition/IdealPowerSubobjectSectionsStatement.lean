import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdealPowerSubobjectSections
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PowSubSuccLe
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ideal_power_subobject_sections : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{0}} [X.Over (Spec (.of A))] (E : X.Modules), E.IsQuasicoherent → ∀ (n : ℕ) (V : X.Opens), IsAffineOpen V → secs (powSub I E n) V = ((Ideal.map (toFunctions (A := A) V) (I ^ n) • ⊤ : Submodule Γ(X, V) Γ(E, V)) : Set Γ(E, V)) := by
  first | exact @GlobalTheory.CompanionTheory.GE.secs_powSub | exact GlobalTheory.CompanionTheory.GE.secs_powSub | (intros; apply GlobalTheory.CompanionTheory.GE.secs_powSub <;> assumption)
