import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RestrictedSystemKilledByIdeal
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PowSubSuccLe
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.restricted_system_killed_by_ideal : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{0}} [X.Over (Spec (.of A))] {E : X.Modules} (J : X.IdealSheafData) (D : Subobject E) (S : ℕ → Subobject E) (c : ℕ), (∀ (n : ℕ) (U : X.affineOpens) (a : Γ(X, U)), a ∈ J.ideal U → ∀ x ∈ secs D U, a • x ∈ secs (S n) U) → ∀ e, Killed J (restrictSys I D S c e) := by
  first | exact @GlobalTheory.CompanionTheory.GE.killed_restrictSys | exact GlobalTheory.CompanionTheory.GE.killed_restrictSys | (intros; apply GlobalTheory.CompanionTheory.GE.killed_restrictSys <;> assumption)
