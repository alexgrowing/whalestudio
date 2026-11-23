import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArtinReesSubobject
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PowSubSuccLe
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.artin_rees_subobject : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{0}} [X.Over (Spec (.of A))] [IsLocallyNoetherian X] [CompactSpace X] {E : X.Modules}, IsCoherent E → ∀ D : Subobject E, (D : X.Modules).IsQuasicoherent → ∃ k : ℕ, ∀ n : ℕ, D ⊓ powSub I E (n + k) ≤ (Subobject.map D.arrow).obj (powSub I (D : X.Modules) n) := by
  first | exact @GlobalTheory.CompanionTheory.GE.artinRees_uniform | exact GlobalTheory.CompanionTheory.GE.artinRees_uniform | (intros; apply GlobalTheory.CompanionTheory.GE.artinRees_uniform <;> assumption)
