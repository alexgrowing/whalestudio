import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProperPushforwardCoherent
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PowIdeal
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.proper_pushforward_coherent : ∀ {X Z : Scheme.{0}} [IsLocallyNoetherian X] (φ : Z ⟶ X), IsProper φ → ∀ {G : Z.Modules}, IsCoherent G → IsCoherent ((Scheme.Modules.pushforward φ).obj G) := by
  first | exact @GlobalTheory.CompanionTheory.GE.PushCoh.isCoherent_pushforward_of_isProper | exact GlobalTheory.CompanionTheory.GE.PushCoh.isCoherent_pushforward_of_isProper | (intros; apply GlobalTheory.CompanionTheory.GE.PushCoh.isCoherent_pushforward_of_isProper <;> assumption)
