import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoherentSubobjectCoherent
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PowSubSuccLe
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coherent_subobject_coherent : ∀ {X : Scheme.{0}} [IsLocallyNoetherian X] {E : X.Modules}, IsCoherent E → ∀ D : Subobject E, (D : X.Modules).IsQuasicoherent → IsCoherent (D : X.Modules) := by
  first | exact @GlobalTheory.CompanionTheory.GE.isCoherent_subobject | exact GlobalTheory.CompanionTheory.GE.isCoherent_subobject | (intros; apply GlobalTheory.CompanionTheory.GE.isCoherent_subobject <;> assumption)
