import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubobjectLeIffAffineSections
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PowSubSuccLe
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.subobject_le_iff_affine_sections : ∀ {X : Scheme.{0}} {E : X.Modules} (S T : Subobject E), S ≤ T ↔ ∀ U : X.affineOpens, secs S (U : X.Opens) ⊆ secs T (U : X.Opens) := by
  first | exact @GlobalTheory.CompanionTheory.GE.le_iff_secs_subset | exact GlobalTheory.CompanionTheory.GE.le_iff_secs_subset | (intros; apply GlobalTheory.CompanionTheory.GE.le_iff_secs_subset <;> assumption)
