import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuasicoherentSupSections
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PowSubSuccLe
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quasicoherent_sup_sections : ∀ {X : Scheme.{0}} {E : X.Modules}, E.IsQuasicoherent → ∀ (S T : Subobject E), (S : X.Modules).IsQuasicoherent → (T : X.Modules).IsQuasicoherent → ((S ⊔ T : Subobject E) : X.Modules).IsQuasicoherent ∧ ∀ V : X.Opens, IsAffineOpen V → secs (S ⊔ T) V = {x | ∃ s ∈ secs S V, ∃ t ∈ secs T V, x = s + t} := by
  first | exact @GlobalTheory.CompanionTheory.GE.supsecs | exact GlobalTheory.CompanionTheory.GE.supsecs | (intros; apply GlobalTheory.CompanionTheory.GE.supsecs <;> assumption)
