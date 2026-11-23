import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoherentNoetherianMaximalSubsheaf
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GenHom
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE GlobalTheory.CompanionTheory.GE.TwGen
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coherent_noetherian_maximal_subsheaf : ∀ {X : Scheme.{0}} [IsNoetherian X] {P : X.Modules}, IsCoherent P → ∀ F : Set (Subobject P), F.Nonempty → (∀ B ∈ F, (B : X.Modules).IsQuasicoherent) → ∃ M ∈ F, ∀ B ∈ F, M ≤ B → B = M := by
  first | exact @GlobalTheory.CompanionTheory.GE.exists_maximal_qcoh_subobject | exact GlobalTheory.CompanionTheory.GE.exists_maximal_qcoh_subobject | (intros; apply GlobalTheory.CompanionTheory.GE.exists_maximal_qcoh_subobject <;> assumption)
