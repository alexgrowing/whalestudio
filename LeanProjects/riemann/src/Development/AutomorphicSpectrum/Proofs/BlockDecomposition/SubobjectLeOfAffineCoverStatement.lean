import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubobjectLeOfAffineCover
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PowIdeal
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.subobject_le_of_affine_cover : ∀ {X : Scheme.{0}} {E : X.Modules} [E.IsQuasicoherent] (S T : Subobject E), (S : X.Modules).IsQuasicoherent → (T : X.Modules).IsQuasicoherent → ∀ {ι : Type} (V : ι → X.Opens), (∀ i, IsAffineOpen (V i)) → iSup V = ⊤ → (∀ i, secs S (V i) ⊆ secs T (V i)) → S ≤ T := by
  first | exact @GlobalTheory.CompanionTheory.GE.le_of_secs_subset_cover | exact GlobalTheory.CompanionTheory.GE.le_of_secs_subset_cover | (intros; apply GlobalTheory.CompanionTheory.GE.le_of_secs_subset_cover <;> assumption)
