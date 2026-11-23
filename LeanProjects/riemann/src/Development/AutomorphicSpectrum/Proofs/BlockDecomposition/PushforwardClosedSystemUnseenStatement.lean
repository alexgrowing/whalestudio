import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PushforwardClosedSystemAuxiliary
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PowIdeal
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pushforward_closed_system_auxiliary : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] {X Z : Scheme.{0}} [X.Over (Spec (.of A))] [Z.Over (Spec (.of A))] [IsSeparated (X ↘ Spec (.of A))] [LocallyOfFiniteType (X ↘ Spec (.of A))] [QuasiCompact (X ↘ Spec (.of A))] (φ : Z ⟶ X), IsProper φ → φ ≫ (X ↘ Spec (.of A)) = (Z ↘ Spec (.of A)) → ∀ {E : X.Modules} (B : Subobject ((Scheme.Modules.pullback φ).obj E)), PropSupp A B → PropSupp A (adjKer φ B) := by
  first | exact @GlobalTheory.CompanionTheory.GE.KerSupp.propSupp_adjKer | exact GlobalTheory.CompanionTheory.GE.KerSupp.propSupp_adjKer | (intros; apply GlobalTheory.CompanionTheory.GE.KerSupp.propSupp_adjKer <;> assumption)
