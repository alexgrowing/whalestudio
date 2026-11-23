import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanOrbitExpEigenvector
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CcGASmoothAndRderMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaxCompactConjugate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoordsSecondKindFormPreservingGroup
open scoped TensorProduct Matrix
open NumberField Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedean_orbit_exp_eigenvector : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (x : Fin n → E), x ≠ 0 → ∀ (w : InfinitePlace F) (τ : EmbOver E w) (Z : Matrix (Fin n) (Fin n) ℂ) (l : ℂ),
      Z *ᵥ (fun i => τ.1 (x i)) = l • (fun i => τ.1 (x i)) → ∀ (t : ℝ) (y : GArch σ J w), GlobalTheory.Orb.archMat σ J τ y = NormedSpace.exp (t • Z) →
      ∃ a : AF F ⊗[F] E, (matHom _ σ J (embArch σ J w y)).1 *ᵥ (fun i => inclR (F := F) (AF F) (x i)) = a • fun i => inclR (F := F) (AF F) (x i) := by
  first | exact @GlobalTheory.StabLine.mulVec_embArch_eq_smul | exact GlobalTheory.StabLine.mulVec_embArch_eq_smul | (intros; apply GlobalTheory.StabLine.mulVec_embArch_eq_smul <;> assumption)
