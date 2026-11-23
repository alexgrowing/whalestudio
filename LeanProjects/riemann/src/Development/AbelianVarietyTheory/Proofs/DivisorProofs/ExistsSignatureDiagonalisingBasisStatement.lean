import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSignatureDiagonalisingBasis
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CcGASmoothAndRderMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaxCompactConjugate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoordsSecondKindFormPreservingGroup
open scoped TensorProduct Matrix
open NumberField Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_signature_diagonalising_basis : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ K' : Subgroup (GAd σ J), GlobalTheory.UAut.IsMaxCpt σ J K' →
      ∀ (k : GAd σ J) (w : InfinitePlace F) (τ : EmbOver E w), ∃ (C : GL (Fin n) ℂ) (ε : Fin n → Bool),
        C.1ᴴ * J.map τ.1 * C.1 = Matrix.diagonal (fun i => if ε i then 1 else -1) ∧
        ∀ y : GArch σ J w, ((C⁻¹).1 * GlobalTheory.Orb.archMat σ J τ y * C.1)ᴴ * ((C⁻¹).1 * GlobalTheory.Orb.archMat σ J τ y * C.1) = 1 →
          k⁻¹ * embArch σ J w y * k ∈ K' := by
  first | exact @GlobalTheory.ArchFrameConj.exists_frame_mem_conj | exact GlobalTheory.ArchFrameConj.exists_frame_mem_conj | (intros; apply GlobalTheory.ArchFrameConj.exists_frame_mem_conj <;> assumption)
