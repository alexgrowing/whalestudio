import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittFrameLineCosetRepresentatives
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreConcl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTransv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLineReps
open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.EisRes
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wittFrame_line_coset_representatives : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E),
    IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y →
    ∀ T : Set (ratPts σ J), (∀ γ : ratPts σ J, ∃! t, t ∈ T ∧ ∃ l : (AF F ⊗[F] E)ˣ,
        (matHom _ σ J (γ * t⁻¹ : ratPts σ J).1).1 * adMat F (col0 X) = l.1 • adMat F (col0 X)) →
    ∀ z : Fin n → E, z ≠ 0 → hE σ J z z = 0 →
      ∃ t ∈ T, ∃ c : E, c ≠ 0 ∧
        (matHom _ σ J (t : GAd σ J)⁻¹).1 *ᵥ GlobalTheory.EisMidHt.adVec F (GlobalTheory.EisMidHt.firstColumn X) = GlobalTheory.EisMidHt.adVec F (c • z) := by
  first | exact @GlobalTheory.IsoLineCarry.main | exact GlobalTheory.IsoLineCarry.main | (intros; apply GlobalTheory.IsoLineCarry.main <;> assumption)
