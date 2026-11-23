import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentStabilizerDoubleCoset
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreConcl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTransv
open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.EisRes
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unipotent_stabilizer_double_coset : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E),
    IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y →
    ∀ w ∈ ratPts σ J, (matHom _ σ J w).1 * adMat F (col0 Y) = adMat F (col0 X) →
    ∀ ν ∈ unipRad σ J (col0 X), ∀ t : GAd σ J, GlobalTheory.EisCT.StabL σ J (col0 X) (w * ν * t⁻¹) →
    ¬ GlobalTheory.EisCT.OrthL σ J (col0 X) t := by
  first | exact @GlobalTheory.EisCT.not_orthL_of_stabL_swap | exact GlobalTheory.EisCT.not_orthL_of_stabL_swap | (intros; apply GlobalTheory.EisCT.not_orthL_of_stabL_swap <;> assumption)
