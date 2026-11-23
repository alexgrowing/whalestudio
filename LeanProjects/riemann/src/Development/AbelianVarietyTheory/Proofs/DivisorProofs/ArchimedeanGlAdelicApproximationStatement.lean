import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanGlAdelicApproximation
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreConcl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTransv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLineReps
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLatticeZeroTorus
open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.EisRes GlobalTheory.EisRestrict
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedean_gl_adelic_approximation : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (m : ℕ)
    (g : ∀ w : InfinitePlace F, GL (Fin m) (w.Completion ⊗[F] E)),
    ∃ a₀ : GL (Fin m) (AF F ⊗[F] E), ∀ w, Formalism.UG.bc (compInf F E w) a₀ = g w := by
  first | exact @GlobalTheory.adelic_gl_prescribed_infinite | exact GlobalTheory.adelic_gl_prescribed_infinite | (intros; apply GlobalTheory.adelic_gl_prescribed_infinite <;> assumption)
