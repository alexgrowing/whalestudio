import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeVectorContentIdealNormProduct
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
theorem _root_.GlobalTheory.T.lattice_vector_content_ideal_norm_product : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ)
    (L : Submodule (𝓞 E) (Fin n → E)), Submodule.IsLattice E L → ∀ u : Fin n → E, u ≠ 0 →
      ∃ I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E, I ≠ 0 ∧ (∀ c : E, c ∈ I ↔ c • u ∈ L) ∧
        ∏ᶠ v, (GlobalTheory.EisMidHt.normFin F L v (fun i => compFin F E v (GlobalTheory.EisMidHt.adVec F u i)) : ℝ) =
          (FractionalIdeal.absNorm I : ℝ) := by
  first | exact @GlobalTheory.LatHtFinPart.finprod_normFin_eq_absNorm | exact GlobalTheory.LatHtFinPart.finprod_normFin_eq_absNorm | (intros; apply GlobalTheory.LatHtFinPart.finprod_normFin_eq_absNorm <;> assumption)
