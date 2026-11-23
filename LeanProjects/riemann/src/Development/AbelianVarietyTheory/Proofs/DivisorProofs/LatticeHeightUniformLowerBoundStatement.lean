import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeHeightUniformLowerBound
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
theorem _root_.GlobalTheory.T.lattice_height_uniform_lower_bound : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (L : Submodule (𝓞 E) (Fin n → E)) (a : GL (Fin n) (AF F ⊗[F] E)), IsCMExt F E σ → Submodule.IsLattice E L →
      ∃ δ : ℝ, 0 < δ ∧ (∀ y : Fin n → E, y ≠ 0 → δ ≤ GlobalTheory.EisMidHt.ht L a (GlobalTheory.EisMidHt.adVec F y)) ∧
        ∀ y : Fin n → E, y ≠ 0 → ∀ w : InfinitePlace F,
          0 < GlobalTheory.EisMidHt.normInf a w (fun i => compInf F E w (GlobalTheory.EisMidHt.adVec F y i)) := by
  first | exact @GlobalTheory.EisMidHt.ht_adVec_lower_bound | exact GlobalTheory.EisMidHt.ht_adVec_lower_bound | (intros; apply GlobalTheory.EisMidHt.ht_adVec_lower_bound <;> assumption)
