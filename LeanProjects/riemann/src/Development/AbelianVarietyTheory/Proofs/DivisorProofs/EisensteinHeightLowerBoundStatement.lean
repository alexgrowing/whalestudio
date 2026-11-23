import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisensteinHeightLowerBound
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
theorem _root_.GlobalTheory.T.eisenstein_height_lower_bound : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E) (L : Submodule (𝓞 E) (Fin n → E))
    (a : GL (Fin n) (AF F ⊗[F] E)) (h : GAd σ J → ℝ), HidaSetting σ J X Y L a h →
      ∀ s : ℝ, 2 < s → ∃ C : ℝ, ∀ y : Fin n → E, y ≠ 0 → hE σ J (GlobalTheory.EisMidHt.firstColumn X) y = 0 →
        hE σ J (GlobalTheory.EisMidHt.firstColumn Y) y = 0 →
        ∑' c : E, ENNReal.ofReal (GlobalTheory.EisMidHt.ht L a (GlobalTheory.EisMidHt.adVec F (y + c • GlobalTheory.EisMidHt.firstColumn X)) ^ (-s)) ≤
          ENNReal.ofReal C * ENNReal.ofReal (GlobalTheory.EisMidHt.ht L a (GlobalTheory.EisMidHt.adVec F y) ^ (1 - s)) := by
  first | exact @GlobalTheory.EisMidHt.tsum_ht_add_smul_le | exact GlobalTheory.EisMidHt.tsum_ht_add_smul_le | (intros; apply GlobalTheory.EisMidHt.tsum_ht_add_smul_le <;> assumption)
