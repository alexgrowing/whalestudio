import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemUnitaryRationalPointsOfFrameImagesRational
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLv
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_unitaryRationalPoints_of_frameImages_rational : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ → ∀ (g : GAd σ J) (C' D' : Matrix (Fin n) (Fin j) E) (Z' : Matrix (Fin n) (Fin m) E), (matHom _ σ J g).1 * adMat F C = adMat F C' → (matHom _ σ J g).1 * adMat F Z = adMat F Z' → (matHom _ σ J g).1 * adMat F D = adMat F D' → g ∈ ratPts σ J := by
  first | exact @GlobalTheory.SphEis.mem_ratPts_of_cols_rat | exact GlobalTheory.SphEis.mem_ratPts_of_cols_rat | (intros; apply GlobalTheory.SphEis.mem_ratPts_of_cols_rat <;> assumption)
