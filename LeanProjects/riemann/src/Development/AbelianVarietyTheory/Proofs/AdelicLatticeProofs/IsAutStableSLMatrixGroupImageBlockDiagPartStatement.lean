import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsAutStableSLMatrixGroupImageBlockDiagPart
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isAutStableSLMatrixGroup_image_blockDiagPart : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)) (e : Matrix ι ι ℚ), IsPre Γ → e * e = e → (∀ g ∈ Γ, (1 - e.map (algebraMap ℚ ℂ)) * g * e.map (algebraMap ℚ ℂ) = 0) → IsPre (blk e '' Γ) := by
  first | exact @GlobalTheory.ClassFin.isPre_blk_image | exact GlobalTheory.ClassFin.isPre_blk_image | (intros; apply GlobalTheory.ClassFin.isPre_blk_image <;> assumption)
