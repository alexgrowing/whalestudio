import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.SecondCountableTopologyArchUnitary

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix

noncomputable section

variable {F E : Type*} [Field F] [Field E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in

theorem star_mulVec_dotProduct_mulVec_mulVec (M H : Matrix ι ι ℂ) (y z : ι → ℂ) :
    star (M *ᵥ y) ⬝ᵥ (H *ᵥ (M *ᵥ z)) = star y ⬝ᵥ ((Mᴴ * H * M) *ᵥ z) := by
  rw [star_mulVec, mulVec_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mul_assoc]

theorem ArchInvariant.proof (h : HermitianForm F E W) (v : Basis ι E W) :
    ArchInvariant.Statement h v := by
  intro g y z w
  have hmem := mem_archUnitary.mp (g⁻¹ : archUnitary h v).2 w
  set M : Matrix ι ι ℂ := (((g⁻¹ : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ)
    with hM
  have hct : (M.map (starRingEnd ℂ))ᵀ = Mᴴ := by
    ext i j
    simp [conjTranspose_apply]
  rw [hct] at hmem
  show star (M *ᵥ y w) ⬝ᵥ (gramAt h v w *ᵥ (M *ᵥ z w)) = star (y w) ⬝ᵥ (gramAt h v w *ᵥ z w)
  rw [star_mulVec_dotProduct_mulVec_mulVec, hmem]

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
