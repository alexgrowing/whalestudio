import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsLattice
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StandardLatticeVecIndep
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open NumberField TensorProduct

noncomputable section

variable {K : Type} [Field K] [NumberField K]

theorem fibreNorm_one_tmul (E : HermitianBundle.{0} K) (σ : K →+* ℂ) (v : E.carrier) :
    fibreNorm E σ ((1 : ComplexAt σ) ⊗ₜ[𝓞 K] v) = ‖fibreVec E.metric σ v‖ :=
  rfl

def ShortFamily.toSmallFamily {E : HermitianBundle.{0} K} {lam : (K →+* ℂ) → ℝ}
    (F : ShortFamily E lam) : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel.SmallFamily E lam where
  vec := F.vec
  indep := F.linearIndependent
  norm_le σ i := by
    rw [← fibreNorm_one_tmul]
    exact F.norm_le σ i

def ShortFamily.ofSmallFamily {E : HermitianBundle.{0} K} {lam : (K →+* ℂ) → ℝ}
    (F : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel.SmallFamily E lam) : ShortFamily E lam where
  vec := F.vec
  linearIndependent := F.indep
  norm_le σ i := by
    rw [fibreNorm_one_tmul]
    exact F.norm_le σ i

def shortFamilyEquivSmallFamily (E : HermitianBundle.{0} K) (lam : (K →+* ℂ) → ℝ) :
    ShortFamily E lam ≃ GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel.SmallFamily E lam where
  toFun := ShortFamily.toSmallFamily
  invFun := ShortFamily.ofSmallFamily
  left_inv _ := rfl
  right_inv _ := rfl

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
