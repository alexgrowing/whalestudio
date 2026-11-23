import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.CutIdentityRightSideCongrOfSubMem
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

private theorem cycEval_add_of_finite {K : Type*} {ι : K → Type*} {R : Type*} [CommRing R]
    (φ : Ideal (MRing ι R) → ℤ) {Z₁ Z₂ : Ideal (MRing ι R) → ℤ}
    (h₁ : (Function.support Z₁).Finite) (h₂ : (Function.support Z₂).Finite) :
    cycEval φ (Z₁ + Z₂) = cycEval φ Z₁ + cycEval φ Z₂ := by
  unfold cycEval
  have f₁ : (Function.support fun W => Z₁ W * φ W).Finite :=
    h₁.subset fun W hW h0 => hW (by simp [h0])
  have f₂ : (Function.support fun W => Z₂ W * φ W).Finite :=
    h₂.subset fun W hW h0 => hW (by simp [h0])
  rw [← finsum_add_distrib f₁ f₂]
  refine finsum_congr fun W => ?_
  simp only [Pi.add_apply]
  ring

theorem RightSideMultiplicativeInForm.proof (h₁ : DivCycleMul.Statement.{u})
    (h₂ : DivCycleFiniteSupport.Statement.{u}) : RightSideMultiplicativeInForm.Statement.{u} := by
  intro O _ _ _ ϖ _ K _ _ ι _ P d hP b f g s₁ s₂ hs₁ hs₂ L
  have hPp : P.IsPrime := hP.multiProj.isPrime
  unfold cutIdentityRightSide
  rw [h₁ O K ι P s₁ s₂ hPp hs₁ hs₂]
  exact cycEval_add_of_finite _ (h₂ O K ι P s₁) (h₂ O K ι P s₂)

end

end GroundTheory.Heights₂.Heights.NumbersDVR
