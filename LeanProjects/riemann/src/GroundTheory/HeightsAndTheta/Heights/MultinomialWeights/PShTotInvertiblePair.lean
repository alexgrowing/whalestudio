import Mathlib
import GroundTheory.HeightsAndTheta.Heights.MultinomialWeights.StatementsEnd
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.TheoremB

open MvPolynomial Finset

theorem ShTotInvertiblePair.proof (h : ShTotIndependent.Statement) :
    ShTotInvertiblePair.Statement := by
  intro d hf
  have hli := LinearIndependent.pair_iff.mp (h d hf).2
  set S : topSpace d →ₗ[ℚ] ℚ := ∑ τ : Fin d.f, shOn d τ with hS
  set T : topSpace d →ₗ[ℚ] ℚ := ∑ τ : Fin d.f, totOn d τ with hT
  have hSapp : ∀ x : topSpace d, S x = shSum d x.1 := by
    intro x
    simp [hS, LinearMap.sum_apply, shOn, shLin, shSum]
  have hTapp : ∀ x : topSpace d, T x = totSum d x.1 := by
    intro x
    simp [hT, LinearMap.sum_apply, totOn, totLin, totSum]
  by_contra hne
  push Not at hne
  have key : ∀ x y : topSpace d, S x * T y - T x * S y = 0 := by
    intro x y
    rw [hSapp, hSapp, hTapp, hTapp]
    exact hne x.1 y.1 ((mem_homogeneousSubmodule _ _).mp x.2)
      ((mem_homogeneousSubmodule _ _).mp y.2)
  obtain ⟨x, hx⟩ : ∃ x : topSpace d, S x ≠ 0 := by
    by_contra h0
    push Not at h0
    have h1 := hli 1 0 (by
      ext y
      simp [h0 y])
    exact one_ne_zero h1.1
  have h2 := hli (T x) (-(S x)) (by
    ext y
    simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, LinearMap.zero_apply]
    linear_combination -(key x y))
  exact hx (neg_eq_zero.mp h2.2)

end GroundTheory.Heights₂.Heights.TheoremB
