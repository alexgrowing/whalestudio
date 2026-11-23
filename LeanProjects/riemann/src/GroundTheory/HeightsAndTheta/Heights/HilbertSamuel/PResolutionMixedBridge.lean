import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedF
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.AMixSt
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsResolutionMixedBridge
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.AnResBridge
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.AnForm.M

noncomputable section

theorem ResolutionMixedBridge.proof : ResolutionMixedBridge.Statement := by
  intro D Ω _ _ κ _ d M m₁ hM hm₁
  have hex : ∃ Ψ : (((k : Unit) → GlobalTheory κ k) → ℂ) →ₗ[ℂ] (Fin (D + 1) → ℂ),
      IsGoodProj (coordIdeal ℤ d.x) Ψ :=
    goodProjExists Unit (GlobalTheory κ) (coordIdeal ℤ d.x) D d.arith
  set B : HermLine (GlobalTheory κ) := (HermLine.ofCone m₁).tensor (HermLine.ofCone d.m).inv with hBdef
  have hB0 : B.a = 0 := by
    funext k
    simp [B, HermLine.tensor, HermLine.inv, HermLine.ofCone]
  have hgl : logRatio d.m m₁ = logNorm B.inv 1 := by
    funext z
    rw [logNorm_inv_one]
    simp only [B, HermLine.tensor, HermLine.inv, HermLine.ofCone, logRatio, div_eq_mul_inv]
  have hBs : IsSmoothHerm B.inv :=
    isSmoothHerm_inv (isSmoothHerm_tensor (gbamix_smoothHerm_ofCone hm₁)
      (isSmoothHerm_inv (gbamix_smoothHerm_ofCone d.smooth)))
  have hsec : IsSectionOn (coordIdeal ℤ d.x) B.inv 1 := isSectionOn_inv_one d.arith.2.1.1 hB0
  have key := AnResBridge.bridge d.R hex.choose (fun j => HermLine.ofCone (M j)) B.inv 1 d.arith
    hex.choose_spec (fun j => gbamix_smoothHerm_ofCone (hM j)) hBs hsec
  unfold ptsIntegral
  rw [dif_pos hex, hgl]
  exact key

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
