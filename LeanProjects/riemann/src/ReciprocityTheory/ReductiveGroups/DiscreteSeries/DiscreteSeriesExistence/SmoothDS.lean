import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.SmoothBr

noncomputable section

open Finset Matrix
open scoped ContDiff

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem IsSmoothVecU.dS (hσ : IsURepOn (UJset ε) σ) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) {v : H}
    (hv : IsSmoothVecU ε σ v) : IsSmoothVecU ε σ (dS σ X v) := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hv g₀ hg₀
  refine ⟨U, fun g => fderiv ℝ F g (g * X), hU, hgU, ?_, ?_⟩
  · have h2 : ContDiffOn ℝ ∞ (fun g : Matrix (Fin n) (Fin n) ℂ => g * X) U :=
      (LinearMap.toContinuousLinearMap (LinearMap.mulRight ℝ X)).contDiff.contDiffOn
    exact ((contDiffOn_infty_iff_fderiv_of_isOpen hU).1 hF).2.clm_apply h2
  · intro g hg hgJ
    dsimp only
    rw [smBr_orbit hσ hX hv hgJ]
    exact smBr_rdExt _ F U g X hU hg hgJ hF hfF hX

end ReciprocityTheory.ChartRestriction.DS
