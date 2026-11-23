import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.IntegralityGoodReduction

noncomputable section

open Matrix
open scoped ContDiff

namespace UpperTheory.V.Lit.Dr

theorem pullEquiv : PullEquiv := by
  intro Γ V S _ _ _ d G _ l hl q η hη γ s p hp
  have hAp : (G.ρ γ⁻¹) p ∈ G.Y := G.maps γ⁻¹ p hp
  have hBA : ∀ x, (G.ρ γ) ((G.ρ γ⁻¹) x) = x := fun x => by
    rw [← ContinuousLinearMap.mul_apply, ← map_mul, mul_inv_cancel, map_one,
      ContinuousLinearMap.one_apply]
  have hAB : ∀ x, (G.ρ γ⁻¹) ((G.ρ γ) x) = x := fun x => by
    rw [← ContinuousLinearMap.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      ContinuousLinearMap.one_apply]
  have hss : (G.σ γ) ((G.σ γ⁻¹) s) = s := by
    rw [← Equiv.Perm.mul_apply, ← map_mul, mul_inv_cancel, map_one, Equiv.Perm.one_apply]
  have hlinv : ∀ x ∈ G.Y, l s x = l ((G.σ γ⁻¹) s) ((G.ρ γ⁻¹) x) := fun x hx => by
    have h := hl.2 γ ((G.σ γ⁻¹) s) ((G.ρ γ⁻¹) x) (G.maps γ⁻¹ x hx)
    rw [hss, hBA] at h
    exact h
  have hηinv : ∀ x, (η : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s x = G.tr q γ ((η : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) ((G.σ γ⁻¹) s) ((G.ρ γ⁻¹) x)) := fun x => by
    have h := congrArg (fun w : G.Om q => (w : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s x) (hη γ)
    exact h.symm
  have hloc : (fun x => l s x • x) =ᶠ[nhds p]
      fun x => (G.ρ γ) (l ((G.σ γ⁻¹) s) ((G.ρ γ⁻¹) x) • (G.ρ γ⁻¹) x) :=
    Filter.eventuallyEq_of_mem (G.isOpen.mem_nhds hp) fun x hx => by
      rw [map_smul, hBA, hlinv x hx]
  have hdl : DifferentiableAt ℝ (l ((G.σ γ⁻¹) s)) ((G.ρ γ⁻¹) p) :=
    (((hl.1 ((G.σ γ⁻¹) s)).1).contDiffAt (G.isOpen.mem_nhds hAp)).differentiableAt (by simp)
  have hD : fderiv ℝ (fun x => l s x • x) p = (G.ρ γ) ∘L
      (fderiv ℝ (fun y => l ((G.σ γ⁻¹) s) y • y) ((G.ρ γ⁻¹) p)) ∘L (G.ρ γ⁻¹) := by
    rw [hloc.fderiv_eq]
    have h1 : HasFDerivAt (fun y => l ((G.σ γ⁻¹) s) y • y)
        (fderiv ℝ (fun y => l ((G.σ γ⁻¹) s) y • y) ((G.ρ γ⁻¹) p)) ((G.ρ γ⁻¹) p) :=
      (hdl.smul differentiableAt_id).hasFDerivAt
    exact ((G.ρ γ).hasFDerivAt.comp p (h1.comp p (G.ρ γ⁻¹).hasFDerivAt)).fderiv
  rw [pull, pull, hD, hηinv, hlinv p hp, map_smul]
  refine ContinuousAlternatingMap.ext fun v => ?_
  simp [Geo.tr, Function.comp_def, hAB]

end UpperTheory.V.Lit.Dr
