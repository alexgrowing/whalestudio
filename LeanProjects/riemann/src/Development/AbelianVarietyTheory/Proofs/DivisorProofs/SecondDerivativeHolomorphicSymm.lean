import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarAddVectorScalar
import ReciprocityTheory.AnalyticForms.AnalyticCharts.Osgood
open Matrix Set Filter Topology
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm GlobalTheory.TorsionForm.Pullback
open scoped ContDiff

namespace GlobalTheory

theorem analyticAt_of_eventually_differentiableAt_fin
    {E E' : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup E'] [NormedSpace ℂ E'] [FiniteDimensional ℂ E']
    (φ : E' → E) (b : E') (h : ∀ᶠ c in 𝓝 b, DifferentiableAt ℂ φ c) : AnalyticAt ℂ φ b := by
  obtain ⟨U, hUb, hU⟩ := h.exists_mem
  obtain ⟨V, hVU, hVo, hbV⟩ := mem_nhds_iff.mp hUb
  let e' : E' ≃L[ℂ] (Fin (Module.finrank ℂ E') → ℂ) :=
    (Module.finBasis ℂ E').equivFun.toContinuousLinearEquiv
  let e : E ≃L[ℂ] (Fin (Module.finrank ℂ E) → ℂ) :=
    (Module.finBasis ℂ E).equivFun.toContinuousLinearEquiv
  have hV' : IsOpen (e'.symm ⁻¹' V) := hVo.preimage e'.symm.continuous
  have hcoord : ∀ i, AnalyticAt ℂ (fun x => e (φ (e'.symm x)) i) (e' b) := by
    intro i
    refine ReciprocityTheory.AnForm.Osgood.osgood _ _ _ hV' ?_ (e' b) (by simpa using hbV)
    intro x hx
    have h1 : DifferentiableAt ℂ φ (e'.symm x) := hU _ (hVU hx)
    have h2 : DifferentiableAt ℂ (fun x => e (φ (e'.symm x))) x :=
      e.differentiableAt.comp x (h1.comp x e'.symm.differentiableAt)
    exact (differentiableAt_apply i _ |>.comp x h2).differentiableWithinAt
  have hpi : AnalyticAt ℂ (fun x => e (φ (e'.symm x))) (e' b) := analyticAt_pi_iff.mpr hcoord
  have h1 : AnalyticAt ℂ (fun x => e (φ (e'.symm x)) ) (e'.toContinuousLinearMap b) := hpi
  have hcomp := (e.symm.toContinuousLinearMap.analyticAt _).comp
      (h1.comp (e'.toContinuousLinearMap.analyticAt b))
  have heq : (⇑e.symm.toContinuousLinearMap ∘ (fun x => e (φ (e'.symm x))) ∘
      ⇑e'.toContinuousLinearMap) = φ := by
    funext y; simp
  rwa [heq] at hcomp

theorem fderiv_fderiv_apply_symm_of_eventually_differentiableAt
    {E E' : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup E'] [NormedSpace ℂ E'] [FiniteDimensional ℂ E']
    (φ : E' → E) (b v w : E') (h : ∀ᶠ c in 𝓝 b, DifferentiableAt ℂ φ c) :
    fderiv ℂ (fun c => fderiv ℂ φ c v) b w = fderiv ℂ (fun c => fderiv ℂ φ c w) b v := by
  have hA : AnalyticAt ℂ φ b := analyticAt_of_eventually_differentiableAt_fin φ b h
  have hC : ContDiffAt ℂ ω φ b := hA.contDiffAt
  have hS : IsSymmSndFDerivAt ℂ φ b := hC.isSymmSndFDerivAt (by simp [minSmoothness])
  have hF : DifferentiableAt ℂ (fderiv ℂ φ) b :=
    (hC.fderiv_right (m := 1) (by simp)).differentiableAt (by simp)
  have key : ∀ u, fderiv ℂ (fun c => fderiv ℂ φ c u) b = (fderiv ℂ (fderiv ℂ φ) b).flip u := by
    intro u
    rw [fderiv_clm_apply hF (differentiableAt_const u)]
    ext x; simp
  rw [key v, key w]
  simp only [ContinuousLinearMap.flip_apply]
  exact hS w v

end GlobalTheory
