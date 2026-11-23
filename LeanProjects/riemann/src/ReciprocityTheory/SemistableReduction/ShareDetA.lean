import ReciprocityTheory.L2DbarEstimates.IsLocalHomeomorph
import ReciprocityTheory.AnalyticForms.AnalyticCharts.Osgood

noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

open Matrix Filter Topology Set

theorem analyticOnNhd_V_of_differentiableOn {n : ℕ} {f : ReciprocityTheory.L2DbarEstimates.V n → ℂ}
    {B : Set (ReciprocityTheory.L2DbarEstimates.V n)} (hB : IsOpen B) (hf : DifferentiableOn ℂ f B) :
    AnalyticOnNhd ℂ f B := by
  intro x hx
  let e : ReciprocityTheory.L2DbarEstimates.V n ≃L[ℂ] (Fin n → ℂ) := EuclideanSpace.equiv (Fin n) ℂ
  have hU : IsOpen (e.symm ⁻¹' B) := hB.preimage e.symm.continuous
  have hg : DifferentiableOn ℂ (f ∘ e.symm) (e.symm ⁻¹' B) :=
    hf.comp e.symm.differentiable.differentiableOn (fun y hy => hy)
  have ha := ReciprocityTheory.AnForm.Osgood.osgood n _ _ hU hg (e x) (by simpa using hx)
  have hfe : f = (f ∘ e.symm) ∘ e := by ext y; simp
  rw [hfe]
  exact ha.comp ((e : ReciprocityTheory.L2DbarEstimates.V n →L[ℂ] (Fin n → ℂ)).analyticAt x)

theorem differentiableOn_finset_prod' {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {ι : Type*} [DecidableEq ι] {F : ι → E → ℂ} {B : Set E}
    (hF : ∀ i, DifferentiableOn ℂ (F i) B) (s : Finset ι) :
    DifferentiableOn ℂ (fun v => ∏ i ∈ s, F i v) B := by
  induction s using Finset.induction_on with
  | empty => simpa using differentiableOn_const (1 : ℂ)
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    exact (hF a).mul ih

theorem differentiableOn_det_of {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {U : Type} [Fintype U] [DecidableEq U] {F : U → U → E → ℂ} {B : Set E}
    (hF : ∀ a b, DifferentiableOn ℂ (F a b) B) :
    DifferentiableOn ℂ (fun v => (Matrix.of fun a b => F a b v).det) B := by
  simp only [Matrix.det_apply', Matrix.of_apply]
  refine DifferentiableOn.fun_sum fun σ _ => ?_
  exact (differentiableOn_const _).mul
    (differentiableOn_finset_prod' (F := fun i v => F (σ i) i v) (fun i => hF _ _) _)

end ReciprocityTheory.MultiplicativeHeights
