import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.ExistsCombComb
import GroundTheory.AutomorphicForms.L2LocalComponents.Summand

open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

open CuspidalSpectrum RightCosetSpace in
private theorem UpperTheory.V.Af.Smo.coeFn_tr {E : Type} [Field E] [NumberField E] {n : ℕ}
    (μ : Measure (Reduction.normOneGL E n)) [μ.IsHaarMeasure] {φ : cuspForms E n} (hφ : φ ∈ centralCuspForms E n)
    (g : AdelicGLn.AdelicGL E n) :
    (toLp μ (cuspRepT μ (toOne g) (cuspVecL μ φ)) : RightCosetSpace (Reduction.rationalGLOne E n) → ℂ)
      =ᵐ[quotientMeasure (Reduction.rationalGLOne E n) μ] quotTr φ g := by
  rw [toLp_cuspRepT, rightRegularRep_apply, toLp_cuspVecL, quotTr_eq_comp hφ, quotTr_one]
  refine (coeFn_rightTranslate _ μ _ _).trans ?_
  exact (measurePreserving_rightMul μ (toOne g)).quasiMeasurePreserving.ae_eq (coeFn_cuspToL2 μ φ)

private theorem UpperTheory.V.Af.Smo.inner_closure {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {S T : Submodule ℂ H} (h : ∀ x ∈ S, ∀ y ∈ T, inner ℂ x y = 0) {x y : H}
    (hx : x ∈ S.topologicalClosure) (hy : y ∈ T.topologicalClosure) : inner ℂ x y = 0 := by
  have h1 : T ≤ S.topologicalClosureᗮ := by
    rw [Submodule.orthogonal_closure]
    exact fun b hb => (Submodule.mem_orthogonal _ _).2 fun a ha => h a ha b hb
  exact (Submodule.mem_orthogonal _ _).1
    (Submodule.topologicalClosure_minimal T h1 (Submodule.isClosed_orthogonal _) hy) x hx

open CuspidalSpectrum RightCosetSpace in
theorem UpperTheory.V.Af.Smo.orthTr :
    UpperTheory.V.Af.Smo.OrthTr := by
  intro E _ _ n μ _ U U' hU hU' sU sU' h φ hφ φ' hφ' g g'
  have i1 := isInvariant_topologicalClosure_map μ hU sU.ρ sU.σ sU.τ
  have i2 := isInvariant_topologicalClosure_map μ hU' sU'.ρ sU'.σ sU'.τ
  have m1 := i1 (toOne g) _ (Submodule.le_topologicalClosure _ (Submodule.mem_map_of_mem (f := cuspVecL μ) hφ))
  have m2 := i2 (toOne g') _ (Submodule.le_topologicalClosure _ (Submodule.mem_map_of_mem (f := cuspVecL μ) hφ'))
  have h0 := UpperTheory.V.Af.Smo.inner_closure (by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    exact h a ha b hb) m1 m2
  have h1 : inner ℂ (toLp μ (cuspRepT μ (toOne g) (cuspVecL μ φ)))
      (toLp μ (cuspRepT μ (toOne g') (cuspVecL μ φ'))) = 0 := h0
  rw [MeasureTheory.L2.inner_def] at h1
  rw [← h1]
  refine integral_congr_ae ?_
  filter_upwards [UpperTheory.V.Af.Smo.coeFn_tr μ (hU hφ) g, UpperTheory.V.Af.Smo.coeFn_tr μ (hU' hφ') g'] with q e1 e2
  rw [e1, e2, RCLike.inner_apply']
