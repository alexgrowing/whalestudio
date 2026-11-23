import Formalism.LocalToGlobal.IndefiniteReal.SobolevIteration.TotalDegreeBindLe

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Mult
  MeasureTheory Matrix Filter Topology

namespace Formalism.IndefR.Tow.SobPf

namespace KFin

theorem avgKFin_holds : AvgKFin := by
  intro n H _ _ _ G s π hs hπ μ hμ q w
  classical
  have := hμ.1
  set N := q.totalDegree with hN
  let e : (Var n →₀ ℕ) → H := fun m => ∫ k, evP (MvPolynomial.monomial m 1) k • π (Matrix.of k) w ∂μ
  let W : Submodule ℂ H := Submodule.span ℂ (e '' Mon n N)
  have hfin : FiniteDimensional ℂ W := FiniteDimensional.span_of_finite ℂ ((finite_Mon n N).image e)
  have hmemW : ∀ q' : MvPolynomial (Var n) ℂ, q'.totalDegree ≤ N →
      (∫ k, evP q' k • π (Matrix.of k) w ∂μ) ∈ W := by
    intro q' hq'
    have hint : ∀ m : Var n →₀ ℕ,
        Integrable (fun k => evP (MvPolynomial.monomial m 1) k • π (Matrix.of k) w) μ :=
      fun m => integrable_avg hs hπ hμ (continuous_evP _) w
    have e1 : (fun k => evP q' k • π (Matrix.of k) w) = fun k => ∑ m ∈ q'.support,
        q'.coeff m • (evP (MvPolynomial.monomial m 1) k • π (Matrix.of k) w) := by
      funext k
      rw [evalMatrix_eq_sum_monomial q' k, Finset.sum_smul]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [mul_smul]
    have hint' : ∀ m ∈ q'.support, Integrable
        (fun k => q'.coeff m • (evP (MvPolynomial.monomial m 1) k • π (Matrix.of k) w)) μ :=
      fun m _ => (hint m).smul (q'.coeff m)
    rw [e1, integral_finset_sum _ hint']
    refine Submodule.sum_mem _ fun m hm => ?_
    rw [integral_smul]
    refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, ?_, rfl⟩)
    exact (MvPolynomial.le_totalDegree hm).trans hq'
  refine ⟨W, hfin, hmemW q le_rfl, ?_⟩
  intro k₀ hk₀ x hx
  have hG := det_G_unit hs
  have hk₀d := det_UH_unit hG hk₀.1
  have key : ∀ q' : MvPolynomial (Var n) ℂ, π k₀ (∫ k, evP q' k • π (Matrix.of k) w ∂μ) =
      ∫ k, evP (MvPolynomial.bind₁ (subst k₀⁻¹) q') k • π (Matrix.of k) w ∂μ := by
    intro q'
    rw [← ContinuousLinearMap.integral_comp_comm _ (integrable_avg hs hπ hμ (continuous_evP _) w)]
    have hT : Continuous fun k : Fin n → Fin n → ℂ => Matrix.of.symm (k₀ * Matrix.of k) :=
      (continuous_const.matrix_mul continuous_id : Continuous fun k : Matrix (Fin n) (Fin n) ℂ => k₀ * k)
    let F : (Fin n → Fin n → ℂ) → H := fun k' =>
      evP (MvPolynomial.bind₁ (subst k₀⁻¹) q') k' • π (Matrix.of k') w
    have hFm : AEStronglyMeasurable F (μ.map fun k => Matrix.of.symm (k₀ * Matrix.of k)) := by
      rw [hμ.2.2.1 k₀ hk₀]; exact (integrable_avg hs hπ hμ (continuous_evP _) w).1
    have h1 : ∫ k', F k' ∂μ = ∫ k, F (Matrix.of.symm (k₀ * Matrix.of k)) ∂μ := by
      conv_lhs => rw [← hμ.2.2.1 k₀ hk₀]
      exact integral_map hT.aemeasurable hFm
    show _ = ∫ k', F k' ∂μ
    rw [h1]
    refine integral_congr_ae ?_
    filter_upwards [hμ.2.1] with k hk
    simp only [F]
    rw [evalMatrix_bind₁_mulLeft, Equiv.apply_symm_apply, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hk₀d, Matrix.one_mul,
      Equiv.symm_apply_apply, hπ.2.1 _ hk₀.1 _ hk.1, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.map_smul]
  have hstep : ∀ m ∈ Mon n N, π k₀ (e m) ∈ W := by
    intro m hm
    show π k₀ (∫ k, evP (MvPolynomial.monomial m 1) k • π (Matrix.of k) w ∂μ) ∈ W
    rw [key]
    refine hmemW _ ((totalDegree_bind_le _ _).trans ?_)
    rw [MvPolynomial.totalDegree_monomial m one_ne_zero]
    exact hm
  have hle : W ≤ W.comap (π k₀ : H →ₗ[ℂ] H) := by
    show Submodule.span ℂ (e '' Mon n N) ≤ _
    rw [Submodule.span_le]
    rintro _ ⟨m, hm, rfl⟩
    exact hstep m hm
  exact hle hx

end KFin

theorem avgKFin_holds : AvgKFin := KFin.avgKFin_holds

end Formalism.IndefR.Tow.SobPf

end
