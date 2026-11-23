import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PModelFibreSumAeFibres
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

namespace ModelFibreSumAlmostEverywhere

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P : Ideal (MRing ι)} {e : ℕ}
  (M : CxModel P e) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))

theorem density_indep {L : HermLine ι} (hL : IsSmoothHerm L) (r : ℝ)
    {γ γ' : (Fin e → ℂ) → (Σ k, ι k) → ℂ} {y : Fin e → ℂ}
    (hγ : AnalyticAt ℂ γ y) (hγ' : AnalyticAt ℂ γ' y) (hy : ∀ k, ∃ i, γ y ⟨k, i⟩ ≠ 0)
    (hseg : (fun y' => segre (γ y')) =ᶠ[𝓝 y] fun y' => segre (γ' y')) :
    maDensity (fun (_ : Fin e) y' => r * Real.log (L.h (γ y'))) y =
      maDensity (fun (_ : Fin e) y' => r * Real.log (L.h (γ' y'))) y := by
  choose i0 hi0 using hy
  set c : K → (Fin e → ℂ) → ℂ := fun k y' => γ' y' ⟨k, i0 k⟩ / γ y' ⟨k, i0 k⟩ with hc_def
  have hcont : ∀ᶠ y' in 𝓝 y, ∀ k, γ y' ⟨k, i0 k⟩ ≠ 0 :=
    eventually_all.mpr fun k => (analyticAt_coord hγ ⟨k, i0 k⟩).continuousAt.eventually_ne (hi0 k)
  have hrel : ∀ᶠ y' in 𝓝 y, (∀ k, c k y' ≠ 0) ∧ γ' y' = bsmul (fun k => c k y') (γ y') := by
    filter_upwards [hcont, hseg] with y' h1 h2
    obtain ⟨h3, h4⟩ := eq_bsmul_of_segre_eq i0 h1 h2
    exact ⟨fun k => div_ne_zero (h3 k) (h1 k), h4⟩
  obtain ⟨hc0, -⟩ := hrel.self_of_nhds
  have hcan : ∀ k, AnalyticAt ℂ (c k) y := fun k =>
    (analyticAt_coord hγ' ⟨k, i0 k⟩).div (analyticAt_coord hγ ⟨k, i0 k⟩) (hi0 k)
  have hH : cxHessian (fun y' => r * Real.log (L.h (γ' y'))) y =
      cxHessian (fun y' => r * Real.log (L.h (γ y'))) y := by
    set G : (Fin e → ℂ) → ℂ := fun y' => ∑ k, ((r * (L.a k : ℝ) : ℝ) : ℂ) * Complex.log (c k y' / c k y)
    set C : ℝ := ∑ k, r * (L.a k : ℝ) * Real.log ‖c k y‖
    have hGan : AnalyticAt ℂ G y := by
      refine Finset.analyticAt_fun_sum _ fun k _ => analyticAt_const.mul ?_
      refine ((hcan k).div analyticAt_const (hc0 k)).clog ?_
      show c k y / c k y ∈ Complex.slitPlane
      rw [div_self (hc0 k)]
      exact Complex.one_mem_slitPlane
    have heq : (fun y' => r * Real.log (L.h (γ' y'))) =ᶠ[𝓝 y]
        fun y' => r * Real.log (L.h (γ y')) + (G y').re + C := by
      filter_upwards [hrel, hcont] with y' ⟨hc, hr⟩ hγ0
      have hpos : 0 < L.h (γ y') := L.pos _ fun k => ⟨i0 k, hγ0 k⟩
      have hsm : L.h (bsmul (fun k => c k y') (γ y')) = (∏ k, ‖c k y'‖ ^ L.a k) * L.h (γ y') :=
        L.smul _ _ hc
      have hne : ∀ k, ‖c k y'‖ ^ L.a k ≠ 0 := fun k => zpow_ne_zero _ (norm_ne_zero_iff.mpr (hc k))
      have hterm : ∀ k, ((((r * (L.a k : ℝ)) : ℝ) : ℂ) * Complex.log (c k y' / c k y)).re =
          r * (L.a k : ℝ) * Real.log ‖c k y'‖ - r * (L.a k : ℝ) * Real.log ‖c k y‖ := by
        intro k
        rw [Complex.re_ofReal_mul, Complex.log_re, norm_div,
          Real.log_div (norm_ne_zero_iff.mpr (hc k)) (norm_ne_zero_iff.mpr (hc0 k)), mul_sub]
      simp only [G, C]
      rw [hr, hsm, Real.log_mul (Finset.prod_ne_zero_iff.mpr fun k _ => hne k) hpos.ne',
        Real.log_prod (fun k _ => hne k), Complex.re_sum]
      simp only [Real.log_zpow, hterm, Finset.sum_sub_distrib]
      rw [mul_add, Finset.mul_sum]
      simp only [← mul_assoc]
      ring
    rw [cxHessian_congr heq, cxHessian_add_re (φ := fun y' => r * Real.log (L.h (γ y'))) C
      (contDiffAt_const.mul (pot_contDiffAt hL hγ fun k => ⟨i0 k, hi0 k⟩)) hGan]
  simp only [maDensity, hH]

theorem exists_sheet (L : HermLine ι) (r : ℝ) (E : Set M.Xc) (hP : IsArithVar P (e + 1))
    (hL : IsSmoothHerm L) (x : M.Xc) (hx : x ∉ modelBad M Ψ E) :
    ∃ γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ, IsSheet P Ψ (modelQ M Ψ x) (modelW M Ψ x) γ ∧
      maDensity (fun (_ : Fin e) y' => r * Real.log (L.h (γ y'))) (modelQ M Ψ x) =
        pushDens M.atlas (fun _ => modelPot M L r) (modelQ M Ψ) x := by
  classical
  obtain ⟨k0⟩ := hP.1
  have hPh : IsMultiHomogIdeal P := hP.2.1.2.1
  set j := chartIdx M.atlas x with hjdef
  have hj : x ∈ (M.atlas.chart j).source := Classical.choose_spec (M.atlas.cover x)
  set u := M.atlas.chart j x with hudef
  have hsu : (M.atlas.chart j).symm u = x := (M.atlas.chart j).left_inv hj
  have huU : u ∈ (M.atlas.chart j).target ∩ (M.atlas.chart j).symm ⁻¹' modelU M x :=
    ⟨(M.atlas.chart j).map_source hj, by rw [Set.mem_preimage, hsu]; exact mem_modelU M x⟩
  obtain ⟨hQa, hQd⟩ := modelQ_good_of_notMem M Ψ E x hx j hj
  set Q := modelQ M Ψ ∘ (M.atlas.chart j).symm with hQdef
  set Df := fderiv ℂ Q u with hDf
  have hdet : Df.det ≠ 0 := hQd
  set Ce := Df.toContinuousLinearEquivOfDetNeZero hdet with hCe
  have hCe' : (Ce : (Fin e → ℂ) →L[ℂ] (Fin e → ℂ)) = Df :=
    ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero Df hdet
  have hstrict : HasStrictFDerivAt Q (Ce : (Fin e → ℂ) →L[ℂ] (Fin e → ℂ)) u := by
    rw [hCe']; exact hQa.hasStrictFDerivAt
  set F := hstrict.toOpenPartialHomeomorph Q with hF
  have hFc : (F : (Fin e → ℂ) → (Fin e → ℂ)) = Q := hstrict.toOpenPartialHomeomorph_coe
  have hus : u ∈ F.source := hstrict.mem_toOpenPartialHomeomorph_source
  have hyt : Q u ∈ F.target := hstrict.image_mem_toOpenPartialHomeomorph_target
  have hσu : F.symm (Q u) = u := by
    have := F.left_inv hus
    rwa [hFc] at this
  have hy0 : Q u = modelQ M Ψ x := by simp only [hQdef, Function.comp_apply, hsu]
  have hσa : AnalyticAt ℂ F.symm (Q u) := by
    refine F.analyticAt_symm (i := Ce) hyt ?_ ?_
    · rw [hσu, hFc]; exact hQa
    · rw [hσu, hFc, hCe']
  have hσd : HasFDerivAt F.symm (Ce.symm : (Fin e → ℂ) →L[ℂ] (Fin e → ℂ)) (Q u) := by
    refine F.hasFDerivAt_symm hyt ?_
    rw [hσu, hFc, hCe']
    exact hQa.differentiableAt.hasFDerivAt
  set γ₀ : (Fin e → ℂ) → (Σ k, ι k) → ℂ :=
    fun y' => modelLift M x ((M.atlas.chart j).symm (F.symm y')) with hγ₀
  have hγ₀a : AnalyticAt ℂ γ₀ (Q u) := (analyticAt_lift_chart M x j huU).comp_of_eq hσa hσu
  have hγ₀u : γ₀ (Q u) = modelLift M x x := by simp only [hγ₀, hσu, hsu]
  set ψ0 : (Fin e → ℂ) → ℂ := fun y' => Ψ (segre (γ₀ y')) 0 with hψ0
  have hψ0a : AnalyticAt ℂ ψ0 (Q u) :=
    analyticAt_pi_iff.mp ((analyticAt_segre_lift M Ψ x j huU).comp_of_eq hσa hσu) 0
  have hψ0u : ψ0 (Q u) ≠ 0 := by
    simp only [hψ0, hγ₀u]; exact psi_zero_ne_of_not_mem_bad M Ψ hx
  set c : (Fin e → ℂ) → K → ℂ := fun y' => Function.update (fun _ => (1 : ℂ)) k0 (ψ0 y')⁻¹
    with hcdef
  have hc_ne : ∀ y', ψ0 y' ≠ 0 → ∀ k, c y' k ≠ 0 := by
    intro y' h k
    by_cases hk : k = k0
    · subst hk; simp [hcdef, h]
    · simp [hcdef, Function.update_of_ne hk]
  have hca : ∀ k, AnalyticAt ℂ (fun y' => c y' k) (Q u) := by
    intro k
    by_cases hk : k = k0
    · subst hk; simp only [hcdef, Function.update_self]; exact hψ0a.inv hψ0u
    · simp only [hcdef, Function.update_of_ne hk]; exact analyticAt_const
  set γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ := fun y' => bsmul (c y') (γ₀ y') with hγdef
  have hγa : AnalyticAt ℂ γ (Q u) :=
    analyticAt_pi_iff.mpr fun p => (hca p.1).mul (analyticAt_pi_iff.mp hγ₀a p)
  have hprod : ∀ y', ∏ k, c y' k = (ψ0 y')⁻¹ := fun y' => by
    simp [hcdef, Finset.prod_update_of_mem (Finset.mem_univ k0)]
  have hseg : ∀ y', segre (γ y') = (ψ0 y')⁻¹ • segre (γ₀ y') := fun y' => by
    rw [← hprod y']; exact segre_smul (c y') (γ₀ y')
  refine ⟨γ, ⟨?_, ?_⟩, ?_⟩
  · rw [← hy0, hseg]
    simp only [hψ0, hγ₀u]
    rfl
  · rw [← hy0]
    have hU : ∀ᶠ y' in 𝓝 (Q u),
        F.symm y' ∈ (M.atlas.chart j).target ∩ (M.atlas.chart j).symm ⁻¹' modelU M x :=
      hσa.continuousAt.preimage_mem_nhds (by
        rw [hσu]; exact ((M.atlas.chart j).isOpen_inter_preimage_symm (modelU_isOpen M x)).mem_nhds huU)
    filter_upwards [hγa.eventually_analyticAt, hU, F.open_target.mem_nhds hyt,
      hψ0a.continuousAt.eventually_ne hψ0u] with y' ha hUy ht h0
    refine ⟨ha.differentiableAt,
      mcPts_smul hPh (c y') (hc_ne y' h0) ((modelLift_spec M x).1 _ hUy.2).1, ?_⟩
    have hq : Q (F.symm y') = y' := by
      have := F.right_inv ht
      rwa [hFc] at this
    rw [hQdef, Function.comp_apply, modelQ_eq_local M Ψ hUy.2] at hq
    rw [hseg, map_smul]
    funext i
    refine Fin.cases ?_ (fun i => ?_) i
    · simp only [Pi.smul_apply, smul_eq_mul, Fin.cons_zero]
      exact inv_mul_cancel₀ h0
    · simp only [Pi.smul_apply, smul_eq_mul, Fin.cons_succ]
      rw [← congrFun hq i, div_eq_inv_mul]
  · rw [← hy0]
    have hblk : ∀ k, ∃ i, γ₀ (Q u) ⟨k, i⟩ ≠ 0 := by
      rw [hγ₀u]; exact (lift_mem M x).1
    have hH : cxHessian (fun y' => r * Real.log (L.h (γ y'))) (Q u) =
        cxHessian (fun y' => r * Real.log (L.h (γ₀ y'))) (Q u) := by
      set G : (Fin e → ℂ) → ℂ :=
        fun y' => ((-(r * (L.a k0 : ℝ)) : ℝ) : ℂ) * Complex.log (ψ0 y' / ψ0 (Q u)) with hG
      set C : ℝ := -(r * (L.a k0 : ℝ) * Real.log ‖ψ0 (Q u)‖) with hC
      have hGa : AnalyticAt ℂ G (Q u) := by
        refine analyticAt_const.mul ((hψ0a.div analyticAt_const hψ0u).clog ?_)
        show ψ0 (Q u) / ψ0 (Q u) ∈ Complex.slitPlane
        rw [div_self hψ0u]
        exact Complex.one_mem_slitPlane
      have heq : (fun y' => r * Real.log (L.h (γ y'))) =ᶠ[𝓝 (Q u)]
          fun y' => r * Real.log (L.h (γ₀ y')) + (G y').re + C := by
        filter_upwards [hψ0a.continuousAt.eventually_ne hψ0u,
          hγ₀a.continuousAt.eventually (isOpen_blockNonzero.mem_nhds hblk)] with y' h0 hb
        have hpos : 0 < L.h (γ₀ y') := L.pos _ hb
        have hn0 : ‖(ψ0 y')⁻¹‖ ^ L.a k0 ≠ 0 :=
          zpow_ne_zero _ (norm_ne_zero_iff.mpr (inv_ne_zero h0))
        simp only [hγdef]
        rw [show bsmul (c y') (γ₀ y') = fun p => c y' p.1 * γ₀ y' p from rfl, L.smul _ _ (hc_ne y' h0),
          prod_norm_update_zpow, Real.log_mul hn0 hpos.ne',
          hG, hC, Complex.re_ofReal_mul, Complex.log_re, norm_div,
          Real.log_div (norm_ne_zero_iff.mpr h0) (norm_ne_zero_iff.mpr hψ0u), Real.log_zpow,
          norm_inv, Real.log_inv]
        ring
      rw [cxHessian_congr heq, cxHessian_add_re (φ := fun y' => r * Real.log (L.h (γ₀ y'))) C
        (contDiffAt_const.mul (pot_contDiffAt hL hγ₀a hblk)) hGa]
    have hmd : maDensity (fun (_ : Fin e) y' => r * Real.log (L.h (γ y'))) (Q u) =
        maDensity (fun (_ : Fin e) y' => r * Real.log (L.h (γ₀ y'))) (Q u) := by
      simp only [maDensity, hH]
    rw [hmd, maDensity_eq_maDens]
    have hcd : ∀ i : Fin e, ContDiffAt ℝ 2
        (fun v => r * Real.log (L.h (modelLift M x ((M.atlas.chart j).symm v)))) (F.symm (Q u)) := by
      intro i
      rw [hσu]
      exact contDiffAt_const.mul (pot_contDiffAt hL (analyticAt_lift_chart M x j huU)
        (by rw [hsu]; exact (lift_mem M x).1))
    have hcomp : ReciprocityTheory.AnForm.maDens (fun (_ : Fin e) y' => r * Real.log (L.h (γ₀ y'))) (Q u) =
        ReciprocityTheory.AnForm.maDens
          (fun (_ : Fin e) v => r * Real.log (L.h (modelLift M x ((M.atlas.chart j).symm v))))
          (F.symm (Q u)) * Complex.normSq (ReciprocityTheory.AnForm.A.jacC F.symm (Q u)).det :=
      ReciprocityTheory.AnForm.A.maDens_comp
        (fun (_ : Fin e) v => r * Real.log (L.h (modelLift M x ((M.atlas.chart j).symm v))))
        F.symm (Q u) hσa hcd
    have hdetinv : LinearMap.det ((Ce.symm : (Fin e → ℂ) →L[ℂ] (Fin e → ℂ)) :
        (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) = (LinearMap.det (Df : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)))⁻¹ := by
      have := ContinuousLinearEquiv.det_coe_symm Ce
      rw [hCe'] at this
      exact this
    have hloc : ReciprocityTheory.AnForm.maDens
        (fun (_ : Fin e) v => r * Real.log (L.h (modelLift M x ((M.atlas.chart j).symm v)))) u =
        locDens M.atlas (fun _ => modelPot M L r) j u := by
      unfold locDens
      rw [hsu]
      rfl
    rw [hcomp, hσu, ReciprocityTheory.AnForm.A.det_jacC, hσd.fderiv, hdetinv, hloc, Complex.normSq_inv,
      Complex.normSq_eq_norm_sq]
    unfold pushDens
    rw [div_eq_mul_inv]

end ModelFibreSumAlmostEverywhere

end GroundTheory.Heights₂.Heights.LowerBoundFree
