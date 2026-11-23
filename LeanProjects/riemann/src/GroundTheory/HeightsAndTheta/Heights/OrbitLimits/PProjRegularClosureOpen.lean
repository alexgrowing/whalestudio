import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PProjRegular
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsProjRegularClosureOpen
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M

namespace ProjRegularClosureOpen

def projNumMat {n : ℕ} (F : (Fin n → ℂ) → Fin (n + 1) → ℂ) (u : Fin n → ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  fun i l => F u 0 * fderiv ℂ (fun v => F v i.succ) u (Pi.single l 1) -
    F u i.succ * fderiv ℂ (fun v => F v 0) u (Pi.single l 1)

theorem analyticAt_projDet {n : ℕ} {F : (Fin n → ℂ) → Fin (n + 1) → ℂ} {u : Fin n → ℂ}
    (hF : AnalyticAt ℂ F u) : AnalyticAt ℂ (fun v => F v 0 * (projNumMat F v).det) u := by
  have hc : ∀ i, AnalyticAt ℂ (fun v => F v i) u := fun i => analyticAt_pi_iff.1 hF i
  have hd : ∀ i (w : Fin n → ℂ), AnalyticAt ℂ (fun v => fderiv ℂ (fun v => F v i) v w) u :=
    fun i w => ((ContinuousLinearMap.apply ℂ ℂ w).analyticAt _).comp (hc i).fderiv
  have hm : ∀ i l, AnalyticAt ℂ (fun v => projNumMat F v i l) u := fun i l =>
    ((hc 0).mul (hd _ _)).sub ((hc _).mul (hd _ _))
  refine (hc 0).mul ?_
  simp only [Matrix.det_apply, Units.smul_def, zsmul_eq_mul]
  exact Finset.univ.analyticAt_fun_sum (fun σ _ =>
    analyticAt_const.mul (Finset.univ.analyticAt_fun_prod (fun i _ => hm _ _)))

theorem det_fderiv_div {n : ℕ} {F : (Fin n → ℂ) → Fin (n + 1) → ℂ} {u : Fin n → ℂ}
    (hF : AnalyticAt ℂ F u) (h0 : F u 0 ≠ 0) :
    LinearMap.det (fderiv ℂ (fun v (i : Fin n) => F v i.succ / F v 0) u :
      (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) = ((F u 0 ^ 2)⁻¹) ^ n * (projNumMat F u).det := by
  classical
  have hc : ∀ i, AnalyticAt ℂ (fun v => F v i) u := fun i => analyticAt_pi_iff.1 hF i
  have key : ∀ (i : Fin n) (w : Fin n → ℂ),
      F u 0 ^ 2 * fderiv ℂ (fun v (i : Fin n) => F v i.succ / F v 0) u w i =
        F u 0 * fderiv ℂ (fun v => F v i.succ) u w - F u i.succ * fderiv ℂ (fun v => F v 0) u w := by
    intro i w
    have hq : AnalyticAt ℂ (fun v => F v i.succ / F v 0) u := (hc _).div (hc 0) h0
    have hev : (fun v => F v i.succ / F v 0 * F v 0) =ᶠ[𝓝 u] (fun v => F v i.succ) := by
      filter_upwards [(hc 0).continuousAt.eventually_ne h0] with v hv
      exact div_mul_cancel₀ _ hv
    have hmul : fderiv ℂ (fun v => F v i.succ) u = (F u i.succ / F u 0) • fderiv ℂ (fun v => F v 0) u +
        F u 0 • fderiv ℂ (fun v => F v i.succ / F v 0) u := by
      rw [← hev.fderiv_eq]
      exact fderiv_fun_mul hq.differentiableAt (hc 0).differentiableAt
    have hcomp : fderiv ℂ (fun v (i : Fin n) => F v i.succ / F v 0) u w i =
        fderiv ℂ (fun v => F v i.succ / F v 0) u w := by
      rw [fderiv_pi (φ := fun (i : Fin n) v => F v i.succ / F v 0)
        (fun i => ((hc _).div (hc 0) h0).differentiableAt)]
      rfl
    rw [hcomp, hmul]
    simp only [FunLike.coe_add, FunLike.coe_smul, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul]
    field_simp
    ring
  have hM : LinearMap.toMatrix' (fderiv ℂ (fun v (i : Fin n) => F v i.succ / F v 0) u :
      (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) = (F u 0 ^ 2)⁻¹ • projNumMat F u := by
    ext i l
    simp only [LinearMap.toMatrix'_apply, ContinuousLinearMap.coe_coe, Matrix.smul_apply,
      smul_eq_mul, projNumMat]
    rw [← key i (Pi.single l 1)]
    field_simp
  rw [← LinearMap.det_toMatrix', hM, Matrix.det_smul, Fintype.card_fin]

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P J : Ideal (MRing ι)}
  {n : ℕ} {R : AnLogRes P J (n + 1)} (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ))

theorem lift_analyticAt_of_mem {V : Set R.X} {BV : FinHolAtlas n V}
    (hB : HoloMap BV R.A Subtype.val) (x : R.X) {j : Fin BV.n} {u : Fin n → ℂ}
    (hu : u ∈ (BV.chart j).target) (hU : ((BV.chart j).symm u).1 ∈ R.U x) :
    AnalyticAt ℂ (fun v => R.lift x ((BV.chart j).symm v).1) u := by
  rw [analyticAt_pi_iff]
  intro p
  obtain ⟨k, hk⟩ : ∃ k, ((BV.chart j).symm u).1 ∈ (R.A.chart k).source := R.A.cover _
  have h1 : AnalyticAt ℂ ((fun y => R.lift x y p) ∘ (R.A.chart k).symm)
      (R.A.chart k ((BV.chart j).symm u).1) :=
    R.holo x p k _ ⟨(R.A.chart k).map_source hk, by
      show (R.A.chart k).symm (R.A.chart k ((BV.chart j).symm u).1) ∈ R.U x
      rw [(R.A.chart k).left_inv hk]; exact hU⟩
  have h2 : AnalyticAt ℂ (R.A.chart k ∘ Subtype.val ∘ (BV.chart j).symm) u :=
    hB.2 j k _ ⟨hu, hk⟩
  have hcont : ContinuousAt (fun v => ((BV.chart j).symm v).1) u :=
    continuous_subtype_val.continuousAt.comp ((BV.chart j).continuousAt_symm hu)
  refine (h1.comp_of_eq h2 rfl).congr ?_
  filter_upwards [hcont.preimage_mem_nhds ((R.A.chart k).open_source.mem_nhds hk)] with v hv
  simp [(R.A.chart k).left_inv hv]

theorem proj_analyticAt_of_mem {V : Set R.X} {BV : FinHolAtlas n V}
    (hB : HoloMap BV R.A Subtype.val) (x : R.X) {j : Fin BV.n} {u : Fin n → ℂ}
    (hu : u ∈ (BV.chart j).target) (hU : ((BV.chart j).symm u).1 ∈ R.U x) :
    AnalyticAt ℂ (fun v => Ψ (segre (R.lift x ((BV.chart j).symm v).1))) u := by
  classical
  have hF := lift_analyticAt_of_mem hB x hu hU
  have hs : AnalyticAt ℂ (fun v => segre (R.lift x ((BV.chart j).symm v).1)) u := by
    rw [analyticAt_pi_iff]
    intro i
    exact Finset.univ.analyticAt_fun_prod (fun k _ => analyticAt_pi_iff.1 hF ⟨k, i k⟩)
  exact ((LinearMap.toContinuousLinearMap Ψ).analyticAt _).comp hs

end ProjRegularClosureOpen

open ProjRegularClosureOpen in

theorem ProjRegularClosureOpen.proof : ProjRegularClosureOpen.Statement := by
  intro K _ ι _ P J n R Ψ V BV hB
  classical
  rw [isOpen_iff_mem_nhds]
  intro x hx
  obtain ⟨j, hj⟩ := BV.cover x
  let S : Set (Fin n → ℂ) :=
    (BV.chart j).target ∩ (BV.chart j).symm ⁻¹' (Subtype.val ⁻¹' R.U x.1)
  have hSo : IsOpen S := (BV.chart j).isOpen_inter_preimage_symm
    ((R.isOpen_U x.1).preimage continuous_subtype_val)
  have hxS : BV.chart j x ∈ S :=
    ⟨(BV.chart j).map_source hj, by simp [(BV.chart j).left_inv hj, R.mem_U]⟩
  obtain ⟨r, hr, hrS⟩ := Metric.isOpen_iff.1 hSo _ hxS
  let F : (Fin n → ℂ) → Fin (n + 1) → ℂ := fun v => Ψ (segre (R.lift x.1 ((BV.chart j).symm v).1))
  let h : (Fin n → ℂ) → ℂ := fun v => F v 0 * (projNumMat F v).det
  have hFa : ∀ u ∈ S, AnalyticAt ℂ F u := fun u hu => proj_analyticAt_of_mem Ψ hB x.1 hu.1 hu.2
  have hha : AnalyticOnNhd ℂ h (Metric.ball (BV.chart j x) r) := fun u hu =>
    analyticAt_projDet (hFa u (hrS hu))
  have hreg : ∀ u ∈ S, (BV.chart j).symm u ∈ projRegular R Ψ BV ↔ h u ≠ 0 := by
    intro u hu
    have hy : (BV.chart j).symm u ∈ (BV.chart j).source := (BV.chart j).map_target hu.1
    have hyu : BV.chart j ((BV.chart j).symm u) = u := (BV.chart j).right_inv hu.1
    have h0iff := ProjRegular.proj_ne_zero_iff Ψ (R := R) (hu.2 : ((BV.chart j).symm u).1 ∈ R.U x.1)
    have hev : (projCoord R Ψ ∘ Subtype.val) ∘ (BV.chart j).symm =ᶠ[𝓝 u]
        fun v (i : Fin n) => F v i.succ / F v 0 := by
      filter_upwards [hSo.mem_nhds hu] with v hv
      exact ProjRegular.projCoord_eq Ψ hv.2
    constructor
    · rintro ⟨h0, hd⟩
      have hF0 : F u 0 ≠ 0 := h0iff.1 h0
      have hdj := hd j hy
      rw [hyu, hev.fderiv_eq, det_fderiv_div (hFa u hu) hF0] at hdj
      exact mul_ne_zero hF0 (right_ne_zero_of_mul hdj)
    · intro hh
      have hF0 : F u 0 ≠ 0 := left_ne_zero_of_mul hh
      have h0 := h0iff.2 hF0
      refine ⟨h0, fun k hk => ProjRegular.det_ne_zero_of_chart Ψ hB _ h0 hk hy ?_⟩
      rw [hyu, hev.fderiv_eq, det_fderiv_div (hFa u hu) hF0]
      exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero (pow_ne_zero _ hF0)))
        (right_ne_zero_of_mul hh)
  have hW : (BV.chart j).source ∩ (BV.chart j) ⁻¹' Metric.ball (BV.chart j x) r ∈ 𝓝 x :=
    ((BV.chart j).isOpen_inter_preimage Metric.isOpen_ball).mem_nhds ⟨hj, Metric.mem_ball_self hr⟩
  filter_upwards [hW] with y hyW
  obtain ⟨hys, hyb⟩ := hyW
  rw [mem_closure_iff_nhds]
  intro W hWy
  by_contra hne
  rw [Set.not_nonempty_iff_eq_empty] at hne
  have hz : h =ᶠ[𝓝 (BV.chart j y)] 0 := by
    have hc : ContinuousAt (BV.chart j).symm (BV.chart j y) :=
      (BV.chart j).continuousAt_symm ((BV.chart j).map_source hys)
    have hW' : W ∈ 𝓝 ((BV.chart j).symm (BV.chart j y)) := by
      rw [(BV.chart j).left_inv hys]; exact hWy
    filter_upwards [hc.preimage_mem_nhds hW', Metric.isOpen_ball.mem_nhds hyb] with v hvW hvB
    by_contra hv
    exact (Set.eq_empty_iff_forall_notMem.1 hne) _ ⟨hvW, (hreg v (hrS hvB)).2 hv⟩
  have hall := hha.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (convex_ball _ _).isPreconnected hyb hz
  obtain ⟨z, hzW, hzreg⟩ := mem_closure_iff_nhds.1 hx _ hW
  exact ((hreg _ (hrS hzW.2)).1 (by rwa [(BV.chart j).left_inv hzW.1])) (hall hzW.2)

end GroundTheory.Heights₂.Heights.Targets
