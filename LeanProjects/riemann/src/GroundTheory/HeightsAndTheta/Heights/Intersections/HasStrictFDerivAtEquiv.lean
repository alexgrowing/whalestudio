import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridge
import GroundTheory.HeightsAndTheta.Heights.Intersections.PullWMemFibre
import GroundTheory.HeightsAndTheta.Heights.Intersections.PullBad
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M
  Topology Filter Set

namespace pullbackPushforward_holds

section Orbit

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem sameOrbit_comm {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') : SameOrbit z' z := by
  obtain ⟨c, hc, rfl⟩ := h
  refine ⟨fun k => (c k)⁻¹, fun k => inv_ne_zero (hc k), ?_⟩
  funext p
  simp [← mul_assoc, inv_mul_cancel₀ (hc p.1)]

theorem sameOrbit_tr {z z' z'' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') (h' : SameOrbit z' z'') :
    SameOrbit z z'' := by
  obtain ⟨c, hc, rfl⟩ := h
  obtain ⟨d, hd, rfl⟩ := h'
  exact ⟨fun k => c k * d k, fun k => mul_ne_zero (hc k) (hd k), by funext p; simp [mul_assoc]⟩

theorem segre_of_sameOrbit {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') :
    ∃ μ : ℂ, μ ≠ 0 ∧ segre z = μ • segre z' := by
  obtain ⟨c, hc, rfl⟩ := h
  exact ⟨∏ k, c k, Finset.prod_ne_zero_iff.mpr fun k _ => hc k, segre_smul c z'⟩

variable {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]

theorem sameOrbit_comp {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : IsBlockMap κ v)
    {z z' : (Σ k', ι' k') → ℂ} (h : SameOrbit z z') :
    SameOrbit (fun p => z (v p)) (fun p => z' (v p)) := by
  obtain ⟨c, hc, rfl⟩ := h
  refine ⟨fun k => c (κ k), fun k => hc _, ?_⟩
  funext p
  show c (v p).1 * z' (v p) = c (κ p.1) * z' (v p)
  rw [hv.2.2.1 p]

end Orbit

theorem hasStrictFDerivAt_equiv {n : ℕ} {Q : (Fin n → ℂ) → (Fin n → ℂ)} {u : Fin n → ℂ}
    (hQ : AnalyticAt ℂ Q u)
    (hd : LinearMap.det (fderiv ℂ Q u : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) ≠ 0) :
    ∃ e : (Fin n → ℂ) ≃L[ℂ] (Fin n → ℂ), HasStrictFDerivAt Q (e : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ)) u := by
  refine ⟨(LinearMap.equivOfDetNeZero _ hd).toContinuousLinearEquiv, ?_⟩
  have h : ((LinearMap.equivOfDetNeZero _ hd).toContinuousLinearEquiv :
      (Fin n → ℂ) →L[ℂ] (Fin n → ℂ)) = fderiv ℂ Q u := by
    ext1 w
    rfl
  rw [h]
  exact hQ.hasStrictFDerivAt

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
  {P' J' : Ideal (MRing ι')} {n : ℕ} (R : AnLogRes P' J' n) {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')}

theorem pullPt_sameOrbit (hv : IsBlockMap κ v) {x z : R.X} (hz : z ∈ R.U x) :
    SameOrbit (pullPt R v z) (fun p => R.lift x z (v p)) :=
  sameOrbit_comp hv (R.compat z x z ⟨R.mem_U z, hz⟩)

theorem pullQ_eq_local (hv : IsBlockMap κ v) (Φ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ))
    {x z : R.X} (hz : z ∈ R.U x) :
    pullQ R v Φ z = fun i => Φ (segre (fun p => R.lift x z (v p))) i.succ /
      Φ (segre (fun p => R.lift x z (v p))) 0 := by
  obtain ⟨μ, hμ, hseg⟩ := segre_of_sameOrbit (pullPt_sameOrbit R hv hz)
  funext i
  simp only [pullQ, hseg, map_smul, Pi.smul_apply, smul_eq_mul]
  exact mul_div_mul_left _ _ hμ

theorem analyticAt_segre_pull (Φ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)) (x : R.X)
    (j : Fin R.A.n) {u : Fin n → ℂ} (hu : u ∈ (R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' R.U x) :
    AnalyticAt ℂ (fun w => Φ (segre (fun p => R.lift x ((R.A.chart j).symm w) (v p)))) u := by
  classical
  have hl := analyticAt_lift_chart R x j hu
  have hs : AnalyticAt ℂ (fun w => segre (fun p => R.lift x ((R.A.chart j).symm w) (v p))) u := by
    refine analyticAt_pi_iff.mpr fun i => ?_
    simp only [segre]
    exact Finset.analyticAt_fun_prod _ fun k _ => analyticAt_pi_iff.mp hl _
  exact (LinearMap.toContinuousLinearMap Φ).analyticAt _ |>.comp hs

theorem analyticAt_pullQ (hv : IsBlockMap κ v) (Φ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ))
    (x : R.X) (j : Fin R.A.n) (hj : x ∈ (R.A.chart j).source)
    (h0 : Φ (segre (pullPt R v x)) 0 ≠ 0) :
    AnalyticAt ℂ (pullQ R v Φ ∘ (R.A.chart j).symm) (R.A.chart j x) := by
  set u := R.A.chart j x
  have hsu : (R.A.chart j).symm u = x := (R.A.chart j).left_inv hj
  have hu : u ∈ (R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' R.U x :=
    ⟨(R.A.chart j).map_source hj, by rw [Set.mem_preimage, hsu]; exact R.mem_U x⟩
  have hH := analyticAt_segre_pull R (v := v) Φ x j hu
  have hH0 : AnalyticAt ℂ (fun w => Φ (segre (fun p => R.lift x ((R.A.chart j).symm w) (v p))) 0) u :=
    analyticAt_pi_iff.mp hH 0
  have hne : Φ (segre (fun p => R.lift x ((R.A.chart j).symm u) (v p))) 0 ≠ 0 := by
    rw [hsu]; exact h0
  have hF : AnalyticAt ℂ (fun w => fun i : Fin n =>
      Φ (segre (fun p => R.lift x ((R.A.chart j).symm w) (v p))) i.succ /
        Φ (segre (fun p => R.lift x ((R.A.chart j).symm w) (v p))) 0) u :=
    analyticAt_pi_iff.mpr fun i => (analyticAt_pi_iff.mp hH i.succ).div hH0 hne
  refine hF.congr ?_
  filter_upwards [((R.A.chart j).isOpen_inter_preimage_symm (R.isOpen_U x)).mem_nhds hu] with w hw
  exact (pullQ_eq_local R hv Φ hw.2).symm

theorem det_pullQ_chart (hv : IsBlockMap κ v) (Φ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ))
    {x : R.X} {j k : Fin R.A.n} (hj : x ∈ (R.A.chart j).source) (hk : x ∈ (R.A.chart k).source)
    (h0 : Φ (segre (pullPt R v x)) 0 ≠ 0) :
    LinearMap.det (fderiv ℂ (pullQ R v Φ ∘ (R.A.chart j).symm) (R.A.chart j x) :
        (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) =
      LinearMap.det (fderiv ℂ (pullQ R v Φ ∘ (R.A.chart k).symm) (R.A.chart k x) :
        (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) *
      LinearMap.det (fderiv ℂ (R.A.chart k ∘ (R.A.chart j).symm) (R.A.chart j x) :
        (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) := by
  set u := R.A.chart j x
  have hsu : (R.A.chart j).symm u = x := (R.A.chart j).left_inv hj
  set T := R.A.chart k ∘ (R.A.chart j).symm with hTdef
  have huk : u ∈ (R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' (R.A.chart k).source :=
    ⟨(R.A.chart j).map_source hj, by rw [mem_preimage, hsu]; exact hk⟩
  have hT : AnalyticAt ℂ T u := R.A.holo j k u huk
  have hTu : T u = R.A.chart k x := by simp only [hTdef, Function.comp_apply, hsu]
  have hQk := analyticAt_pullQ R hv Φ x k hk h0
  have heq : pullQ R v Φ ∘ (R.A.chart j).symm =ᶠ[𝓝 u] (pullQ R v Φ ∘ (R.A.chart k).symm) ∘ T := by
    filter_upwards [((R.A.chart j).isOpen_inter_preimage_symm (R.A.chart k).open_source).mem_nhds
      huk] with w hw
    simp only [hTdef, Function.comp_apply, (R.A.chart k).left_inv hw.2]
  rw [heq.fderiv_eq, fderiv_comp u (by rw [hTu]; exact hQk.differentiableAt) hT.differentiableAt,
    hTu]
  exact LinearMap.det_comp _ _

theorem eval_lift_eq_zero_iff {f : MRing ι'} {a : K' → ℕ} (hf : IsMultiHomog f a) {x z : R.X}
    (hz : z ∈ R.U x) :
    eval (R.lift z z) (map (Int.castRingHom ℂ) f) = 0 ↔
      eval (R.lift x z) (map (Int.castRingHom ℂ) f) = 0 := by
  obtain ⟨c, hc, hzc⟩ := R.compat z x z ⟨R.mem_U z, hz⟩
  rw [hzc, eval_smul_homog f a hf c]
  have : ∏ k, c k ^ a k ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc k)
  simp [this]

theorem isOpen_chart_ne {f : MRing ι'} {a : K' → ℕ} (hf : IsMultiHomog f a) (j : Fin R.A.n) :
    IsOpen ((R.A.chart j).target ∩
      (R.A.chart j).symm ⁻¹' {x | eval (R.lift x x) (map (Int.castRingHom ℂ) f) ≠ 0}) := by
  rw [isOpen_iff_mem_nhds]
  rintro u1 ⟨hu1, h1⟩
  set x1 := (R.A.chart j).symm u1
  have hV : (R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' R.U x1 ∈ 𝓝 u1 :=
    ((R.A.chart j).isOpen_inter_preimage_symm (R.isOpen_U x1)).mem_nhds ⟨hu1, R.mem_U x1⟩
  have hcont : ContinuousAt (fun u => eval (R.lift x1 ((R.A.chart j).symm u))
      (map (Int.castRingHom ℂ) f)) u1 :=
    (MvPolynomial.continuous_eval _).continuousAt.comp
      (analyticAt_lift_chart R x1 j ⟨hu1, R.mem_U x1⟩).continuousAt
  have hne : eval (R.lift x1 ((R.A.chart j).symm u1)) (map (Int.castRingHom ℂ) f) ≠ 0 := h1
  filter_upwards [hV, hcont.eventually_ne hne] with u hu hne'
  exact ⟨hu.1, fun h => hne' ((eval_lift_eq_zero_iff R hf hu.2).mp h)⟩

theorem fzero_null (hP' : IsArithVar P' (n + 1)) {f : MRing ι'} {a : K' → ℕ} (hf : IsMultiHomog f a)
    (hfP : f ∉ P') (j : Fin R.A.n) :
    volume ((R.A.chart j).target ∩
      (R.A.chart j).symm ⁻¹' {x | eval (R.lift x x) (map (Int.castRingHom ℂ) f) = 0}) = 0 := by
  classical
  obtain ⟨Ψ', hΨ'⟩ := goodProjExists K' ι' P' n hP'
  have hJf : IsMultiHomogIdeal (Ideal.span {f}) :=
    ⟨{f}, fun g hg => ⟨a, by rw [Set.mem_singleton_iff.mp hg]; exact hf⟩, rfl⟩
  have hJP : ¬ Ideal.span {f} ≤ P' := fun h => hfP (h (Ideal.subset_span rfl))
  have hnull := projB_null Ψ' hP' hΨ' hJf hJP
  apply ReciprocityTheory.AnForm.volume_eq_zero_of_locally_in_analytic_zero_set
  rintro u0 ⟨hu0, -⟩
  set x0 := (R.A.chart j).symm u0
  set V := (R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' R.U x0 with hVdef
  have hV : IsOpen V := (R.A.chart j).isOpen_inter_preimage_symm (R.isOpen_U x0)
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hV u0 ⟨hu0, R.mem_U x0⟩
  set g : (Fin n → ℂ) → ℂ := fun u => eval (R.lift x0 ((R.A.chart j).symm u))
    (map (Int.castRingHom ℂ) f) with hgdef
  have hga : AnalyticOnNhd ℂ g V := fun u hu =>
    analyticAt_eval_poly _ fun p => analyticAt_pi_iff.mp (analyticAt_lift_chart R x0 j hu) p
  refine ⟨Metric.ball u0 r, Metric.isOpen_ball, Metric.mem_ball_self hr,
    (convex_ball u0 r).isPreconnected, g, hga.mono hball, ?_, ?_⟩
  · by_contra hall
    push Not at hall
    set N := ((R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' {x | Ψ' (segre (R.lift x x)) 0 = 0}) ∪
      ((R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' {x | Ψ' (segre (R.lift x x)) 0 ≠ 0 ∧
        ∃ k, x ∈ (R.A.chart k).source ∧
          LinearMap.det (fderiv ℂ (brQ R Ψ' ∘ (R.A.chart k).symm) (R.A.chart k x) :
            (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) = 0}) with hNdef
    have hN : volume N = 0 :=
      measure_union_null (psi0_null R Ψ' hP' hΨ' j) (ram_null R Ψ' hP' hΨ' j)
    obtain ⟨u1, hu1B, hu1N⟩ : ∃ u1 ∈ Metric.ball u0 r, u1 ∉ N := by
      by_contra h
      push Not at h
      exact (Metric.measure_ball_pos volume u0 hr).ne' (measure_mono_null h hN)
    have hu1t : u1 ∈ (R.A.chart j).target := (hball hu1B).1
    set x1 := (R.A.chart j).symm u1
    have hx1 : x1 ∈ (R.A.chart j).source := (R.A.chart j).map_target hu1t
    have hcx1 : R.A.chart j x1 = u1 := (R.A.chart j).right_inv hu1t
    have h01 : Ψ' (segre (R.lift x1 x1)) 0 ≠ 0 := fun h => hu1N (Or.inl ⟨hu1t, h⟩)
    have hdet1 : LinearMap.det (fderiv ℂ (brQ R Ψ' ∘ (R.A.chart j).symm) u1 :
        (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) ≠ 0 := by
      intro h
      exact hu1N (Or.inr ⟨hu1t, h01, j, hx1, by rw [hcx1]; exact h⟩)
    have hQa : AnalyticAt ℂ (brQ R Ψ' ∘ (R.A.chart j).symm) u1 := by
      have := analyticAt_brQ R Ψ' x1 j hx1 h01
      rwa [hcx1] at this
    obtain ⟨e, he⟩ := hasStrictFDerivAt_equiv hQa hdet1
    have hcont0 : ContinuousOn (fun u => Ψ' (segre (R.lift x0 ((R.A.chart j).symm u))) 0) V :=
      fun u hu => (analyticAt_pi_iff.mp (analyticAt_segre_lift R Ψ' x0 j hu) 0).continuousAt.continuousWithinAt
    set O := Metric.ball u0 r ∩
      (fun u => Ψ' (segre (R.lift x0 ((R.A.chart j).symm u))) 0) ⁻¹' {0}ᶜ with hOdef
    have hO : IsOpen O :=
      (hcont0.mono hball).isOpen_inter_preimage Metric.isOpen_ball isOpen_compl_singleton
    have hu1O : u1 ∈ O := by
      refine ⟨hu1B, ?_⟩
      obtain ⟨μ, hμ, hμeq⟩ := psi_lift_eq R (hball hu1B).2 Ψ'
      show Ψ' (segre (R.lift x0 x1)) 0 ≠ 0
      intro h
      apply h01
      rw [hμeq, Pi.smul_apply, smul_eq_mul, h, mul_zero]
    have himg : (brQ R Ψ' ∘ (R.A.chart j).symm) '' O ∈
        𝓝 ((brQ R Ψ' ∘ (R.A.chart j).symm) u1) := by
      rw [← he.map_nhds_eq_of_equiv]
      exact Filter.image_mem_map (hO.mem_nhds hu1O)
    refine (Measure.measure_pos_of_mem_nhds (μ := volume) himg).ne' (measure_mono_null ?_ hnull)
    rintro _ ⟨u, huO, rfl⟩
    set x := (R.A.chart j).symm u
    have hxU : x ∈ R.U x0 := (hball huO.1).2
    obtain ⟨μ, hμ, hμeq⟩ := psi_lift_eq R hxU Ψ'
    have h0x : Ψ' (segre (R.lift x x)) 0 ≠ 0 := by
      rw [hμeq, Pi.smul_apply, smul_eq_mul]
      exact mul_ne_zero hμ huO.2
    obtain ⟨z2, hz2, hsz2, hΨz2⟩ := brW_mem_fibre R Ψ' hP'.1 hP'.2.1.2.1 h0x
    refine ⟨z2, hz2, ?_, ?_⟩
    · have hso : SameOrbit z2 (R.lift x x) :=
        sameOrbit_of_segre (R.mem x x (R.mem_U x)).1 _ (inv_ne_zero h0x) (by rw [hsz2]; rfl)
      refine mem_mcPts_of_sameOrbit hJf hso ⟨(R.mem x x (R.mem_U x)).1, fun g' hg' => ?_⟩
      obtain ⟨r', rfl⟩ := Ideal.mem_span_singleton'.mp hg'
      rw [map_mul, eval_mul, (eval_lift_eq_zero_iff R hf hxU).mpr (hall u huO.1), mul_zero]
    · rw [hsz2, hΨz2]
      rfl
  · rintro w ⟨⟨-, hw0⟩, hwb⟩
    exact (eval_lift_eq_zero_iff R hf (hball hwb).2).mp hw0

end pullbackPushforward_holds

end GroundTheory.Heights₂.Heights.Inter
