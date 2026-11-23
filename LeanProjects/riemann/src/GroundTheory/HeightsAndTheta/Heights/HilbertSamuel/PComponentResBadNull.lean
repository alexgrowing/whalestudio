import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsComponentResBadNull
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ComponentResBadNullFlat
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeL
import ReciprocityTheory.AnalyticForms.AnalyticCharts.NullZero
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo Topology Filter Set

namespace ResBridge

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {W : Ideal (MvPolynomial (Σ k, ι k) ℂ)} {e : ℕ} (R : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.Res ι W e)

theorem ram_null {P : Ideal (MRing ι)} (hP : IsArithVar P (e + 1))
    (hW : W ∈ (P.map (MvPolynomial.map (Int.castRingHom ℂ))).minimalPrimes)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (hΨ : IsGoodProj P Ψ) (j : Fin R.atlas.n) :
    volume ((R.atlas.chart j).target ∩ (R.atlas.chart j).symm ⁻¹' {x | Ψ (segre (R.pt x)) 0 ≠ 0 ∧
      ∃ k, x ∈ (R.atlas.chart k).source ∧
        LinearMap.det (fderiv ℂ (resProj R Ψ ∘ (R.atlas.chart k).symm) (R.atlas.chart k x) :
          (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) = 0}) = 0 := by
  apply ReciprocityTheory.AnForm.volume_eq_zero_of_locally_in_analytic_zero_set
  rintro u0 ⟨hu0, h00, -⟩
  set x0 := (R.atlas.chart j).symm u0
  set V := (R.atlas.chart j).target ∩ (R.atlas.chart j).symm ⁻¹' R.R.src (R.idx x0) with hVdef
  have hV : IsOpen V := (R.atlas.chart j).isOpen_inter_preimage_symm (R.R.isOpen_alt_bis _)
  have hgc : ContinuousOn (fun u => Ψ (segre (R.liftAt x0 ((R.atlas.chart j).symm u))) 0) V :=
    fun u hu => (analyticAt_pi_iff.mp (analyticAt_segre_liftAt R Ψ x0 j hu) 0).continuousAt.continuousWithinAt
  set O := V ∩ (fun u => Ψ (segre (R.liftAt x0 ((R.atlas.chart j).symm u))) 0) ⁻¹' {0}ᶜ with hOdef
  have hO : IsOpen O := hgc.isOpen_inter_preimage hV isOpen_compl_singleton
  have hu0O : u0 ∈ O := ⟨⟨hu0, R.mem_src_idx x0⟩, h00⟩
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hO u0 hu0O
  have h0 : ∀ u ∈ Metric.ball u0 r, Ψ (segre (R.pt ((R.atlas.chart j).symm u))) 0 ≠ 0 := by
    intro u hu
    obtain ⟨μ, hμ, hμeq⟩ := psi_pt_eq R (hball hu).1.2 Ψ
    rw [hμeq, Pi.smul_apply, smul_eq_mul]
    exact mul_ne_zero hμ (hball hu).2
  have hQa : AnalyticOnNhd ℂ (resProj R Ψ ∘ (R.atlas.chart j).symm) (Metric.ball u0 r) := by
    intro u hu
    have := analyticAt_resProj R Ψ _ j ((R.atlas.chart j).map_target (hball hu).1.1) (h0 u hu)
    rwa [(R.atlas.chart j).right_inv (hball hu).1.1] at this
  refine ⟨Metric.ball u0 r, Metric.isOpen_ball, Metric.mem_ball_self hr,
    (convex_ball u0 r).isPreconnected, fun u => LinearMap.det
      (fderiv ℂ (resProj R Ψ ∘ (R.atlas.chart j).symm) u : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)),
    fun u hu => analyticAt_det_fderiv (hQa u hu), ?_, ?_⟩
  · by_contra hall
    push Not at hall
    exact not_flat R hP hW Ψ hΨ j Metric.isOpen_ball (fun u hu => (hball hu).1.1)
      ⟨u0, Metric.mem_ball_self hr⟩ h0 hQa hall
  · rintro w ⟨⟨hwt, hw0, k, hk, hdk⟩, -⟩
    have := det_resProj_chart R Ψ (j := j) ((R.atlas.chart j).map_target hwt) hk hw0
    rw [(R.atlas.chart j).right_inv hwt] at this
    show LinearMap.det (fderiv ℂ (resProj R Ψ ∘ (R.atlas.chart j).symm) w :
      (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) = 0
    rw [this, hdk, zero_mul]

theorem psi0_null {P : Ideal (MRing ι)} (hP : IsArithVar P (e + 1))
    (hW : W ∈ (P.map (MvPolynomial.map (Int.castRingHom ℂ))).minimalPrimes)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (hΨ : IsGoodProj P Ψ) (j : Fin R.atlas.n) :
    volume ((R.atlas.chart j).target ∩
      (R.atlas.chart j).symm ⁻¹' {x | Ψ (segre (R.pt x)) 0 = 0}) = 0 := by
  apply ReciprocityTheory.AnForm.volume_eq_zero_of_locally_in_analytic_zero_set
  rintro u0 ⟨hu0, -⟩
  set x0 := (R.atlas.chart j).symm u0
  set V := (R.atlas.chart j).target ∩ (R.atlas.chart j).symm ⁻¹' R.R.src (R.idx x0) with hVdef
  have hV : IsOpen V := (R.atlas.chart j).isOpen_inter_preimage_symm (R.R.isOpen_alt_bis _)
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hV u0 ⟨hu0, R.mem_src_idx x0⟩
  set f : (Fin e → ℂ) → ℂ := fun u => Ψ (segre (R.liftAt x0 ((R.atlas.chart j).symm u))) 0 with hfdef
  have hfa : AnalyticOnNhd ℂ f V := fun u hu =>
    analyticAt_pi_iff.mp (analyticAt_segre_liftAt R Ψ x0 j hu) 0
  refine ⟨Metric.ball u0 r, Metric.isOpen_ball, Metric.mem_ball_self hr,
    (convex_ball u0 r).isPreconnected, f, hfa.mono hball, ?_, ?_⟩
  · by_contra hall
    push Not at hall
    have hgood := hΨ _ (pt_mem_mcPts R hW x0)
    obtain ⟨i0, hi0⟩ : ∃ i0, Ψ (segre (R.liftAt x0 x0)) i0 ≠ 0 := by
      by_contra h
      push Not at h
      exact hgood (funext h)
    have hi0ne : i0 ≠ 0 := by
      rintro rfl
      exact hi0 (hall u0 (Metric.mem_ball_self hr))
    set m : Fin e := i0.pred hi0ne
    have hm : m.succ = i0 := Fin.succ_pred i0 hi0ne
    set Ψ' : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ) :=
      (LinearMap.funLeft ℂ ℂ (Equiv.swap (0 : Fin (e + 1)) i0)).comp Ψ with hΨ'def
    have hΨ'app : ∀ w i, Ψ' w i = Ψ w (Equiv.swap 0 i0 i) := fun w i => rfl
    have hΨ' : IsGoodProj P Ψ' := by
      intro z hz h
      refine hΨ z hz (funext fun i => ?_)
      have := congrFun h (Equiv.swap 0 i0 i)
      rw [hΨ'app, Equiv.swap_apply_self] at this
      exact this
    have hg'c : ContinuousOn (fun u => Ψ' (segre (R.liftAt x0 ((R.atlas.chart j).symm u))) 0)
        (Metric.ball u0 r) := fun u hu =>
      (analyticAt_pi_iff.mp (analyticAt_segre_liftAt R Ψ' x0 j (hball hu)) 0).continuousAt.continuousWithinAt
    set O := Metric.ball u0 r ∩
      (fun u => Ψ' (segre (R.liftAt x0 ((R.atlas.chart j).symm u))) 0) ⁻¹' {0}ᶜ with hOdef
    have hO : IsOpen O := hg'c.isOpen_inter_preimage Metric.isOpen_ball isOpen_compl_singleton
    have hu0O : u0 ∈ O := by
      refine ⟨Metric.mem_ball_self hr, ?_⟩
      show Ψ' (segre (R.liftAt x0 x0)) 0 ≠ 0
      rw [hΨ'app, Equiv.swap_apply_left]
      exact hi0
    have h0O : ∀ u ∈ O, Ψ' (segre (R.pt ((R.atlas.chart j).symm u))) 0 ≠ 0 := by
      intro u hu
      obtain ⟨μ, hμ, hμeq⟩ := psi_pt_eq R (hball hu.1).2 Ψ'
      rw [hμeq, Pi.smul_apply, smul_eq_mul]
      exact mul_ne_zero hμ hu.2
    have hanO : AnalyticOnNhd ℂ (resProj R Ψ' ∘ (R.atlas.chart j).symm) O := by
      intro u hu
      have := analyticAt_resProj R Ψ' _ j ((R.atlas.chart j).map_target (hball hu.1).1) (h0O u hu)
      rwa [(R.atlas.chart j).right_inv (hball hu.1).1] at this
    have hzero : ∀ u ∈ O, (resProj R Ψ' ∘ (R.atlas.chart j).symm) u m = 0 := by
      intro u hu
      simp only [Function.comp_apply, resProj]
      rw [hm, hΨ'app, Equiv.swap_apply_right]
      obtain ⟨μ, hμ, hμeq⟩ := psi_pt_eq R (hball hu.1).2 Ψ
      rw [hμeq, Pi.smul_apply, smul_eq_mul]
      have : f u = 0 := hall u hu.1
      simp only [hfdef] at this
      rw [this, mul_zero, zero_div]
    have hdetO : ∀ u ∈ O, LinearMap.det (fderiv ℂ (resProj R Ψ' ∘ (R.atlas.chart j).symm) u :
        (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) = 0 := by
      intro u hu
      have hcoord : (fun v => (resProj R Ψ' ∘ (R.atlas.chart j).symm) v m) =ᶠ[𝓝 u] fun _ => 0 := by
        filter_upwards [hO.mem_nhds hu] with v hv
        exact hzero v hv
      have hd : HasFDerivAt (fun v => (resProj R Ψ' ∘ (R.atlas.chart j).symm) v m)
          ((ContinuousLinearMap.proj m).comp (fderiv ℂ (resProj R Ψ' ∘ (R.atlas.chart j).symm) u)) u :=
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin e => ℂ) m).hasFDerivAt.comp u
          (hanO u hu).differentiableAt.hasFDerivAt
      have hd0 : HasFDerivAt (fun v => (resProj R Ψ' ∘ (R.atlas.chart j).symm) v m)
          (0 : (Fin e → ℂ) →L[ℂ] ℂ) u :=
        (hasFDerivAt_const (0 : ℂ) u).congr_of_eventuallyEq hcoord
      have hrow := hd.unique hd0
      refine det_eq_zero_of_coord m fun v => ?_
      have := congrArg (fun T : (Fin e → ℂ) →L[ℂ] ℂ => T v) hrow
      simpa using this
    exact not_flat R hP hW Ψ' hΨ' j hO (fun u hu => (hball hu.1).1) ⟨u0, hu0O⟩ h0O hanO hdetO
  · rintro w ⟨⟨hwt, hw0⟩, hwb⟩
    obtain ⟨μ, hμ, hμeq⟩ := psi_pt_eq R (hball hwb).2 Ψ
    have := congrFun hμeq 0
    rw [Pi.smul_apply, smul_eq_mul] at this
    have hw0' : Ψ (segre (R.pt ((R.atlas.chart j).symm w))) 0 = 0 := hw0
    rw [hw0'] at this
    exact (mul_eq_zero.mp this.symm).resolve_left hμ

end ResBridge

theorem ComponentResBadNull.proof : ComponentResBadNull.Statement := by
  intro K _ _ ι _ P e W R Ψ hP hW hΨ j
  refine measure_mono_null ?_ (measure_union_null (measure_union_null (ResBridge.D_null R j)
    (ResBridge.psi0_null R hP hW Ψ hΨ j)) (ResBridge.ram_null R hP hW Ψ hΨ j))
  rintro u ⟨hu, hbad⟩
  rcases hbad with (hD | h0) | ⟨k, hk, hnot⟩
  · exact Or.inl (Or.inl ⟨hu, hD⟩)
  · exact Or.inl (Or.inr ⟨hu, h0⟩)
  · by_cases h0 : Ψ (segre (R.pt ((R.atlas.chart j).symm u))) 0 = 0
    · exact Or.inl (Or.inr ⟨hu, h0⟩)
    · refine Or.inr ⟨hu, h0, k, hk, ?_⟩
      by_contra hdet
      exact hnot ⟨ResBridge.analyticAt_resProj R Ψ _ k hk h0, hdet⟩

end GroundTheory.Heights₂.Heights.HilbertSamuel
