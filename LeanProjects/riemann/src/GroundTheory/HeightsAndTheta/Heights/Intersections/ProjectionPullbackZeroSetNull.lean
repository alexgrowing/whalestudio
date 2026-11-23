import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.HasStrictFDerivAtEquiv
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsBlockGenFinite
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M
  Topology Filter Set

namespace pullbackPushforward_holds

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
  {P' J' : Ideal (MRing ι')} {n : ℕ} (R : AnLogRes P' J' n) {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')}

theorem orbit_subsingleton (t : (Σ k', ι' k') → ℂ) :
    {x : R.X | R.lift x x ∉ mcPts J' ∧ SameOrbit (R.lift x x) t}.Subsingleton := by
  rintro x ⟨hx, hxt⟩ x' ⟨-, hx't⟩
  exact R.inj x x' hx (sameOrbit_tr hxt (sameOrbit_comm hx't))

theorem not_flat_pull (hGen : BlockGenFinite.Statement) (hv : IsBlockMap κ v)
    (hP' : IsArithVar P' (n + 1)) (hP : IsArithVar (imageZ v P') (n + 1))
    (Φ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)) (hΦ : IsGoodProj (imageZ v P') Φ)
    (j : Fin R.A.n) {O : Set (Fin n → ℂ)} (hO : IsOpen O) (hOt : O ⊆ (R.A.chart j).target)
    (hne : O.Nonempty) (h0 : ∀ u ∈ O, Φ (segre (pullPt R v ((R.A.chart j).symm u))) 0 ≠ 0)
    (han : AnalyticOnNhd ℂ (pullQ R v Φ ∘ (R.A.chart j).symm) O)
    (hdet : ∀ u ∈ O, LinearMap.det (fderiv ℂ (pullQ R v Φ ∘ (R.A.chart j).symm) u :
      (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) = 0) : False := by
  classical
  obtain ⟨f, a, hf, hfP, hfin⟩ := hGen K ι K' ι' κ v P' n hv hP' hP
  set O' := O ∩ ((R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' {x | R.lift x x ∉ mcPts J'}) ∩
    ((R.A.chart j).target ∩
      (R.A.chart j).symm ⁻¹' {x | eval (R.lift x x) (map (Int.castRingHom ℂ) f) ≠ 0}) with hO'def
  have hO' : IsOpen O' := (hO.inter (isOpen_chart_notB R j)).inter (isOpen_chart_ne R hf j)
  have hne' : O'.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    have hsub : O ⊆ ((R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' {x | R.lift x x ∈ mcPts J'}) ∪
        ((R.A.chart j).target ∩
          (R.A.chart j).symm ⁻¹' {x | eval (R.lift x x) (map (Int.castRingHom ℂ) f) = 0}) := by
      intro u hu
      by_cases hB : R.lift ((R.A.chart j).symm u) ((R.A.chart j).symm u) ∈ mcPts J'
      · exact Or.inl ⟨hOt hu, hB⟩
      by_cases hF : eval (R.lift ((R.A.chart j).symm u) ((R.A.chart j).symm u))
          (map (Int.castRingHom ℂ) f) = 0
      · exact Or.inr ⟨hOt hu, hF⟩
      have : u ∈ O' := ⟨⟨hu, hOt hu, hB⟩, hOt hu, hF⟩
      rw [h] at this
      exact absurd this (Set.notMem_empty u)
    exact (hO.measure_pos volume hne).ne'
      (measure_mono_null hsub (measure_union_null (R.null j) (fzero_null R hP' hf hfP j)))
  obtain ⟨y, hy⟩ := exists_infinite_fibre hO' hne' (han.mono fun u hu => hu.1.1)
    (fun u hu => hdet u hu.1.1)
  have hSinf : ((R.A.chart j).symm '' (O' ∩ (pullQ R v Φ ∘ (R.A.chart j).symm) ⁻¹' {y})).Infinite :=
    Set.Infinite.image ((R.A.chart j).symm.injOn.mono fun u hu => hu.1.1.2.1) hy
  have hF := fibreFinite K ι (imageZ v P') n Φ hP hΦ y
  choose! uw huw using fun w (hw : w ∈ fibre (imageZ v P') Φ y) => hw
  choose T hT using fun w => hfin (uw w)
  refine hSinf ((hF.biUnion fun w _ => (T w).finite_toSet.biUnion fun t _ =>
    (orbit_subsingleton R t).finite).subset ?_)
  rintro _ ⟨u, ⟨huO', hqu⟩, rfl⟩
  set x := (R.A.chart j).symm u
  have hxB : R.lift x x ∉ mcPts J' := huO'.1.2.2
  have hxf : eval (R.lift x x) (map (Int.castRingHom ℂ) f) ≠ 0 := huO'.2.2
  have h0x : Φ (segre (pullPt R v x)) 0 ≠ 0 := h0 u huO'.1.1
  have hqx : pullQ R v Φ x = y := hqu
  have hw := IntersectionWithSection.pullW_mem_fibre hv hP R Φ h0x
  rw [hqx] at hw
  obtain ⟨hu1, hu2, -⟩ := huw _ hw
  have hso : SameOrbit (pullPt R v x) (uw (pullW R v Φ x)) :=
    sameOrbit_of_segre hu1.1 (Φ (segre (pullPt R v x)) 0) h0x
      (by rw [hu2]; simp [pullW, smul_smul, mul_inv_cancel₀ h0x])
  obtain ⟨t, ht, hxt⟩ := hT (pullW R v Φ x) (R.lift x x) (R.mem x x (R.mem_U x)) hxf hso
  exact Set.mem_biUnion hw (Set.mem_biUnion (Finset.mem_coe.mpr ht) ⟨hxB, hxt⟩)

theorem projection_pullback_zeroSet_null (hGen : BlockGenFinite.Statement) (hv : IsBlockMap κ v)
    (hP' : IsArithVar P' (n + 1)) (hP : IsArithVar (imageZ v P') (n + 1))
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)) (hΨ : IsGoodProj (imageZ v P') Ψ)
    (j : Fin R.A.n) :
    volume ((R.A.chart j).target ∩
      (R.A.chart j).symm ⁻¹' {x | Ψ (segre (pullPt R v x)) 0 = 0}) = 0 := by
  classical
  apply ReciprocityTheory.AnForm.volume_eq_zero_of_locally_in_analytic_zero_set
  rintro u0 ⟨hu0, -⟩
  set x0 := (R.A.chart j).symm u0
  set V := (R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' R.U x0 with hVdef
  have hV : IsOpen V := (R.A.chart j).isOpen_inter_preimage_symm (R.isOpen_U x0)
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hV u0 ⟨hu0, R.mem_U x0⟩
  set f : (Fin n → ℂ) → ℂ := fun u => Ψ (segre (fun p => R.lift x0 ((R.A.chart j).symm u) (v p))) 0
    with hfdef
  have hfa : AnalyticOnNhd ℂ f V := fun u hu =>
    analyticAt_pi_iff.mp (analyticAt_segre_pull R (v := v) Ψ x0 j hu) 0
  refine ⟨Metric.ball u0 r, Metric.isOpen_ball, Metric.mem_ball_self hr,
    (convex_ball u0 r).isPreconnected, f, hfa.mono hball, ?_, ?_⟩
  · by_contra hall
    push Not at hall
    have hgood := hΨ _ (IntersectionWithSection.comp_mem_mcPts hv (R.mem x0 x0 (R.mem_U x0)))
    obtain ⟨i0, hi0⟩ : ∃ i0, Ψ (segre (pullPt R v x0)) i0 ≠ 0 := by
      by_contra h
      push Not at h
      exact hgood (funext h)
    have hi0ne : i0 ≠ 0 := by
      rintro rfl
      exact hi0 (hall u0 (Metric.mem_ball_self hr))
    set m : Fin n := i0.pred hi0ne
    have hm : m.succ = i0 := Fin.succ_pred i0 hi0ne
    set Ψ' : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ) :=
      (LinearMap.funLeft ℂ ℂ (Equiv.swap (0 : Fin (n + 1)) i0)).comp Ψ with hΨ'def
    have hΨ'app : ∀ w i, Ψ' w i = Ψ w (Equiv.swap 0 i0 i) := fun w i => rfl
    have hΨ' : IsGoodProj (imageZ v P') Ψ' := by
      intro z hz h
      refine hΨ z hz (funext fun i => ?_)
      have := congrFun h (Equiv.swap 0 i0 i)
      rw [hΨ'app, Equiv.swap_apply_self] at this
      exact this
    have hg'c : ContinuousOn (fun u => Ψ' (segre (fun p => R.lift x0 ((R.A.chart j).symm u) (v p))) 0)
        (Metric.ball u0 r) := fun u hu =>
      (analyticAt_pi_iff.mp (analyticAt_segre_pull R (v := v) Ψ' x0 j (hball hu)) 0).continuousAt.continuousWithinAt
    set O := Metric.ball u0 r ∩
      (fun u => Ψ' (segre (fun p => R.lift x0 ((R.A.chart j).symm u) (v p))) 0) ⁻¹' {0}ᶜ with hOdef
    have hO : IsOpen O := hg'c.isOpen_inter_preimage Metric.isOpen_ball isOpen_compl_singleton
    have hu0O : u0 ∈ O := by
      refine ⟨Metric.mem_ball_self hr, ?_⟩
      show Ψ' (segre (pullPt R v x0)) 0 ≠ 0
      rw [hΨ'app, Equiv.swap_apply_left]
      exact hi0
    have h0O : ∀ u ∈ O, Ψ' (segre (pullPt R v ((R.A.chart j).symm u))) 0 ≠ 0 := by
      intro u hu
      obtain ⟨μ, hμ, hμeq⟩ := segre_of_sameOrbit (pullPt_sameOrbit R hv (hball hu.1).2)
      rw [hμeq, map_smul, Pi.smul_apply, smul_eq_mul]
      exact mul_ne_zero hμ hu.2
    have hanO : AnalyticOnNhd ℂ (pullQ R v Ψ' ∘ (R.A.chart j).symm) O := by
      intro u hu
      have := analyticAt_pullQ R hv Ψ' _ j ((R.A.chart j).map_target (hball hu.1).1) (h0O u hu)
      rwa [(R.A.chart j).right_inv (hball hu.1).1] at this
    have hzero : ∀ u ∈ O, (pullQ R v Ψ' ∘ (R.A.chart j).symm) u m = 0 := by
      intro u hu
      simp only [Function.comp_apply, pullQ]
      rw [hm, hΨ'app, Equiv.swap_apply_right]
      obtain ⟨μ, hμ, hμeq⟩ := segre_of_sameOrbit (pullPt_sameOrbit R hv (hball hu.1).2)
      rw [hμeq, map_smul, Pi.smul_apply, smul_eq_mul]
      have : f u = 0 := hall u hu.1
      simp only [hfdef] at this
      rw [this, mul_zero, zero_div]
    have hdetO : ∀ u ∈ O, LinearMap.det (fderiv ℂ (pullQ R v Ψ' ∘ (R.A.chart j).symm) u :
        (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) = 0 := by
      intro u hu
      have hcoord : (fun w => (pullQ R v Ψ' ∘ (R.A.chart j).symm) w m) =ᶠ[𝓝 u] fun _ => 0 := by
        filter_upwards [hO.mem_nhds hu] with w hw
        exact hzero w hw
      have hd : HasFDerivAt (fun w => (pullQ R v Ψ' ∘ (R.A.chart j).symm) w m)
          ((ContinuousLinearMap.proj m).comp (fderiv ℂ (pullQ R v Ψ' ∘ (R.A.chart j).symm) u)) u :=
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) m).hasFDerivAt.comp u
          (hanO u hu).differentiableAt.hasFDerivAt
      have hd0 : HasFDerivAt (fun w => (pullQ R v Ψ' ∘ (R.A.chart j).symm) w m)
          (0 : (Fin n → ℂ) →L[ℂ] ℂ) u :=
        (hasFDerivAt_const (0 : ℂ) u).congr_of_eventuallyEq hcoord
      have hrow := hd.unique hd0
      refine det_eq_zero_of_coord m fun w => ?_
      have := congrArg (fun T : (Fin n → ℂ) →L[ℂ] ℂ => T w) hrow
      simpa using this
    exact not_flat_pull R hGen hv hP' hP Ψ' hΨ' j hO (fun u hu => (hball hu.1).1) ⟨u0, hu0O⟩ h0O
      hanO hdetO
  · rintro w ⟨⟨-, hw0⟩, hwb⟩
    obtain ⟨μ, hμ, hμeq⟩ := segre_of_sameOrbit (pullPt_sameOrbit R hv (hball hwb).2)
    have h := congrArg (fun s => Ψ s 0) hμeq
    simp only [map_smul, Pi.smul_apply, smul_eq_mul] at h
    have hw0' : Ψ (segre (pullPt R v ((R.A.chart j).symm w))) 0 = 0 := hw0
    rw [hw0'] at h
    exact (mul_eq_zero.mp h.symm).resolve_left hμ

theorem ram_pull_null (hGen : BlockGenFinite.Statement) (hv : IsBlockMap κ v)
    (hP' : IsArithVar P' (n + 1)) (hP : IsArithVar (imageZ v P') (n + 1))
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)) (hΨ : IsGoodProj (imageZ v P') Ψ)
    (j : Fin R.A.n) :
    volume ((R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' {x | Ψ (segre (pullPt R v x)) 0 ≠ 0 ∧
      ∃ k, x ∈ (R.A.chart k).source ∧
        LinearMap.det (fderiv ℂ (pullQ R v Ψ ∘ (R.A.chart k).symm) (R.A.chart k x) :
          (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) = 0}) = 0 := by
  apply ReciprocityTheory.AnForm.volume_eq_zero_of_locally_in_analytic_zero_set
  rintro u0 ⟨hu0, h00, -⟩
  set x0 := (R.A.chart j).symm u0
  set V := (R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' R.U x0 with hVdef
  have hV : IsOpen V := (R.A.chart j).isOpen_inter_preimage_symm (R.isOpen_U x0)
  have hgc : ContinuousOn (fun u => Ψ (segre (fun p => R.lift x0 ((R.A.chart j).symm u) (v p))) 0) V :=
    fun u hu => (analyticAt_pi_iff.mp (analyticAt_segre_pull R (v := v) Ψ x0 j hu) 0).continuousAt.continuousWithinAt
  set O := V ∩ (fun u => Ψ (segre (fun p => R.lift x0 ((R.A.chart j).symm u) (v p))) 0) ⁻¹' {0}ᶜ
    with hOdef
  have hO : IsOpen O := hgc.isOpen_inter_preimage hV isOpen_compl_singleton
  have hu0O : u0 ∈ O := ⟨⟨hu0, R.mem_U x0⟩, h00⟩
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hO u0 hu0O
  have h0 : ∀ u ∈ Metric.ball u0 r, Ψ (segre (pullPt R v ((R.A.chart j).symm u))) 0 ≠ 0 := by
    intro u hu
    obtain ⟨μ, hμ, hμeq⟩ := segre_of_sameOrbit (pullPt_sameOrbit R hv (hball hu).1.2)
    rw [hμeq, map_smul, Pi.smul_apply, smul_eq_mul]
    exact mul_ne_zero hμ (hball hu).2
  have hQa : AnalyticOnNhd ℂ (pullQ R v Ψ ∘ (R.A.chart j).symm) (Metric.ball u0 r) := by
    intro u hu
    have := analyticAt_pullQ R hv Ψ _ j ((R.A.chart j).map_target (hball hu).1.1) (h0 u hu)
    rwa [(R.A.chart j).right_inv (hball hu).1.1] at this
  refine ⟨Metric.ball u0 r, Metric.isOpen_ball, Metric.mem_ball_self hr,
    (convex_ball u0 r).isPreconnected, fun u => LinearMap.det (fderiv ℂ (pullQ R v Ψ ∘ (R.A.chart j).symm) u :
      (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)), fun u hu => analyticAt_det_fderiv (hQa u hu), ?_, ?_⟩
  · by_contra hall
    push Not at hall
    exact not_flat_pull R hGen hv hP' hP Ψ hΨ j Metric.isOpen_ball (fun u hu => (hball hu).1.1)
      ⟨u0, Metric.mem_ball_self hr⟩ h0 hQa hall
  · rintro w ⟨⟨hwt, hw0, k, hk, hdk⟩, -⟩
    have := det_pullQ_chart R hv Ψ (j := j) ((R.A.chart j).map_target hwt) hk hw0
    rw [(R.A.chart j).right_inv hwt] at this
    show LinearMap.det (fderiv ℂ (pullQ R v Ψ ∘ (R.A.chart j).symm) w :
      (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) = 0
    rw [this, hdk, zero_mul]

theorem pullBad_null (hGen : BlockGenFinite.Statement) (hv : IsBlockMap κ v)
    (hP' : IsArithVar P' (n + 1)) (hP : IsArithVar (imageZ v P') (n + 1))
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)) (hΨ : IsGoodProj (imageZ v P') Ψ)
    (j : Fin R.A.n) :
    volume ((R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' pullBad R v Ψ) = 0 := by
  have h3 : pullBad R v Ψ ⊆ {x | R.lift x x ∈ mcPts J'} ∪ {x | Ψ (segre (pullPt R v x)) 0 = 0} ∪
      {x | Ψ (segre (pullPt R v x)) 0 ≠ 0 ∧ ∃ k, x ∈ (R.A.chart k).source ∧
        LinearMap.det (fderiv ℂ (pullQ R v Ψ ∘ (R.A.chart k).symm) (R.A.chart k x) :
          (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) = 0} := by
    rintro x ((h | h) | ⟨k, hk, hn⟩)
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
    · by_cases h0 : Ψ (segre (pullPt R v x)) 0 = 0
      · exact Or.inl (Or.inr h0)
      · refine Or.inr ⟨h0, k, hk, ?_⟩
        by_contra hd
        exact hn ⟨analyticAt_pullQ R hv Ψ x k hk h0, hd⟩
  refine measure_mono_null (Set.inter_subset_inter_right _ (Set.preimage_mono h3)) ?_
  simp only [Set.preimage_union, Set.inter_union_distrib_left]
  exact measure_union_null (measure_union_null (R.null j) (projection_pullback_zeroSet_null R hGen hv hP' hP Ψ hΨ j))
    (ram_pull_null R hGen hv hP' hP Ψ hΨ j)

end pullbackPushforward_holds

end GroundTheory.Heights₂.Heights.Inter
