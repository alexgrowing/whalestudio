import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeE
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeK
import ReciprocityTheory.AnalyticForms.AnalyticCharts.NullZero

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial MeasureTheory ReciprocityTheory.AnForm.M Topology Filter Set

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {P J : Ideal (MRing ι)} {e : ℕ} (R : AnLogRes P J e)

theorem brFib_finite' (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (hP : IsArithVar P (e + 1)) (hΨ : IsGoodProj P Ψ) (y : Fin e → ℂ) :
    (brQ R Ψ ⁻¹' {y} ∩ {x | R.lift x x ∉ mcPts J ∧ Ψ (segre (R.lift x x)) 0 ≠ 0}).Finite := by
  have hK : Nonempty K := hP.1
  have hPh : IsMultiHomogIdeal P := hP.2.1.2.1

  refine Set.Finite.of_finite_image (f := brW R Ψ) ?_ ((brW_injOn R Ψ).mono Set.inter_subset_right)
  refine (fibreFinite K ι P e Ψ hP hΨ y).subset ?_
  rintro _ ⟨x, ⟨hxy, hx⟩, rfl⟩
  rw [Set.mem_preimage, Set.mem_singleton_iff] at hxy
  have h := brW_mem_fibre R Ψ hK hPh hx.2
  rwa [hxy] at h

theorem lift_mem_iff {x z : R.X} (hz : z ∈ R.U x) :
    R.lift z z ∈ mcPts J ↔ R.lift x z ∈ mcPts J := by
  have h1 : SameOrbit (R.lift z z) (R.lift x z) := R.compat z x z ⟨R.mem_U z, hz⟩
  have h2 : SameOrbit (R.lift x z) (R.lift z z) := R.compat x z z ⟨hz, R.mem_U z⟩
  exact ⟨mem_mcPts_of_sameOrbit R.homog h2, mem_mcPts_of_sameOrbit R.homog h1⟩

theorem psi_lift_eq {x z : R.X} (hz : z ∈ R.U x)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) :
    ∃ μ : ℂ, μ ≠ 0 ∧ Ψ (segre (R.lift z z)) = μ • Ψ (segre (R.lift x z)) := by
  obtain ⟨c, hc, heq⟩ := R.compat z x z ⟨R.mem_U z, hz⟩
  refine ⟨∏ k, c k, Finset.prod_ne_zero_iff.2 fun k _ => hc k, ?_⟩
  rw [heq, segre_smul, map_smul]

theorem isOpen_chart_notB (j : Fin R.A.n) :
    IsOpen ((R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' {x | R.lift x x ∉ mcPts J}) := by
  have hS : IsOpen {x : R.X | R.lift x x ∉ mcPts J} := by
    rw [isOpen_iff_forall_mem_open]
    intro x0 hx0
    have hP0 : R.lift x0 x0 ∈ mcPts P := R.mem x0 x0 (R.mem_U x0)

    have hex : ∃ f ∈ J, eval (R.lift x0 x0) (map (Int.castRingHom ℂ) f) ≠ 0 := by
      by_contra hcon
      exact hx0 ⟨hP0.1, fun f hf => not_not.1 fun h => hcon ⟨f, hf, h⟩⟩
    obtain ⟨f, hfJ, hf⟩ := hex
    have hcont : ContinuousOn (fun z => eval (R.lift x0 z) (map (Int.castRingHom ℂ) f)) (R.U x0) := by
      have hl : ContinuousOn (fun z => R.lift x0 z) (R.U x0) :=
        continuousOn_pi.2 fun p => continuousOn_lift R x0 p
      exact (MvPolynomial.continuous_eval _).comp_continuousOn hl
    refine ⟨R.U x0 ∩ (fun z => eval (R.lift x0 z) (map (Int.castRingHom ℂ) f)) ⁻¹' {w | w ≠ 0},
      ?_, hcont.isOpen_inter_preimage (R.isOpen_U x0) isOpen_ne, ⟨R.mem_U x0, hf⟩⟩
    rintro z ⟨hz, hzf⟩
    show R.lift z z ∉ mcPts J
    rw [lift_mem_iff R hz]
    exact fun h => hzf (h.2 f hfJ)
  exact (R.A.chart j).isOpen_inter_preimage_symm hS

theorem not_flat (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (hP : IsArithVar P (e + 1)) (hΨ : IsGoodProj P Ψ) (j : Fin R.A.n) {O : Set (Fin e → ℂ)}
    (hO : IsOpen O) (hOt : O ⊆ (R.A.chart j).target) (hne : O.Nonempty)
    (h0 : ∀ u ∈ O, Ψ (segre (R.lift ((R.A.chart j).symm u) ((R.A.chart j).symm u))) 0 ≠ 0)
    (han : AnalyticOnNhd ℂ (brQ R Ψ ∘ (R.A.chart j).symm) O)
    (hdet : ∀ u ∈ O, LinearMap.det (fderiv ℂ (brQ R Ψ ∘ (R.A.chart j).symm) u :
      (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) = 0) : False := by

  set O' := O ∩ ((R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' {x | R.lift x x ∉ mcPts J})
  have hO' : IsOpen O' := hO.inter (isOpen_chart_notB R j)
  have hO'ne : O'.Nonempty := by
    by_contra hcon
    rw [Set.not_nonempty_iff_eq_empty] at hcon
    have hsub : O ⊆ (R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' {x | R.lift x x ∈ mcPts J} := by
      intro u hu
      refine ⟨hOt hu, ?_⟩
      by_contra hb
      have hu' : u ∈ O' := ⟨hu, hOt hu, hb⟩
      rw [hcon] at hu'
      exact hu'
    exact (hO.measure_pos volume hne).ne' (measure_mono_null hsub (R.null j))

  obtain ⟨y, hy⟩ := exists_infinite_fibre hO' hO'ne (han.mono Set.inter_subset_left)
    (fun u hu => hdet u hu.1)
  apply hy
  refine Set.Finite.of_finite_image (f := (R.A.chart j).symm) ?_
    ((R.A.chart j).symm.injOn.mono fun u hu => hu.1.2.1)
  refine (brFib_finite' R Ψ hP hΨ y).subset ?_
  rintro _ ⟨u, ⟨huO', huy⟩, rfl⟩
  exact ⟨huy, huO'.2.2, h0 u huO'.1⟩

theorem analyticAt_det_fderiv {Q : (Fin e → ℂ) → (Fin e → ℂ)} {u : Fin e → ℂ}
    (hQ : AnalyticAt ℂ Q u) :
    AnalyticAt ℂ (fun v => LinearMap.det (fderiv ℂ Q v : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ))) u := by
  have hF : AnalyticAt ℂ (fderiv ℂ Q) u := hQ.fderiv

  have hentry : ∀ i j : Fin e, AnalyticAt ℂ
      (fun v => LinearMap.toMatrix' (fderiv ℂ Q v : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) i j) u := by
    intro i j
    have hL : AnalyticAt ℂ (fun L : (Fin e → ℂ) →L[ℂ] (Fin e → ℂ) => L (Pi.single j 1) i)
        (fderiv ℂ Q u) := by
      have h := ContinuousLinearMap.analyticAt
        ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin e => ℂ) i).comp
          (ContinuousLinearMap.apply ℂ (Fin e → ℂ) (Pi.single j (1 : ℂ)))) (fderiv ℂ Q u)
      exact h
    have heq : (fun v => LinearMap.toMatrix' (fderiv ℂ Q v : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) i j) =
        fun v => fderiv ℂ Q v (Pi.single j 1) i := by
      funext v
      rw [LinearMap.toMatrix'_apply, ContinuousLinearMap.coe_coe]
    rw [heq]
    exact hL.comp hF

  have hdet : (fun v => LinearMap.det (fderiv ℂ Q v : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ))) =
      fun v => (LinearMap.toMatrix' (fderiv ℂ Q v : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ))).det := by
    funext v
    rw [LinearMap.det_toMatrix']
  rw [hdet]
  simp only [Matrix.det_apply, Units.smul_def, zsmul_eq_mul]
  refine Finset.analyticAt_fun_sum _ fun σ _ => ?_
  exact analyticAt_const.mul (Finset.analyticAt_fun_prod _ fun i _ => hentry _ _)

theorem det_eq_zero_of_coord {L : (Fin e → ℂ) →L[ℂ] (Fin e → ℂ)} (m : Fin e)
    (h : ∀ v, L v m = 0) : LinearMap.det (L : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) = 0 := by
  by_contra hd

  have hu : IsUnit (L : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) :=
    (LinearMap.isUnit_iff_isUnit_det _).2 (Ne.isUnit hd)
  obtain ⟨v, hv⟩ := ((Module.End.isUnit_iff _).1 hu).2 (Pi.single m 1)
  rw [ContinuousLinearMap.coe_coe] at hv
  have hvm := congrFun hv m
  rw [h v, Pi.single_eq_same] at hvm
  exact zero_ne_one hvm

theorem det_brQ_chart (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) {x : R.X}
    {j k : Fin R.A.n} (hj : x ∈ (R.A.chart j).source) (hk : x ∈ (R.A.chart k).source)
    (h0 : Ψ (segre (R.lift x x)) 0 ≠ 0) :
    LinearMap.det (fderiv ℂ (brQ R Ψ ∘ (R.A.chart j).symm) (R.A.chart j x) :
        (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) =
      LinearMap.det (fderiv ℂ (brQ R Ψ ∘ (R.A.chart k).symm) (R.A.chart k x) :
        (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) *
      LinearMap.det (fderiv ℂ (R.A.chart k ∘ (R.A.chart j).symm) (R.A.chart j x) :
        (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) := by
  have hxj : (R.A.chart j).symm (R.A.chart j x) = x := (R.A.chart j).left_inv hj
  have hmem : R.A.chart j x ∈ (R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' (R.A.chart k).source :=
    ⟨(R.A.chart j).map_source hj, show (R.A.chart j).symm (R.A.chart j x) ∈ (R.A.chart k).source by
      rw [hxj]; exact hk⟩
  have hT : AnalyticAt ℂ (R.A.chart k ∘ (R.A.chart j).symm) (R.A.chart j x) := R.A.holo j k _ hmem
  have hQk : AnalyticAt ℂ (brQ R Ψ ∘ (R.A.chart k).symm) (R.A.chart k x) :=
    analyticAt_brQ R Ψ x k hk h0

  have hev : (brQ R Ψ ∘ (R.A.chart j).symm) =ᶠ[𝓝 (R.A.chart j x)]
      (brQ R Ψ ∘ (R.A.chart k).symm) ∘ (R.A.chart k ∘ (R.A.chart j).symm) := by
    have hn : (R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' (R.A.chart k).source ∈
        𝓝 (R.A.chart j x) :=
      ((R.A.chart j).isOpen_inter_preimage_symm (R.A.chart k).open_source).mem_nhds hmem
    filter_upwards [hn] with v hv
    simp only [Function.comp_apply]
    rw [(R.A.chart k).left_inv hv.2]
  have hfx : (R.A.chart k ∘ (R.A.chart j).symm) (R.A.chart j x) = R.A.chart k x := by
    simp only [Function.comp_apply]
    rw [hxj]
  have hg : DifferentiableAt ℂ (brQ R Ψ ∘ (R.A.chart k).symm)
      ((R.A.chart k ∘ (R.A.chart j).symm) (R.A.chart j x)) := by
    rw [hfx]
    exact hQk.differentiableAt
  rw [hev.fderiv_eq, fderiv_comp _ hg hT.differentiableAt, hfx]
  exact LinearMap.det_comp _ _

end ReciprocityTheory.ChartRestriction.G.Geo
