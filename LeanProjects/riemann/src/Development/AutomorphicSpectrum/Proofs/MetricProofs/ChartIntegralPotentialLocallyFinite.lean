import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsPtsBddConv
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FlagIndices
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StLemmaETailMass
import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PModelFibreSumAeSheet
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PModelFibreFinite
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.LintegralFibSum
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeI
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MixedDensityNonnegOffNullSet
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LocDensDivJacN
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree

namespace GlobalTheory.CompanionTheory.Ar.Giv.Push

open GroundTheory.Heights₂.Heights.LowerBoundFree.ModelFibreSumAlmostEverywhere

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P : Ideal (MRing ι)} {e : ℕ}

def trivLine (ι : K → Type) : HermLine ι where
  a := 0
  h := fun _ => 1
  pos := fun _ _ => one_pos
  smul := fun c z hc => by simp

theorem trivLine_smooth : IsSmoothHerm (trivLine ι) := contDiffOn_const

theorem exists_localInverse (M : CxModel P e) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (E : Set M.Xc) (x : M.Xc) (hx : x ∉ modelBad M Ψ E) (j : Fin M.atlas.n)
    (hj : x ∈ (M.atlas.chart j).source) :
    ∃ σ : (Fin e → ℂ) → (Fin e → ℂ), AnalyticAt ℂ σ (modelQ M Ψ x) ∧
      σ (modelQ M Ψ x) = M.atlas.chart j x ∧
      Complex.normSq (ReciprocityTheory.AnForm.A.jacC σ (modelQ M Ψ x)).det =
        (‖LinearMap.det (fderiv ℂ (modelQ M Ψ ∘ (M.atlas.chart j).symm) (M.atlas.chart j x) :
          (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ))‖ ^ 2)⁻¹ ∧
      ∀ᶠ x' in 𝓝 x, σ (modelQ M Ψ x') = M.atlas.chart j x' ∧ x' ∈ (M.atlas.chart j).source := by
  classical
  set u := M.atlas.chart j x with hudef
  have hsu : (M.atlas.chart j).symm u = x := (M.atlas.chart j).left_inv hj
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
  have hdetinv : LinearMap.det ((Ce.symm : (Fin e → ℂ) →L[ℂ] (Fin e → ℂ)) :
      (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) = (LinearMap.det (Df : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)))⁻¹ := by
    have := ContinuousLinearEquiv.det_coe_symm Ce
    rw [hCe'] at this
    exact this
  refine ⟨F.symm, ?_, ?_, ?_, ?_⟩
  · rw [← hy0]; exact hσa
  · rw [← hy0]; exact hσu
  · rw [← hy0, ReciprocityTheory.AnForm.A.det_jacC, hσd.fderiv, hdetinv, Complex.normSq_inv,
      Complex.normSq_eq_norm_sq]
  · have hopen : IsOpen ((M.atlas.chart j).source ∩ M.atlas.chart j ⁻¹' F.source) :=
      (M.atlas.chart j).isOpen_inter_preimage F.open_source
    filter_upwards [hopen.mem_nhds (⟨hj, hus⟩ : x ∈ (M.atlas.chart j).source ∩ M.atlas.chart j ⁻¹' F.source)]
      with x' hx'
    refine ⟨?_, hx'.1⟩
    have h1 := F.left_inv hx'.2
    rw [hFc] at h1
    simpa only [hQdef, Function.comp_apply, (M.atlas.chart j).left_inv hx'.1] using h1

theorem cxHessian_eq_of_torus (L : HermLine ι) (r : ℝ) {γ γ' : (Fin e → ℂ) → (Σ k, ι k) → ℂ}
    {y : Fin e → ℂ} (hγ : AnalyticAt ℂ γ y) (hγ' : AnalyticAt ℂ γ' y)
    (hy : ∀ k, ∃ i, γ y ⟨k, i⟩ ≠ 0)
    (hrel : ∀ᶠ y' in 𝓝 y, ∃ c : K → ℂ, (∀ k, c k ≠ 0) ∧ γ' y' = bsmul c (γ y'))
    {ψ : (Fin e → ℂ) → ℝ} (hψ : ContDiffAt ℝ 2 ψ y) {G₁ : (Fin e → ℂ) → ℂ}
    (hG₁ : AnalyticAt ℂ G₁ y)
    (hpot : ∀ᶠ y' in 𝓝 y, ψ y' - r * Real.log (L.h (γ y')) = (G₁ y').re) :
    cxHessian (fun y' => r * Real.log (L.h (γ' y'))) y = cxHessian ψ y := by
  choose i0 hi0 using hy
  set t : K → (Fin e → ℂ) → ℂ := fun k y' => γ' y' ⟨k, i0 k⟩ / γ y' ⟨k, i0 k⟩ with ht_def
  have hcont : ∀ᶠ y' in 𝓝 y, ∀ k, γ y' ⟨k, i0 k⟩ ≠ 0 :=
    eventually_all.mpr fun k => (analyticAt_coord hγ ⟨k, i0 k⟩).continuousAt.eventually_ne (hi0 k)
  have hrel' : ∀ᶠ y' in 𝓝 y, (∀ k, t k y' ≠ 0) ∧ γ' y' = bsmul (fun k => t k y') (γ y') := by
    filter_upwards [hcont, hrel] with y' h1 ⟨c, hc, h2⟩
    have htc : ∀ k, t k y' = c k := by
      intro k
      simp only [ht_def, h2]
      exact mul_div_cancel_right₀ _ (h1 k)
    refine ⟨fun k => by rw [htc k]; exact hc k, ?_⟩
    rw [show (fun k => t k y') = c from funext htc]
    exact h2
  obtain ⟨ht0, -⟩ := hrel'.self_of_nhds
  have htan : ∀ k, AnalyticAt ℂ (t k) y := fun k =>
    (analyticAt_coord hγ' ⟨k, i0 k⟩).div (analyticAt_coord hγ ⟨k, i0 k⟩) (hi0 k)
  set G : (Fin e → ℂ) → ℂ :=
    fun y' => (∑ k, ((r * (L.a k : ℝ) : ℝ) : ℂ) * Complex.log (t k y' / t k y)) - G₁ y' with hG
  set C : ℝ := ∑ k, r * (L.a k : ℝ) * Real.log ‖t k y‖ with hC
  have hGan : AnalyticAt ℂ G y := by
    refine AnalyticAt.sub (Finset.analyticAt_fun_sum _ fun k _ => analyticAt_const.mul ?_) hG₁
    refine ((htan k).div analyticAt_const (ht0 k)).clog ?_
    show t k y / t k y ∈ Complex.slitPlane
    rw [div_self (ht0 k)]
    exact Complex.one_mem_slitPlane
  have heq : (fun y' => r * Real.log (L.h (γ' y'))) =ᶠ[𝓝 y] fun y' => ψ y' + (G y').re + C := by
    filter_upwards [hrel', hcont, hpot] with y' ⟨hc, hr⟩ hγ0 hp
    have hpos : 0 < L.h (γ y') := L.pos _ fun k => ⟨i0 k, hγ0 k⟩
    have hsm : L.h (bsmul (fun k => t k y') (γ y')) = (∏ k, ‖t k y'‖ ^ L.a k) * L.h (γ y') :=
      L.smul _ _ hc
    have hne : ∀ k, ‖t k y'‖ ^ L.a k ≠ 0 := fun k => zpow_ne_zero _ (norm_ne_zero_iff.mpr (hc k))
    have hterm : ∀ k, ((((r * (L.a k : ℝ)) : ℝ) : ℂ) * Complex.log (t k y' / t k y)).re =
        r * (L.a k : ℝ) * Real.log ‖t k y'‖ - r * (L.a k : ℝ) * Real.log ‖t k y‖ := by
      intro k
      rw [Complex.re_ofReal_mul, Complex.log_re, norm_div,
        Real.log_div (norm_ne_zero_iff.mpr (hc k)) (norm_ne_zero_iff.mpr (ht0 k)), mul_sub]
    simp only [hG, hC]
    rw [hr, hsm, Real.log_mul (Finset.prod_ne_zero_iff.mpr fun k _ => hne k) hpos.ne',
      Real.log_prod (fun k _ => hne k), Complex.sub_re, Complex.re_sum, ← hp]
    simp only [Real.log_zpow, hterm, Finset.sum_sub_distrib]
    rw [mul_add, Finset.mul_sum]
    simp only [← mul_assoc]
    ring
  rw [cxHessian_congr heq, cxHessian_add_re C hψ hGan]

theorem sheet_cxHessian (M : CxModel P e) {σ : (Fin e → ℂ) → (Fin e → ℂ)}
    {γ' : (Fin e → ℂ) → (Σ k, ι k) → ℂ} {y u : Fin e → ℂ} {x : M.Xc} {j : Fin M.atlas.n}
    (hσ : AnalyticAt ℂ σ y) (hσy : σ y = u) (hu : u ∈ (M.atlas.chart j).target)
    (hsu : (M.atlas.chart j).symm u = x) (hγ' : AnalyticAt ℂ γ' y)
    (hpts : ∀ᶠ y' in 𝓝 y, γ' y' ∈ mcPts P ∧ M.proj (γ' y') = (M.atlas.chart j).symm (σ y'))
    (L : HermLine ι) (r : ℝ) (ϕ : M.Xc → ℝ)
    (hϕ : ContDiffAt ℝ 2 (ϕ ∘ (M.atlas.chart j).symm) u)
    {U : Set M.Xc} (hU : IsOpen U) (hxU : x ∈ U) {s : M.Xc → (Σ k, ι k) → ℂ}
    (hs : ∀ y' ∈ U, s y' ∈ mcPts P ∧ M.proj (s y') = y')
    (hsa : ∀ p, M.atlas.HoloOn U fun y' => s y' p) {G : M.Xc → ℂ} (hG : M.atlas.HoloOn U G)
    (hpot : ∀ y' ∈ U, ϕ y' - r * Real.log (L.h (s y')) = (G y').re) :
    cxHessian (fun y' => r * Real.log (L.h (γ' y'))) y =
      cxHessian ((ϕ ∘ (M.atlas.chart j).symm) ∘ σ) y := by
  have hmem : u ∈ (M.atlas.chart j).target ∩ (M.atlas.chart j).symm ⁻¹' U :=
    ⟨hu, by rw [Set.mem_preimage, hsu]; exact hxU⟩
  have hopen := (M.atlas.chart j).isOpen_inter_preimage_symm hU
  have hev : ∀ᶠ y' in 𝓝 y, σ y' ∈ (M.atlas.chart j).target ∩ (M.atlas.chart j).symm ⁻¹' U :=
    hσ.continuousAt.preimage_mem_nhds (by rw [hσy]; exact hopen.mem_nhds hmem)
  have hγ₁ : AnalyticAt ℂ (fun y' => s ((M.atlas.chart j).symm (σ y'))) y :=
    analyticAt_pi_iff.mpr fun p => (hsa p j u hmem).comp_of_eq hσ hσy
  have hG₁ : AnalyticAt ℂ (fun y' => G ((M.atlas.chart j).symm (σ y'))) y :=
    (hG j u hmem).comp_of_eq hσ hσy
  have hψ : ContDiffAt ℝ 2 ((ϕ ∘ (M.atlas.chart j).symm) ∘ σ) y :=
    ContDiffAt.comp y (by rw [hσy]; exact hϕ) (hσ.contDiffAt.restrict_scalars ℝ)
  refine cxHessian_eq_of_torus L r hγ₁ hγ' ?_ ?_ hψ hG₁ ?_
  · show ∀ k, ∃ i, s ((M.atlas.chart j).symm (σ y)) ⟨k, i⟩ ≠ 0
    rw [hσy, hsu]
    exact (hs x hxU).1.1
  · filter_upwards [hev, hpts] with y' h1 ⟨h2, h3⟩
    have h4 := hs _ h1.2
    obtain ⟨c, hc, h⟩ := (M.fibre _ h4.1 _ h2).mp (h4.2.trans h3.symm)
    exact ⟨c, hc, h⟩
  · filter_upwards [hev] with y' h1
    exact hpot _ h1.2

theorem sheet_density_eq (M : CxModel P e) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (E : Set M.Xc) (x : M.Xc) (hx : x ∉ modelBad M Ψ E) {γ' : (Fin e → ℂ) → (Σ k, ι k) → ℂ}
    (hγ' : IsSheet P Ψ (modelQ M Ψ x) (modelW M Ψ x) γ') (c : Fin e → ℝ) (B : Fin e → HermLine ι)
    (Φ : Fin e → LocPot M.Xc)
    (hsm : ∀ i, ContDiffAt ℝ 2 ((Φ i).φ x ∘ (M.atlas.chart (chartIdx M.atlas x)).symm)
      (M.atlas.chart (chartIdx M.atlas x) x))
    (hsec : ∀ i, ∃ U : Set M.Xc, IsOpen U ∧ x ∈ U ∧ ∃ s : M.Xc → (Σ k, ι k) → ℂ,
      (∀ y' ∈ U, s y' ∈ mcPts P ∧ M.proj (s y') = y') ∧ (∀ p, M.atlas.HoloOn U fun y' => s y' p) ∧
      ∃ G : M.Xc → ℂ, M.atlas.HoloOn U G ∧
        ∀ y' ∈ U, (Φ i).φ x y' - c i * Real.log ((B i).h (s y')) = (G y').re) :
    maDensity (fun i y' => c i * Real.log ((B i).h (γ' y'))) (modelQ M Ψ x) =
      pushDens M.atlas Φ (modelQ M Ψ) x := by
  set j := chartIdx M.atlas x with hjdef
  have hj : x ∈ (M.atlas.chart j).source := Classical.choose_spec (M.atlas.cover x)
  set u := M.atlas.chart j x with hudef
  have hsu : (M.atlas.chart j).symm u = x := (M.atlas.chart j).left_inv hj
  have hu : u ∈ (M.atlas.chart j).target := (M.atlas.chart j).map_source hj
  obtain ⟨σ, hσ, hσy, hnorm, hV⟩ := exists_localInverse M Ψ E x hx j hj
  have han : AnalyticAt ℂ γ' (modelQ M Ψ x) := sheet_analyticAt osgood hγ'
  have hz' : γ' (modelQ M Ψ x) ∈ mcPts P := hγ'.2.self_of_nhds.2.1
  have hproj : M.proj (γ' (modelQ M Ψ x)) = x :=
    proj_eq_of_segre M hz' _ (inv_ne_zero (psi_zero_ne_of_not_mem_bad M Ψ hx)) hγ'.1
  have hcont : Tendsto (fun y' => M.proj (γ' y')) (𝓝 (modelQ M Ψ x)) (𝓝 x) := by
    have h1 : Tendsto γ' (𝓝 (modelQ M Ψ x)) (𝓝[mcPts P] γ' (modelQ M Ψ x)) :=
      tendsto_nhdsWithin_iff.mpr ⟨han.continuousAt.tendsto, hγ'.2.mono fun _ h => h.2.1⟩
    have h2 := (M.cont _ hz').tendsto.comp h1
    rwa [hproj] at h2
  have hpts : ∀ᶠ y' in 𝓝 (modelQ M Ψ x),
      γ' y' ∈ mcPts P ∧ M.proj (γ' y') = (M.atlas.chart j).symm (σ y') := by
    filter_upwards [hγ'.2, hcont.eventually hV] with y' ⟨_, h1, h2⟩ ⟨h3, h4⟩
    obtain ⟨-, hq, -⟩ := mem_fibre_data M Ψ h1 h2
    rw [hq] at h3
    exact ⟨h1, by rw [h3, (M.atlas.chart j).left_inv h4]⟩
  have hH : ∀ i, cxHessian (fun y' => c i * Real.log ((B i).h (γ' y'))) (modelQ M Ψ x) =
      cxHessian (((Φ i).φ x ∘ (M.atlas.chart j).symm) ∘ σ) (modelQ M Ψ x) := by
    intro i
    obtain ⟨U, hU, hxU, s, hs, hsa, G, hG, hpot⟩ := hsec i
    exact sheet_cxHessian M hσ hσy hu hsu han hpts (B i) (c i) _ (hsm i) hU hxU hs hsa hG hpot
  have hma : maDensity (fun i y' => c i * Real.log ((B i).h (γ' y'))) (modelQ M Ψ x) =
      maDensity (fun i => ((Φ i).φ x ∘ (M.atlas.chart j).symm) ∘ σ) (modelQ M Ψ x) := by
    simp only [maDensity, hH]
  have hloc : ReciprocityTheory.AnForm.maDens (fun i => (Φ i).φ x ∘ (M.atlas.chart j).symm) u =
      locDens M.atlas Φ j u := by
    unfold locDens
    rw [hsu]
    rfl
  have hpush : pushDens M.atlas Φ (modelQ M Ψ) x = locDens M.atlas Φ j u /
      ‖LinearMap.det (fderiv ℂ (modelQ M Ψ ∘ (M.atlas.chart j).symm) u :
        (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ))‖ ^ 2 := rfl
  rw [hma, maDensity_eq_maDens, ReciprocityTheory.AnForm.A.maDens_comp
    (fun i => (Φ i).φ x ∘ (M.atlas.chart j).symm) σ _ hσ (fun i => by rw [hσy]; exact hsm i),
    hnorm, hσy, hloc, hpush, div_eq_mul_inv]

theorem fibre_term_ae : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (n : ℕ) (M : CxModel P n) (Q : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)) (Y Z : Set M.Xc) (N : Set ((Σ k, ι k) → ℂ)) (c : Fin n → ℝ) (B : Fin n → HermLine ι) (Φ : Fin n → LocPot M.Xc) (g : ((Σ k, ι k) → ℂ) → ℝ) (G₀ : M.Xc → ℝ), IsArithVar P (n + 1) → IsGoodProj P Q → IsOpen Y → (∀ j, volume ((M.atlas.chart j).target ∩ (M.atlas.chart j).symm ⁻¹' (Yᶜ ∪ Z)) = 0) → IsPtsNull P n N → (∀ i x, M.atlas.SmoothOn ((Φ i).U x ∩ Y) ((Φ i).φ x)) → (∀ i, ∀ x, ∀ y₀ ∈ (Φ i).U x ∩ Y, ∃ U : Set M.Xc, IsOpen U ∧ y₀ ∈ U ∧ U ⊆ (Φ i).U x ∩ Y ∧ ∃ s : M.Xc → (Σ k, ι k) → ℂ, (∀ y' ∈ U, s y' ∈ mcPts (P) ∧ M.proj (s y') = y') ∧ (∀ p, M.atlas.HoloOn U fun y' => s y' p) ∧ ∃ G : M.Xc → ℂ, M.atlas.HoloOn U G ∧ ∀ y' ∈ U, (Φ i).φ x y' - (fun z => c i * Real.log ((B i).h z)) (s y') = (G y').re) → (∀ z ∈ mcPts P, z ∉ N → M.proj z ∈ Y → M.proj z ∉ Z → g z = G₀ (M.proj z)) → ∀ᵐ y, ∃ W : M.Xc → (((k : K) → ι k) → ℂ), Set.InjOn W (modelQ M Q ⁻¹' {y} \ modelBad M Q (Yᶜ ∪ Z)) ∧ fibre P Q y = W '' (modelQ M Q ⁻¹' {y} \ modelBad M Q (Yᶜ ∪ Z)) ∧ ∀ x ∈ modelQ M Q ⁻¹' {y} \ modelBad M Q (Yᶜ ∪ Z), sheetDensity P Q (fun i z => c i * Real.log ((B i).h z)) g y (W x) = G₀ x * pushDens M.atlas Φ (modelQ M Q) x := by
  intro K _ ι _ P n M Q Y Z N c B Φ g G₀ hP hQ hY hnull hN hΦs hΦt hg
  have hnull' : volume ({y : Fin n → ℂ | ∃ z ∈ mcPts P, z ∈ N ∧ Q (segre z) = Fin.cons 1 y} ∪
      modelQ M Q '' (modelBad M Q (Yᶜ ∪ Z) ∩ {x | Q (segre (modelLift M x x)) 0 ≠ 0})) = 0 :=
    measure_union_null (hN Q hQ) (image_bad_null M Q hnull)
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hnull'] with y hy
  have hyN : ¬ ∃ z ∈ mcPts P, z ∈ N ∧ Q (segre z) = Fin.cons 1 y := fun h => hy (Or.inl h)
  have hfib : fibre P Q y = modelW M Q '' (modelQ M Q ⁻¹' {y} \ modelBad M Q (Yᶜ ∪ Z)) := by
    ext w
    constructor
    · rintro ⟨z, hz, rfl, hΨz⟩
      obtain ⟨h0, hq, hw⟩ := mem_fibre_data M Q hz hΨz
      exact ⟨M.proj z, ⟨hq, fun hb => hy (Or.inr ⟨M.proj z, ⟨hb, h0⟩, hq⟩)⟩, hw⟩
    · rintro ⟨x, hx, rfl⟩
      have := modelW_mem_fibre M Q hP.1 hP.2.1.2.1 (psi_zero_ne_of_not_mem_bad M Q hx.2)
      rwa [show modelQ M Q x = y from hx.1] at this
  refine ⟨modelW M Q, (modelW_injOn M Q).mono fun x hx => psi_zero_ne_of_not_mem_bad M Q hx.2, hfib,
    fun x hx => ?_⟩
  have hxy : modelQ M Q x = y := hx.1
  have hxb : x ∉ modelBad M Q (Yᶜ ∪ Z) := hx.2
  subst hxy
  have hxE := notMem_of_notMem_bad M Q hxb
  have hxY : x ∈ Y := by
    by_contra h
    exact hxE (Or.inl h)
  have hxZ : x ∉ Z := fun h => hxE (Or.inr h)
  obtain ⟨γ, hγ, -⟩ := exists_sheet M Q (trivLine ι) 0 (Yᶜ ∪ Z) hP trivLine_smooth x hxb
  have hex : ∃ γ, IsSheet P Q (modelQ M Q x) (modelW M Q x) γ := ⟨γ, hγ⟩
  have hγ' : IsSheet P Q (modelQ M Q x) (modelW M Q x) hex.choose := hex.choose_spec
  have hz' : hex.choose (modelQ M Q x) ∈ mcPts P := hγ'.2.self_of_nhds.2.1
  have hproj : M.proj (hex.choose (modelQ M Q x)) = x :=
    proj_eq_of_segre M hz' _ (inv_ne_zero (psi_zero_ne_of_not_mem_bad M Q hxb)) hγ'.1
  have hgv : g (hex.choose (modelQ M Q x)) = G₀ x :=
    (hg _ hz' (fun hzN => hyN ⟨_, hz', hzN, hγ'.2.self_of_nhds.2.2⟩)
      (by rw [hproj]; exact hxY) (by rw [hproj]; exact hxZ)).trans (by rw [hproj])
  have hsm : ∀ i, ContDiffAt ℝ 2 ((Φ i).φ x ∘ (M.atlas.chart (chartIdx M.atlas x)).symm)
      (M.atlas.chart (chartIdx M.atlas x) x) := by
    intro i
    have hk : x ∈ (M.atlas.chart (chartIdx M.atlas x)).source :=
      Classical.choose_spec (M.atlas.cover x)
    have hxk := (M.atlas.chart (chartIdx M.atlas x)).left_inv hk
    have hmem : M.atlas.chart (chartIdx M.atlas x) x ∈ (M.atlas.chart (chartIdx M.atlas x)).target ∩
        (M.atlas.chart (chartIdx M.atlas x)).symm ⁻¹' ((Φ i).U x ∩ Y) :=
      ⟨(M.atlas.chart _).map_source hk, by
        rw [Set.mem_preimage, hxk]; exact ⟨(Φ i).mem_U x, hxY⟩⟩
    have hop := (M.atlas.chart (chartIdx M.atlas x)).isOpen_inter_preimage_symm
      (((Φ i).isOpen_U x).inter hY)
    exact ((hΦs i x _).contDiffAt (hop.mem_nhds hmem)).of_le (WithTop.coe_le_coe.2 le_top)
  have hsec : ∀ i, ∃ U : Set M.Xc, IsOpen U ∧ x ∈ U ∧ ∃ s : M.Xc → (Σ k, ι k) → ℂ,
      (∀ y' ∈ U, s y' ∈ mcPts P ∧ M.proj (s y') = y') ∧ (∀ p, M.atlas.HoloOn U fun y' => s y' p) ∧
      ∃ G : M.Xc → ℂ, M.atlas.HoloOn U G ∧
        ∀ y' ∈ U, (Φ i).φ x y' - c i * Real.log ((B i).h (s y')) = (G y').re := by
    intro i
    obtain ⟨U, hU, hxU, -, s, hs, hsa, G, hG, hpot⟩ := hΦt i x x ⟨(Φ i).mem_U x, hxY⟩
    exact ⟨U, hU, hxU, s, hs, hsa, G, hG, hpot⟩
  unfold sheetDensity
  rw [dif_pos hex]
  beta_reduce
  rw [hgv, sheet_density_eq M Q (Yᶜ ∪ Z) x hxb hγ' c B Φ hsm hsec]

end GlobalTheory.CompanionTheory.Ar.Giv.Push
