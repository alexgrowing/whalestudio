import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StChartVelLift
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StProjHoloLocal
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.MCoordIdealGenericPointEq
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

theorem hasDerivAt_eval_comp {σ : Type*} [Fintype σ] (f : MvPolynomial σ ℂ) {γ : ℂ → σ → ℂ} {w : σ → ℂ} {t : ℂ}
    (hγ : HasDerivAt γ w t) :
    HasDerivAt (fun s => eval (γ s) f) (∑ i, eval (γ t) (pderiv i f) * w i) t := by
  classical
  induction f using MvPolynomial.induction_on with
  | C a => simpa using hasDerivAt_const t a
  | add p q hp hq =>
    have hf : (fun s => eval (γ s) (p + q)) = fun s => eval (γ s) p + eval (γ s) q := by
      funext s
      simp
    rw [hf]
    refine (hp.add hq).congr_deriv ?_
    simp only [map_add, add_mul, Finset.sum_add_distrib]
  | mul_X p n hp =>
    have hn : HasDerivAt (fun s => γ s n) (w n) t := hasDerivAt_pi.1 hγ n
    have hf : (fun s => eval (γ s) (p * X n)) = fun s => eval (γ s) p * γ s n := by
      funext s
      simp
    rw [hf]
    refine (hp.mul hn).congr_deriv ?_
    have hs : ∑ i, eval (γ t) (pderiv i (p * X n)) * w i =
        ∑ i, eval (γ t) (pderiv i p) * w i * γ t n + ∑ i, eval (γ t) p * ((Pi.single n (1 : ℂ) : σ → ℂ) i * w i) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Derivation.leibniz, pderiv_X, smul_eq_mul, map_add, map_mul, eval_X]
      by_cases h : i = n
      · subst h
        simp
        ring
      · simp [h, Ne.symm h]
        ring
    rw [hs, ← Finset.mul_sum, ← Finset.sum_mul]
    congr 2
    simp [Pi.single_apply]

theorem ChartVelLift.proof (hP : ProjHoloLocal.Statement) : ChartVelLift.Statement := by
  intro II Ψ _ _ K _ ι _ Ω _ _ E _ _ D O Lt _ _ _ X k y hy v hv
  classical
  have hcompat : ReciprocityTheory.AnForm.M.IsCompatChart X.M.atlas (X.S.R.chart k) := X.S.R.compat k
  have hx : (X.S.R.chart k).symm y ∈ (X.S.R.chart k).source := (X.S.R.chart k).map_target hy
  obtain ⟨U, hUo, hxU, s, hs, hshol⟩ := X.M.sections ((X.S.R.chart k).symm y)
  obtain ⟨j, hj⟩ := X.M.atlas.cover ((X.S.R.chart k).symm y)

  set V : Set (Fin D.n → ℂ) := (X.S.R.chart k).target ∩
    (X.S.R.chart k).symm ⁻¹' (U ∩ (X.M.atlas.chart j).source) with hV
  have hVo : IsOpen V := (X.S.R.chart k).continuousOn_symm.isOpen_inter_preimage (X.S.R.chart k).open_target
    (hUo.inter (X.M.atlas.chart j).open_source)

  have hanal : ∀ u ∈ V, ∀ p, AnalyticAt ℂ (fun u => s ((X.S.R.chart k).symm u) p) u := by
    intro u hu p
    have h1 : AnalyticAt ℂ (X.M.atlas.chart j ∘ (X.S.R.chart k).symm) u :=
      (hcompat j).2 u ⟨hu.1, hu.2.2⟩
    have h2 : AnalyticAt ℂ ((fun y' => s y' p) ∘ (X.M.atlas.chart j).symm)
        ((X.M.atlas.chart j ∘ (X.S.R.chart k).symm) u) := by
      refine hshol p j _ ⟨(X.M.atlas.chart j).map_source hu.2.2, ?_⟩
      show (X.M.atlas.chart j).symm ((X.M.atlas.chart j) ((X.S.R.chart k).symm u)) ∈ U
      rw [(X.M.atlas.chart j).left_inv hu.2.2]
      exact hu.2.1
    refine (h2.comp h1).congr ?_
    filter_upwards [hVo.mem_nhds hu] with u' hu'
    simp only [Function.comp_apply]
    rw [(X.M.atlas.chart j).left_inv hu'.2.2]

  set L : ℂ → Fin D.n → ℂ := fun σ => y + σ • v with hL
  have hLd : ∀ σ, HasDerivAt L v σ := fun σ => by
    have h := ((hasDerivAt_id σ).smul_const v).const_add y
    simp only [id, one_smul] at h
    exact h
  have hL0 : L 0 = y := by simp [hL]
  set T : Set ℂ := L ⁻¹' V with hT
  have hTo : IsOpen T := hVo.preimage (continuous_const.add (continuous_id.smul continuous_const))
  have hT0 : (0 : ℂ) ∈ T := by
    show L 0 ∈ V
    rw [hL0]
    exact ⟨hy, hxU, hj⟩
  set γ : ℂ → (Σ k, ι k) → ℂ := fun σ => s ((X.S.R.chart k).symm (L σ)) with hγdef
  have hγd : ∀ σ ∈ T, DifferentiableAt ℂ γ σ := fun σ hσ =>
    differentiableAt_pi.2 fun p => (hanal (L σ) hσ p).differentiableAt.comp σ (hLd σ).differentiableAt
  have hγmem : ∀ σ ∈ T, γ σ ∈ mcPts (mCoordIdeal D.y) ∧
      X.M.proj (γ σ) = (X.S.R.chart k).symm (L σ) := fun σ hσ => hs _ hσ.2.1
  have hγ0 : γ 0 = s ((X.S.R.chart k).symm y) := by simp [hγdef, hL0]
  have hγw : HasDerivAt γ (deriv γ 0) 0 := (hγd 0 hT0).hasDerivAt
  have hTn : T ∈ 𝓝 (0 : ℂ) := hTo.mem_nhds hT0

  have hline : (fun σ => X.S.R.chart k (X.M.proj (γ σ))) =ᶠ[𝓝 0] L := by
    filter_upwards [hTn] with σ hσ
    rw [(hγmem σ hσ).2, (X.S.R.chart k).right_inv hσ.1]
  have hz : γ 0 ∈ mcPts (mCoordIdeal D.y) := (hγmem 0 hT0).1
  have hpz : X.M.proj (γ 0) = (X.S.R.chart k).symm y := by rw [(hγmem 0 hT0).2, hL0]
  refine ⟨γ 0, hz, hpz, deriv γ 0, ⟨γ, rfl, hγw, ?_, (hLd 0).congr_of_eventuallyEq hline⟩, ?_, ?_⟩
  · filter_upwards [hTn] with σ hσ
    exact ⟨hγd σ hσ, (hγmem σ hσ).1⟩
  ·
    intro f hf
    have hder := hasDerivAt_eval_comp (map (Int.castRingHom ℂ) f) hγw
    have hzero : (fun σ => eval (γ σ) (map (Int.castRingHom ℂ) f)) =ᶠ[𝓝 0] fun _ => (0 : ℂ) := by
      filter_upwards [hTn] with σ hσ
      exact (hγmem σ hσ).1.2 f hf
    exact hder.unique ((hasDerivAt_const (0 : ℂ) (0 : ℂ)).congr_of_eventuallyEq hzero)
  ·
    intro c hwc
    obtain ⟨W, hWo, hzW, F, hFd, hF⟩ :=
      hP II Ψ K ι Ω E D X.M (X.S.R.chart k) hcompat (γ 0) hz (by rw [hpz]; exact hx)
    have hFz : HasFDerivAt F (fderiv ℂ F (γ 0)) (γ 0) :=
      (hFd.differentiableAt (hWo.mem_nhds hzW)).hasFDerivAt

    have hWγ : ∀ᶠ σ in 𝓝 (0 : ℂ), γ σ ∈ W := hγw.continuousAt.preimage_mem_nhds (hWo.mem_nhds hzW)
    have h1 : fderiv ℂ F (γ 0) (deriv γ 0) = v := by
      refine (hFz.comp_hasDerivAt (0 : ℂ) hγw).unique ((hLd 0).congr_of_eventuallyEq ?_)
      filter_upwards [hTn, hWγ, hline] with σ hσ hσW hσl
      rw [Function.comp_apply, ← (hF (γ σ) ⟨hσW, (hγmem σ hσ).1⟩).2]
      exact hσl

    set δ : ℂ → (Σ k, ι k) → ℂ := fun σ => torusSmul (fun k => Complex.exp (σ * c k)) (γ 0) with hδ
    have hδ0 : δ 0 = γ 0 := by
      funext p
      simp [hδ, torusSmul]
    have hδd : HasDerivAt δ (torusSmul c (γ 0)) 0 := by
      refine hasDerivAt_pi.2 fun p => ?_
      have h := (((hasDerivAt_id (0 : ℂ)).mul_const (c p.1)).cexp).mul_const (γ 0 p)
      simpa [hδ, torusSmul] using h
    have hδmem : ∀ σ, δ σ ∈ mcPts (mCoordIdeal D.y) := fun σ =>
      ComponentDataEquivalence.mcPts_torus D.arith.2.1.2.1 hz fun k => Complex.exp_ne_zero _
    have hδproj : ∀ σ, X.M.proj (δ σ) = X.M.proj (γ 0) := fun σ =>
      ((X.M.fibre (γ 0) hz (δ σ) (hδmem σ)).2 ⟨_, fun k => Complex.exp_ne_zero _, rfl⟩).symm
    have hWδ : ∀ᶠ σ in 𝓝 (0 : ℂ), δ σ ∈ W := by
      have := hδd.continuousAt.preimage_mem_nhds (hWo.mem_nhds (hδ0 ▸ hzW))
      exact this
    have h2 : fderiv ℂ F (γ 0) (torusSmul c (γ 0)) = 0 := by
      have hFz' : HasFDerivAt F (fderiv ℂ F (γ 0)) (δ 0) := hδ0 ▸ hFz
      refine (hFz'.comp_hasDerivAt (0 : ℂ) hδd).unique
        ((hasDerivAt_const (0 : ℂ) (X.S.R.chart k (X.M.proj (γ 0)))).congr_of_eventuallyEq ?_)
      filter_upwards [hWδ] with σ hσW
      rw [Function.comp_apply, ← (hF (δ σ) ⟨hσW, hδmem σ⟩).2, hδproj σ]
    exact hv (h1.symm.trans (hwc ▸ h2))

end GroundTheory.Heights₂.Heights.LowerBoundFree
