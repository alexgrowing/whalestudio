import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FlagIndices
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Objects
import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.MCoordIdealGenericPointEq
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PChartVelLift
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LeviChartRegularityStatementHolds

set_option maxSynthPendingDepth 1

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Giv

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree

theorem isCompatChart_atlas {e : ℕ} {X : Type*} [TopologicalSpace X] (A : FinHolAtlas e X) (j : Fin A.n) :
    IsCompatChart A (A.chart j) :=
  fun k => ⟨A.holo k j, A.holo j k⟩

theorem potential_pos_of_section :
    ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)] [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (M : XModel D) (Φ : LocPot M.Xc), IsPotential M.atlas Φ → (∀ x, ∀ y₀ ∈ (Φ).U x ∩ Set.univ, ∃ U : Set M.Xc, IsOpen U ∧ y₀ ∈ U ∧ U ⊆ (Φ).U x ∩ Set.univ ∧ ∃ s : M.Xc → (Σ k, ι k) → ℂ, (∀ y' ∈ U, s y' ∈ mcPts (mCoordIdeal D.y) ∧ M.proj (s y') = y') ∧ (∀ p, M.atlas.HoloOn U fun y' => s y' p) ∧ ∃ G : M.Xc → ℂ, M.atlas.HoloOn U G ∧ ∀ y' ∈ U, (Φ).φ x y' - (fun z => Real.log (D.A'.h z)) (s y') = (G y').re) → IsPosPot M.atlas Φ := by
  intro II Ψ _ _ K _ ι _ Ω _ _ E _ _ D M Φ hΦ hloc x j y hy v hv
  classical
  set e := M.atlas.chart j with he
  have hcompat : IsCompatChart M.atlas e := isCompatChart_atlas M.atlas j
  have hsrc : e.symm y ∈ e.source := e.map_target hy.1
  obtain ⟨U, hUo, hyU, hUsub, s, hs, hsh, G, hG, hrel⟩ := hloc x (e.symm y) ⟨hy.2, trivial⟩
  set V : Set (Fin D.n → ℂ) := e.target ∩ e.symm ⁻¹' U with hV
  have hVo : IsOpen V := e.isOpen_inter_preimage_symm hUo
  have hyV : y ∈ V := ⟨hy.1, hyU⟩
  have hVn : V ∈ 𝓝 y := hVo.mem_nhds hyV
  set τ : (Fin D.n → ℂ) → (Σ k, ι k) → ℂ := fun u => s (e.symm u) with hτdef
  have hτ : AnalyticOnNhd ℂ τ V := fun u hu => analyticAt_pi_iff.2 fun p => hsh p j u hu
  have hg : AnalyticAt ℂ (G ∘ e.symm) y := hG j y hyV
  have hτmem : ∀ u ∈ V, τ u ∈ mcPts (mCoordIdeal D.y) ∧ M.proj (τ u) = e.symm u := fun u hu => hs _ hu.2
  have hz : τ y ∈ mcPts (mCoordIdeal D.y) := (hτmem y hyV).1
  have hpz : M.proj (τ y) = e.symm y := (hτmem y hyV).2
  have hτy : AnalyticAt ℂ τ y := hτ y hyV
  set w := fderiv ℂ τ y v with hwdef

  set L : ℂ → Fin D.n → ℂ := fun σ => y + σ • v with hL
  have hLd : HasDerivAt L v 0 := by
    have h := ((hasDerivAt_id (0 : ℂ)).smul_const v).const_add y
    simp only [id, one_smul] at h
    exact h
  have hL0 : L 0 = y := by simp [hL]
  have hLn : ∀ᶠ σ in 𝓝 (0 : ℂ), L σ ∈ V :=
    hLd.continuousAt.preimage_mem_nhds (by rw [hL0]; exact hVn)
  set γ : ℂ → (Σ k, ι k) → ℂ := fun σ => τ (L σ) with hγdef
  have hγ0 : γ 0 = τ y := by simp [hγdef, hL0]
  have hγw : HasDerivAt γ w 0 :=
    (hτy.differentiableAt.hasFDerivAt).comp_hasDerivAt_of_eq (0 : ℂ) hLd hL0.symm

  have htan : IsConeTangent (Int.castRingHom ℂ) (mCoordIdeal D.y) (τ y) w := by
    intro f hf
    have hder := hasDerivAt_eval_comp (map (Int.castRingHom ℂ) f) hγw
    rw [hγ0] at hder
    have hzero : (fun σ => eval (γ σ) (map (Int.castRingHom ℂ) f)) =ᶠ[𝓝 0] fun _ => (0 : ℂ) := by
      filter_upwards [hLn] with σ hσ
      exact (hτmem _ hσ).1.2 f hf
    exact hder.unique ((hasDerivAt_const (0 : ℂ) (0 : ℂ)).congr_of_eventuallyEq hzero)

  have hnt : ∀ c : K → ℂ, w ≠ torusSmul c (τ y) := by
    intro c hwc
    obtain ⟨W, hWo, hzW, F, hFd, hF⟩ :=
      projHoloLocal II Ψ K ι Ω E D M e hcompat (τ y) hz (by rw [hpz]; exact hsrc)
    have hFz : HasFDerivAt F (fderiv ℂ F (τ y)) (τ y) :=
      (hFd.differentiableAt (hWo.mem_nhds hzW)).hasFDerivAt
    have hFγ : HasFDerivAt F (fderiv ℂ F (τ y)) (γ 0) := hγ0 ▸ hFz
    have hWγ : ∀ᶠ σ in 𝓝 (0 : ℂ), γ σ ∈ W :=
      hγw.continuousAt.preimage_mem_nhds (hWo.mem_nhds (hγ0 ▸ hzW))
    have h1 : fderiv ℂ F (τ y) w = v := by
      refine (hFγ.comp_hasDerivAt (0 : ℂ) hγw).unique (hLd.congr_of_eventuallyEq ?_)
      filter_upwards [hLn, hWγ] with σ hσ hσW
      rw [Function.comp_apply, ← (hF (γ σ) ⟨hσW, (hτmem _ hσ).1⟩).2, (hτmem _ hσ).2, e.right_inv hσ.1]
    set δ : ℂ → (Σ k, ι k) → ℂ := fun σ => torusSmul (fun k => Complex.exp (σ * c k)) (τ y) with hδ
    have hδ0 : δ 0 = τ y := by
      funext p
      simp [hδ, torusSmul]
    have hδd : HasDerivAt δ (torusSmul c (τ y)) 0 := by
      refine hasDerivAt_pi.2 fun p => ?_
      have h := (((hasDerivAt_id (0 : ℂ)).mul_const (c p.1)).cexp).mul_const (τ y p)
      simpa [hδ, torusSmul] using h
    have hδmem : ∀ σ, δ σ ∈ mcPts (mCoordIdeal D.y) := fun σ =>
      ComponentDataEquivalence.mcPts_torus D.arith.2.1.2.1 hz fun k => Complex.exp_ne_zero _
    have hδproj : ∀ σ, M.proj (δ σ) = M.proj (τ y) := fun σ =>
      ((M.fibre (τ y) hz (δ σ) (hδmem σ)).2 ⟨_, fun k => Complex.exp_ne_zero _, rfl⟩).symm
    have hWδ : ∀ᶠ σ in 𝓝 (0 : ℂ), δ σ ∈ W :=
      hδd.continuousAt.preimage_mem_nhds (hWo.mem_nhds (hδ0 ▸ hzW))
    have h2 : fderiv ℂ F (τ y) (torusSmul c (τ y)) = 0 := by
      have hFz' : HasFDerivAt F (fderiv ℂ F (τ y)) (δ 0) := hδ0 ▸ hFz
      refine (hFz'.comp_hasDerivAt (0 : ℂ) hδd).unique
        ((hasDerivAt_const (0 : ℂ) (e (M.proj (τ y)))).congr_of_eventuallyEq ?_)
      filter_upwards [hWδ] with σ hσW
      rw [Function.comp_apply, ← (hF (δ σ) ⟨hσW, hδmem σ⟩).2, hδproj σ]
    exact hv (h1.symm.trans (hwc ▸ h2))

  have hO : {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} ∈ 𝓝 (τ y) :=
    MuRegSmooth.isOpen_blocks.mem_nhds hz.1
  have hlogA : ContDiffAt ℝ 2 (fun z => Real.log (D.A'.h z)) (τ y) :=
    ((D.A'_pos.1.contDiffAt hO).of_le (WithTop.coe_le_coe.2 le_top)).log (D.A'.pos _ hz.1).ne'
  have hc1 : ContDiffAt ℝ 2 ((fun z => Real.log (D.A'.h z)) ∘ τ) y :=
    hlogA.comp y (hτy.restrictScalars.contDiffAt (n := 2))
  have hc2 : ContDiffAt ℝ 2 (fun u => ((G ∘ e.symm) u).re) y := by
    have h := (Complex.reCLM.contDiff (n := 2)).contDiffAt.comp y
      (hg.restrictScalars.contDiffAt (n := 2))
    convert h using 1
    funext u
    simp
  have hev : (Φ.φ x ∘ e.symm) =ᶠ[𝓝 y]
      fun u => ((fun z => Real.log (D.A'.h z)) ∘ τ) u + (1 : ℝ) * ((G ∘ e.symm) u).re := by
    filter_upwards [hVn] with u hu
    have := hrel _ hu.2
    simp only [Function.comp_apply, one_mul, hτdef]
    linarith
  have hpos := D.A'_pos.2 (τ y) hz w htan hnt
  rw [levi_congr hev, levi_add_smul 1 hc1 hc2, levi_re_analytic hg, levi_comp v hτy hlogA]
  rw [mul_zero, add_zero]
  exact hpos

end GlobalTheory.CompanionTheory.Ar.Giv
