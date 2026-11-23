import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsPeriodAtRestrict
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IntegralClosureHeightEqOneOfLiesOver
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FiniteMinimalPrimes
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SncResolutionRegularLocalRingStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SncResolutionCoverAndCone
import ReciprocityTheory.AnalyticForms.RegularLocalRings.AnChart
import ReciprocityTheory.AnalyticForms.RegularLocalRings.LocTransfer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterAlgRes
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterMinor
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open MvPolynomial

namespace GlobalTheory.CompanionTheory.Ar.ChartParams

theorem eval_unren_eq_zero {σ : Type} [Fintype σ] (Q : Ideal (MvPolynomial σ ℂ))
    (v : Fin (Fintype.card σ) → ℂ)
    (hv : v ∈ ReciprocityTheory.AnForm.R.zeroSet (Q.map (ReciprocityTheory.AnForm.R.renR σ : MvPolynomial σ ℂ →+* _))) :
    ∀ f ∈ Q, eval (fun q => v (Fintype.equivFin σ q)) f = 0 := by
  intro f hf
  have h1 := hv (ReciprocityTheory.AnForm.R.renC σ f) (Ideal.mem_map_of_mem _ hf)
  have h2 := ReciprocityTheory.AnForm.R.eval_renC (fun q => v (Fintype.equivFin σ q)) f
  have h3 : ReciprocityTheory.AnForm.R.renPt (fun q => v (Fintype.equivFin σ q)) = v := by
    funext j; simp [ReciprocityTheory.AnForm.R.renPt]
  rw [h3, h1] at h2
  exact h2.symm

theorem analyticOnNhd_rescale {σ : Type} {n m : ℕ} (e : σ ≃ Fin m) (g : (Fin n → ℂ) → Fin m → ℂ)
    (V : Set (Fin n → ℂ)) (hg : AnalyticOnNhd ℂ g V) (ε : ℝ) (hεV : Metric.ball 0 ε ⊆ V) (hε : 0 < ε) :
    ∀ t ∈ Metric.ball (0 : Fin n → ℂ) 1, ∀ q, AnalyticAt ℂ (fun s => g ((ε : ℂ) • s) (e q)) t := by
  intro t ht q
  have hmem : (ε : ℂ) • t ∈ V := by
    apply hεV
    rw [mem_ball_zero_iff] at ht ⊢
    rw [norm_smul]
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε]
    nlinarith
  have h1 : AnalyticAt ℂ (fun s : Fin n → ℂ => (ε : ℂ) • s) t :=
    ((ε : ℂ) • ContinuousLinearMap.id ℂ (Fin n → ℂ)).analyticAt t
  have h2 : AnalyticAt ℂ (fun s => g ((ε : ℂ) • s)) t :=
    AnalyticAt.comp (f := fun s : Fin n → ℂ => (ε : ℂ) • s) (hg _ hmem) h1
  exact (analyticAt_pi_iff (f := fun l s => g ((ε : ℂ) • s) l)).mp h2 (e q)

theorem eq_zero_of_fderiv_eq_zero {σ : Type} [Fintype σ] {n m : ℕ} (e : σ ≃ Fin m)
    (r : Fin n → MvPolynomial (Fin m) ℂ) (gm : (Fin n → ℂ) → σ → ℂ) (ε : ℂ) (hε : ε ≠ 0)
    (t : Fin n → ℂ) (hgm : DifferentiableAt ℂ gm t)
    (hr : ∀ᶠ s in nhds t, ReciprocityTheory.AnForm.R.evalFam r (fun j => gm s (e.symm j)) = ε • s)
    (v : Fin n → ℂ) (hv : fderiv ℂ gm t v = 0) : v = 0 := by
  let R : (σ → ℂ) → Fin n → ℂ := fun y i => eval (fun j => y (e.symm j)) (r i)
  have hR : DifferentiableAt ℂ R (gm t) := by
    have han : AnalyticAt ℂ R (gm t) := by
      rw [analyticAt_pi_iff]
      intro i
      refine ReciprocityTheory.AnForm.R.analyticAt_eval_of_pi
        (f := fun (y : σ → ℂ) (j : Fin m) => y (e.symm j)) (fun l => ?_) (r i)
      exact (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : σ => ℂ) (e.symm l)).analyticAt _
    exact han.differentiableAt
  have hc : HasFDerivAt (R ∘ gm) ((fderiv ℂ R (gm t)).comp (fderiv ℂ gm t)) t :=
    hR.hasFDerivAt.comp t hgm.hasFDerivAt
  have hs : HasFDerivAt (R ∘ gm) (ε • ContinuousLinearMap.id ℂ (Fin n → ℂ)) t := by
    have h0 : HasFDerivAt (fun s : Fin n → ℂ => ε • s)
        (ε • ContinuousLinearMap.id ℂ (Fin n → ℂ)) t :=
      (hasFDerivAt_id t).const_smul ε
    exact h0.congr_of_eventuallyEq hr
  have heq := hc.unique hs
  have h1 := congrArg (fun L => L v) heq
  simp only [ContinuousLinearMap.comp_apply, hv, map_zero, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply] at h1
  exact (smul_eq_zero.mp h1.symm).resolve_left hε

theorem sncChart_of_regular_parameters : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (P : Ideal (MRing J))
    (hP : ReciprocityTheory.AnForm.R.IsMultiHomogIdeal (pC P)) (n : ℕ) (Bd : Set ((Σ k, J k) → ℂ)) (c : (k : K) → J k)
    (w : (Σ k, J k) → ℂ), w ∈ mcPts P → (∀ k, w ⟨k, c k⟩ ≠ 0) →
    ∀ (a : ℕ) (r : Fin n → MvPolynomial (Fin (Fintype.card (Σ k, J k))) ℂ)
      (h : MvPolynomial (Fin (Fintype.card (Σ k, J k))) ℂ)
      [IsRegularLocalRing (ReciprocityTheory.AnForm.R.locRing (Cmp.SncRes.ideal (pC P) c)
        (ReciprocityTheory.AnForm.R.renPt (ReciprocityTheory.AnForm.R.affCoord c w)))],
    ringKrullDim (ReciprocityTheory.AnForm.R.locRing (Cmp.SncRes.ideal (pC P) c)
      (ReciprocityTheory.AnForm.R.renPt (ReciprocityTheory.AnForm.R.affCoord c w))) = n → a ≤ n →
    Ideal.span (Set.range fun i => algebraMap _ (ReciprocityTheory.AnForm.R.locRing (Cmp.SncRes.ideal (pC P) c)
      (ReciprocityTheory.AnForm.R.renPt (ReciprocityTheory.AnForm.R.affCoord c w))) (r i)) =
      Ideal.map (algebraMap _ (ReciprocityTheory.AnForm.R.locRing (Cmp.SncRes.ideal (pC P) c)
        (ReciprocityTheory.AnForm.R.renPt (ReciprocityTheory.AnForm.R.affCoord c w))))
        (ReciprocityTheory.AnForm.R.ptIdeal (ReciprocityTheory.AnForm.R.renPt (ReciprocityTheory.AnForm.R.affCoord c w))) →
    (∀ i, eval (ReciprocityTheory.AnForm.R.renPt (ReciprocityTheory.AnForm.R.affCoord c w)) (r i) = 0) →
    eval (ReciprocityTheory.AnForm.R.renPt (ReciprocityTheory.AnForm.R.affCoord c w)) h ≠ 0 →
    (∀ v ∈ ReciprocityTheory.AnForm.R.zeroSet (Cmp.SncRes.ideal (pC P) c), eval v h ≠ 0 →
      ((fun q => v (Fintype.equivFin (Σ k, J k) q)) ∈ Bd ↔ ∃ i : Fin n, (i : ℕ) < a ∧ eval v (r i) = 0)) →
    ∃ (χ : SncChart P n Bd) (O : Set ((Σ k, J k) → ℂ)), IsOpen O ∧ w ∈ O ∧
      ∀ z ∈ O ∩ mcPts P, ∃ t : Fin n → ℂ, ‖t‖ ≤ 1 / 2 ∧ ∃ c' : K → ℂ, (∀ k, c' k ≠ 0) ∧
        z = torusSmul c' (χ.γ t) := by
  intro K _ J _ P hP n Bd c w hw hwc a r h _ hdim haN hspan hr0 hh0 hbd
  classical
  set I := Cmp.SncRes.ideal (pC P) c with hI
  set p := ReciprocityTheory.AnForm.R.renPt (ReciprocityTheory.AnForm.R.affCoord c w) with hp
  have hcone : ∀ z, z ∈ mcPts P → (∀ k, z ⟨k, c k⟩ ≠ 0) →
      ReciprocityTheory.AnForm.R.renPt (ReciprocityTheory.AnForm.R.affCoord c z) ∈ ReciprocityTheory.AnForm.R.zeroSet I := by
    intro z hz hzc
    have h1 := (ReciprocityTheory.AnForm.R.mem_conePts_iff_chartIdeal hP c z hzc).1
      ((mem_mcPts_iff_conePts_pC P z).1 hz)
    exact ReciprocityTheory.AnForm.R.renPt_zero _ _ h1
  have hpz : p ∈ ReciprocityTheory.AnForm.R.zeroSet I := hcone w hw hwc
  obtain ⟨U, V, g, hU, hpU, hV, hg, hbij, hrg⟩ :=
    ReciprocityTheory.AnForm.R.exists_holo_coords I p n hdim r hspan

  have hsolve : ∀ v ∈ U ∩ ReciprocityTheory.AnForm.R.zeroSet I,
      ReciprocityTheory.AnForm.R.evalFam r v ∈ V ∧ g (ReciprocityTheory.AnForm.R.evalFam r v) = v := by
    intro v hv
    obtain ⟨u, hu, rfl⟩ := hbij.surjOn hv
    rw [hrg u hu]
    exact ⟨hu, rfl⟩
  have hr0' : ReciprocityTheory.AnForm.R.evalFam r p = 0 := funext hr0
  obtain ⟨h0V, hg0⟩ := hsolve p ⟨hpU, hpz⟩
  rw [hr0'] at h0V hg0

  have hcont0 : ContinuousAt g 0 := (hg 0 h0V).continuousAt
  have hnear : ∀ᶠ u in nhds (0 : Fin n → ℂ), u ∈ V ∧ eval (g u) h ≠ 0 := by
    have hVn : ∀ᶠ u in nhds (0 : Fin n → ℂ), u ∈ V := hV.mem_nhds h0V
    refine hVn.and ?_
    have hc : ContinuousAt (fun u => eval (g u) h) 0 :=
      (MvPolynomial.continuous_eval h).continuousAt.comp hcont0
    refine hc.eventually_ne ?_
    rw [hg0]; exact hh0
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1 hnear
  have hεV : Metric.ball (0 : Fin n → ℂ) ε ⊆ V := fun u hu => (hball u hu).1
  have hεc : (ε : ℂ) ≠ 0 := by exact_mod_cast hε.ne'
  have hsc : ∀ t ∈ Metric.ball (0 : Fin n → ℂ) 1, (ε : ℂ) • t ∈ Metric.ball (0 : Fin n → ℂ) ε := by
    intro t ht
    rw [mem_ball_zero_iff] at ht ⊢
    rw [norm_smul]
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε]
    nlinarith
  let e := Fintype.equivFin (Σ k, J k)
  let gm : (Fin n → ℂ) → (Σ k, J k) → ℂ := fun t q => g ((ε : ℂ) • t) (e q)

  have hzs : ∀ t ∈ Metric.ball (0 : Fin n → ℂ) 1, g ((ε : ℂ) • t) ∈ ReciprocityTheory.AnForm.R.zeroSet I :=
    fun t ht => (hbij.mapsTo (hεV (hsc t ht))).2
  have hchart : ∀ t ∈ Metric.ball (0 : Fin n → ℂ) 1,
      gm t ∈ ReciprocityTheory.AnForm.R.conePts (pC P) ∧ ∀ k, gm t ⟨k, c k⟩ = 1 := by
    intro t ht
    have h1 := ReciprocityTheory.AnForm.R.conePts_of_chartIdeal hP c (gm t)
      (eval_unren_eq_zero _ _ (hzs t ht))
    exact ⟨h1.1, h1.2.1⟩
  have hcoord : ∀ t ∈ Metric.ball (0 : Fin n → ℂ) 1,
      ReciprocityTheory.AnForm.R.evalFam r (g ((ε : ℂ) • t)) = (ε : ℂ) • t :=
    fun t ht => hrg _ (hεV (hsc t ht))
  have han : AnalyticOnNhd ℂ gm (Metric.ball 0 1) := fun t ht =>
    AnalyticAt.pi (f := fun q s => g ((ε : ℂ) • s) (e q))
      (analyticOnNhd_rescale e g V hg ε hεV hε t ht)
  refine ⟨SncChart.mk gm a haN han ?_ ?_ ?_ ?_, {z | (∀ k, z ⟨k, c k⟩ ≠ 0) ∧
              ReciprocityTheory.AnForm.R.renPt (ReciprocityTheory.AnForm.R.affCoord c z) ∈ U ∧
              ‖ReciprocityTheory.AnForm.R.evalFam r (ReciprocityTheory.AnForm.R.renPt (ReciprocityTheory.AnForm.R.affCoord c z))‖ < ε / 2},
            ?_, ⟨hwc, hpU, ?_⟩, ?_⟩
  · exact fun t ht => (mem_mcPts_iff_conePts_pC P _).2 (hchart t ht).1
  · intro t ht v ⟨c', hc'⟩
    have hdiff : DifferentiableAt ℂ gm t := (han t ht).differentiableAt
    have hcomp : ∀ k, c' k = 0 := by
      intro k
      have h1 := congrFun hc' ⟨k, c k⟩
      have h2 : (fun s => gm s ⟨k, c k⟩) =ᶠ[nhds t] fun _ => (1 : ℂ) := by
        filter_upwards [Metric.isOpen_ball.mem_nhds ht] with s hs using (hchart s hs).2 k
      have h3 : HasFDerivAt (fun s => gm s ⟨k, c k⟩)
          ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : (Σ k, J k) => ℂ) ⟨k, c k⟩).comp
            (fderiv ℂ gm t)) t :=
        (hasFDerivAt_pi'.1 hdiff.hasFDerivAt) ⟨k, c k⟩
      have h4 := h3.unique ((hasFDerivAt_const (1 : ℂ) t).congr_of_eventuallyEq h2)
      have h5 := congrArg (fun L => L v) h4
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
        ContinuousLinearMap.zero_apply] at h5
      rw [h1] at h5
      simpa [torusSmul, (hchart t ht).2 k] using h5
    have hzero : fderiv ℂ gm t v = 0 := by
      rw [hc']; funext q; simp [torusSmul, hcomp q.1]
    refine eq_zero_of_fderiv_eq_zero e r gm (ε : ℂ) hεc t hdiff ?_ v hzero
    filter_upwards [Metric.isOpen_ball.mem_nhds ht] with s hs
    have : (fun j => gm s (e.symm j)) = g ((ε : ℂ) • s) := by
      funext j; simp [gm]
    rw [this]
    exact hcoord s hs
  · intro t ht t' ht' c' hc' he
    have hone : ∀ k, c' k = 1 := by
      intro k
      have h1 := congrFun he ⟨k, c k⟩
      simpa [torusSmul, (hchart t ht).2 k, (hchart t' ht').2 k] using h1.symm
    have hgg : g ((ε : ℂ) • t) = g ((ε : ℂ) • t') := by
      funext j
      have h1 := congrFun he (e.symm j)
      simpa [gm, torusSmul, hone] using h1
    have h2 := (hcoord t ht).symm.trans ((congrArg _ hgg).trans (hcoord t' ht'))
    exact smul_right_injective _ hεc h2
  · intro t ht
    have h1 := hbd (g ((ε : ℂ) • t)) (hzs t ht) (hball _ (hsc t ht)).2
    refine h1.trans ?_
    have h2 : ∀ i, eval (g ((ε : ℂ) • t)) (r i) = (ε : ℂ) * t i := fun i =>
      congrFun (hcoord t ht) i
    simp only [h2, mul_eq_zero, hεc, false_or]
  · have hA : IsOpen {z : (Σ k, J k) → ℂ | ∀ k, z ⟨k, c k⟩ ≠ 0} := by
      have : {z : (Σ k, J k) → ℂ | ∀ k, z ⟨k, c k⟩ ≠ 0} = ⋂ k, {z | z ⟨k, c k⟩ ≠ 0} := by
        ext z; simp
      rw [this]
      exact isOpen_iInter_of_finite fun k => isOpen_ne_fun (continuous_apply _) continuous_const
    have hf : ContinuousOn (fun z : (Σ k, J k) → ℂ =>
        ReciprocityTheory.AnForm.R.renPt (ReciprocityTheory.AnForm.R.affCoord c z))
        {z : (Σ k, J k) → ℂ | ∀ k, z ⟨k, c k⟩ ≠ 0} := by
      refine continuousOn_pi.2 fun j => ?_
      simp only [ReciprocityTheory.AnForm.R.renPt, ReciprocityTheory.AnForm.R.affCoord, Function.comp_apply]
      exact (continuous_apply _).continuousOn.div (continuous_apply _).continuousOn
        fun z hz => hz _
    have hev : Continuous (ReciprocityTheory.AnForm.R.evalFam r) :=
      continuous_pi fun l => MvPolynomial.continuous_eval (p := r l)
    have hT : IsOpen (U ∩ ReciprocityTheory.AnForm.R.evalFam r ⁻¹' {u | ‖u‖ < ε / 2}) :=
      hU.inter (isOpen_lt continuous_norm continuous_const |>.preimage hev)
    have := hf.isOpen_inter_preimage hA hT
    exact this
  · show ‖ReciprocityTheory.AnForm.R.evalFam r p‖ < ε / 2
    rw [hr0', norm_zero]; positivity
  · rintro z ⟨⟨hzc, hzU, hzn⟩, hzm⟩
    obtain ⟨hv1, hv2⟩ := hsolve _ ⟨hzU, hcone z hzm hzc⟩
    set v := ReciprocityTheory.AnForm.R.renPt (ReciprocityTheory.AnForm.R.affCoord c z) with hv
    set u := ReciprocityTheory.AnForm.R.evalFam r v with hu
    refine ⟨(ε : ℂ)⁻¹ • u, ?_, fun k => z ⟨k, c k⟩, hzc, ?_⟩
    · rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε]
      rw [inv_mul_le_iff₀ hε]
      linarith
    · funext q
      show z q = z ⟨q.1, c q.1⟩ * g ((ε : ℂ) • (ε : ℂ)⁻¹ • u) (e q)
      rw [smul_inv_smul₀ hεc, hv2]
      have hvq : v (e q) = ReciprocityTheory.AnForm.R.affCoord c z q := by
        show ReciprocityTheory.AnForm.R.affCoord c z (e.symm (e q)) = _
        rw [Equiv.symm_apply_apply]
      rw [hvq]
      simp only [ReciprocityTheory.AnForm.R.affCoord]
      rw [mul_div_cancel₀ _ (hzc q.1)]

end GlobalTheory.CompanionTheory.Ar.ChartParams
