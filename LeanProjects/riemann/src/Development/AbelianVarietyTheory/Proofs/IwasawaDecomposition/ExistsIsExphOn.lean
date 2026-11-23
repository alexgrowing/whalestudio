import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemSupportBDIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsExphOnEmpty
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocMapOfMem
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormIteratedFDerivScaleSnd
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JetContDiffOnAndHomogeneous
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartMatrixSmoothInvertible
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IteratedDerivChartTrans
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.QuadraticFormPositiveNearCompactStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothMapStaysInChartTargetStatement
open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.ChernReg
open scoped TensorProduct ContDiff

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ChernReg.ExphLoc

theorem exists_isExphOn : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (p : Y ⟶ Sp k) (σ : k →+* ℂ) (d : ℕ) [SmoothOfRelativeDimension d p] (R : AnRead p σ d) (a : ChartForm p σ d), IsKaehlerForm R a → ∀ (c : AlgChart p σ d), ∀ y ∈ c.e.source, ∃ (E : ChartMap p σ d) (W : Set (CxPts p σ)) (ε : ℝ), IsOpen W ∧ y ∈ W ∧ W ⊆ c.e.source ∧ 0 < ε ∧ ExphOn.IsExphOn a E W ε := by
  intro k _ Y p σ d _ R a ha c y hy
  obtain ⟨hsm, hdet, hform⟩ := GlobalTheory.ChernReg.MatSmooth.matIn_smooth_unit_form k Y p σ d R a ha c
  obtain ⟨r, hr, hrt⟩ := Metric.isOpen_iff.1 c.e.open_target (c.e y) (c.e.map_source hy)
  set C := Metric.closedBall (c.e y) (r / 2) with hCdef
  have hCU : C ⊆ c.e.target := (Metric.closedBall_subset_ball (by linarith)).trans hrt
  have hC : IsCompact C := isCompact_closedBall _ _
  have hjet := fun n => GlobalTheory.ChernReg.jet_contDiffOn_and_homogeneous d c.e.target (matIn a c) c.e.open_target hsm hdet n
  obtain ⟨f, hf, hfj⟩ := GlobalTheory.BorelParam.borel_param d c.e.target C c.e.open_target hC hCU (jet (matIn a c))
    (fun n => (hjet n).1) (fun n z hz t ξ => by
      have := (hjet n).2 z hz (t : ℂ) ξ
      rwa [Complex.coe_smul, ← Complex.ofReal_pow, Complex.coe_smul] at this)
  have hf0 : ∀ z ∈ C, f (z, 0) = z := fun z hz => by
    have := hfj z hz 0 0
    simpa [jet_zero] using this

  have hcont : ContinuousOn (fun x : ReciprocityTheory.L2DbarEstimates.V d × ReciprocityTheory.L2DbarEstimates.V d => a c (c.e.symm x.1) x.2.ofLp)
      (C ×ˢ Set.univ) := by
    have h1 : ContinuousOn (fun x : ReciprocityTheory.L2DbarEstimates.V d × ReciprocityTheory.L2DbarEstimates.V d =>
        ((x.2.ofLp ᵥ* matIn a c x.1) ⬝ᵥ star x.2.ofLp).re) (C ×ˢ Set.univ) := by
      have hm : ∀ i j, ContinuousOn (fun x : ReciprocityTheory.L2DbarEstimates.V d × ReciprocityTheory.L2DbarEstimates.V d => matIn a c x.1 i j)
          (C ×ˢ Set.univ) := fun i j =>
        ((hsm i j).continuousOn.mono hCU).comp continuousOn_fst fun x hx => hx.1
      refine Complex.continuous_re.comp_continuousOn ?_
      simp only [dotProduct, vecMul]
      refine continuousOn_finset_sum _ fun i _ => ContinuousOn.mul ?_ ?_
      · refine continuousOn_finset_sum _ fun j _ => ContinuousOn.mul ?_ (hm j i)
        exact ((PiLp.continuous_apply 2 _ j).comp continuous_snd).continuousOn
      · exact (continuous_star.comp ((PiLp.continuous_apply 2 _ i).comp continuous_snd)).continuousOn
    refine h1.congr fun x hx => ?_
    have := hform x.1 (hCU hx.1) x.2
    simp only
    rw [← this, Complex.ofReal_re]
  obtain ⟨ε, hε, hεU⟩ := GlobalTheory.T.quadratic_form_positive_near_compact d C c.e.target f (fun z η => a c (c.e.symm z) η.ofLp) hC c.e.open_target hCU
    hf.continuous hf0 hcont
    (fun z hz t η => (continuous_and_smul ha (c.e.map_target (hCU hz))).2 t η.ofLp)
    (fun z hz η hη => ha.2 c _ (c.e.map_target (hCU hz)) η.ofLp fun h => hη (by simpa using congrArg (WithLp.toLp 2) h))
  set W := c.e.symm '' Metric.ball (c.e y) (r / 2) with hWdef
  have hWC : ∀ y' ∈ W, c.e y' ∈ C := by
    rintro _ ⟨z, hz, rfl⟩
    rw [c.e.right_inv (hCU (Metric.ball_subset_closedBall hz))]
    exact Metric.ball_subset_closedBall hz
  have hWs : W ⊆ c.e.source := by
    rintro _ ⟨z, hz, rfl⟩
    exact c.e.map_target (hCU (Metric.ball_subset_closedBall hz))
  have hWo : IsOpen W := c.e.isOpen_image_symm_of_subset_target Metric.isOpen_ball
    fun z hz => hCU (Metric.ball_subset_closedBall hz)
  have hyW : y ∈ W := ⟨c.e y, Metric.mem_ball_self (by linarith), c.e.left_inv hy⟩
  have hεW : ∀ y' ∈ W, ∀ η : ReciprocityTheory.L2DbarEstimates.V d, a c y' η.ofLp < ε → f (c.e y', η) ∈ c.e.target := by
    intro y' hy' η hη
    refine hεU _ (hWC y' hy') η ?_
    simpa only [c.e.left_inv (hWs hy')] using hη

  refine ⟨locMap c f, W, ε, hWo, hyW, hWs, hε, ?_, ?_, ?_, ?_, ?_⟩
  · intro c₁ c₂ y' h₁ h₂ ξ
    by_cases hs : y' ∈ c.e.source
    · unfold locMap
      rw [ExphOn.dtrans_dtrans c₁ c₂ c h₁ h₂ hs]
    · simp only [locMap, hs, false_and, if_false]
  · intro c₀ v hv hvW ξ hξ
    obtain ⟨Φ, hΦ, hΦt, hΦe⟩ := GlobalTheory.T.smooth_map_stays_in_chart_target k Y p σ d R a ha c c₀ f W ε hf hWs hεW v hv hvW ξ hξ
    exact ((c.e.continuousAt_symm hΦt).comp hΦ.continuousAt).congr hΦe.symm
  · intro c₀ c' v hv hvW ξ hξ hE
    obtain ⟨Φ, hΦ, hΦt, hΦe⟩ := GlobalTheory.T.smooth_map_stays_in_chart_target k Y p σ d R a ha c c₀ f W ε hf hWs hεW v hv hvW ξ hξ
    have hE' : c.e.symm (Φ (v, ξ)) ∈ c'.e.source := by
      have := hΦe.eq_of_nhds
      simp only at this
      rwa [← this]
    have ho := ChartGlue.isOpen_over c.e c'.e.open_source
    have hτ : ContDiffAt ℝ ∞ (c'.e ∘ c.e.symm) (Φ (v, ξ)) :=
      (((contDiffOn_piLp 2).2 fun i => ReciprocityTheory.L2DbarEstimates.contDiffOn_of_differentiableOn d _ _ ho
        (differentiableOn_euclidean.1 (c.holo_trans c') i)).restrict_scalars ℝ).contDiffAt
        (ho.mem_nhds ⟨hΦt, hE'⟩)
    refine (hτ.comp _ hΦ).congr_of_eventuallyEq ?_
    exact hΦe.fun_comp c'.e
  · intro c₀ y' h₀ hW'
    have hs := hWs hW'
    have e0 : c₀.dtrans c y' 0 = 0 := by simpa using dtrans_smul c c₀ y' 0 0
    rw [locMap_of_mem c c₀ f ⟨hs, by rw [e0, WithLp.toLp_zero, hf0 _ (hWC y' hW')]; exact c.e.map_source hs⟩,
      e0, WithLp.toLp_zero, hf0 _ (hWC y' hW'), c.e.left_inv hs]
  · intro c₀ y' h₀ hW' ξ n
    have hs := hWs hW'
    have hz := hWC y' hW'
    set η : ReciprocityTheory.L2DbarEstimates.V d := WithLp.toLp 2 (c₀.dtrans c y' ξ.ofLp) with hη
    set g : ℝ → ReciprocityTheory.L2DbarEstimates.V d := fun t => f (c.e y', t • η) with hg
    have hgc : ContDiff ℝ ∞ g := hf.comp (contDiff_const.prodMk (contDiff_id.smul contDiff_const))
    have hg0 : g 0 = c.e y' := by simp only [hg, zero_smul]; exact hf0 _ hz
    have hgt : g 0 ∈ c.e.target := hg0 ▸ c.e.map_source hs
    have hev : ∀ᶠ t in 𝓝 (0:ℝ), g t ∈ c.e.target :=
      hgc.continuous.continuousAt.preimage_mem_nhds (c.e.open_target.mem_nhds hgt)
    have hu : (fun t : ℝ => locMap c f c₀ y' (t • ξ.ofLp)) =ᶠ[𝓝 0] fun t => c.e.symm (g t) := by
      filter_upwards [hev] with t ht
      have e1 : WithLp.toLp 2 (c₀.dtrans c y' (t • ξ.ofLp)) = t • η := by
        rw [dtrans_smul, WithLp.toLp_smul]
      rw [locMap_of_mem c c₀ f ⟨hs, by rw [e1]; exact ht⟩, e1]
    have hcu : (fun t : ℝ => c.e (locMap c f c₀ y' (t • ξ.ofLp))) =ᶠ[𝓝 0] g := by
      filter_upwards [hu, hev] with t h1 h2
      rw [h1, c.e.right_inv h2]
    have hu0 : locMap c f c₀ y' ((0:ℝ) • ξ.ofLp) = y' := by
      have := hu.eq_of_nhds
      simp only at this
      rw [this, hg0, c.e.left_inv hs]
    have key := GlobalTheory.ChernReg.ExphOn.iteratedDeriv_chart_trans k Y p σ d R a ha c c₀ (fun t => locMap c f c₀ y' (t • ξ.ofLp)) η
      (by simp only [hu0]; exact hs) (by simp only [hu0]; exact h₀)
      (((c.e.continuousAt_symm hgt).comp hgc.continuous.continuousAt).congr hu.symm)
      (hgc.contDiffAt.congr_of_eventuallyEq hcu)
      (fun m => by simp only [hu0]; rw [hcu.iteratedDeriv_eq]; exact hfj _ hz η m) n
    simp only [hu0] at key
    rw [key, hη, WithLp.ofLp_toLp, ExphOn.dtrans_dtrans c₀ c c₀ h₀ hs h₀, ExphOn.dtrans_self c₀ h₀, WithLp.toLp_ofLp]

end GlobalTheory.ChernReg.ExphLoc
