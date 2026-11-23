import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EndValuedForm11Coeffs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopFormIntegralOfSupportInHolomorphicChartStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransgressionCorrectionIsTopDegreeFormStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransgressionDensityHolomorphicChartEtaleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransgressionTopCoeffComplexEqZeroOfCutoffZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableOnChernTransgressionTermPoincareGrowthStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableOnHolomorphicChartTransEtaleChartStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramMatrixSmoothIsUnitInHolomorphicChartStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffAtHolomorphicComplexChartOfSmoothAtStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodPatchChartImagePropertiesStatement
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

set_option autoImplicit false
noncomputable section

theorem GlobalTheory.GoodTop.hasInt_corrDens_of_goodPatch : ∀ {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {m : ℕ} (E : Fr (ratOf X) (fun _ : Unit => m) 0) (O : X.X.Opens) (H H₀ : Mat (fun _ : Unit => m) X.Fn → CxPts X.str σ → Mat (fun _ : Unit => m) ℂ), IsMetricOn E O H → IsMetricOn E ⊤ H₀ → ∀ {e : OpenPartialHomeomorph (CxPts X.str σ) (V X.dim)} {S : Finset (Fin X.dim)} {A : Mat (fun _ : Unit => m) X.Fn} {W : Set (CxPts X.str σ)} {c : ℝ}, GoodPatch E O H e S A W c → ∀ {ρ : CxPts X.str σ → ℝ}, (∀ y, CInfAt ρ y) → tsupport ρ ⊆ W → HasInt (fun c : AlgChart X.str σ X.dim => c.e) (corrDens E H₀ H ρ) (ptsIn X.str σ O) ((Real.pi ^ X.dim)⁻¹ * (∫ v in offHyp S (e '' W), corrC (fun v => ρ (e.symm v)) (fun v => H₀ A (e.symm v) ()) (fun v => H A (e.symm v) ()) v).re) := by
  intro F _ σ X m E O H H₀ hH hH₀ e S A W c hP ρ hρ hsupp
  classical
  have := X.smooth_str
  obtain ⟨hUo, hUeq, hK⟩ := GlobalTheory.T.goodPatch_chart_image_properties E O H hP
  set g : V X.dim → ℝ := corrTop (fun v => ρ (e.symm v)) (fun v => H₀ A (e.symm v) ()) (fun v => H A (e.symm v) ())
    with hg
  have hKc : IsCompact (e '' tsupport ρ) := hK _ (isClosed_tsupport ρ) hsupp
  have hint : IntegrableOn (corrC (fun v => ρ (e.symm v)) (fun v => H₀ A (e.symm v) ()) (fun v => H A (e.symm v) ()))
      (offHyp S (e '' W)) := by
    refine GlobalTheory.T.integrableOn_chernTransgressionTerm_poincareGrowth S (e '' W) (e '' tsupport ρ) _ _ _ c hUo hKc (Set.image_mono hsupp) ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · rintro _ ⟨z, hz, rfl⟩ a ha
      exact hP.small z hz a ha
    · rintro _ ⟨z, hz, rfl⟩
      have htop : z ∈ ptsIn X.str σ (⊤ : X.X.Opens) := by
        simp [ptsIn]
      exact GlobalTheory.T.gramMatrix_smooth_isUnit_in_holomorphicChart E ⊤ H₀ hH₀ hP.holo htop (hP.sub hz) (hP.frame z hz)
    · intro v hv
      rw [← hUeq] at hv
      obtain ⟨z, ⟨hzO, hz⟩, rfl⟩ := hv
      exact GlobalTheory.T.gramMatrix_smooth_isUnit_in_holomorphicChart E O H hH hP.holo hzO (hP.sub hz) (hP.frame z hz)
    · intro v hv a i j
      rw [← hUeq] at hv
      obtain ⟨z, ⟨hzO, hz⟩, rfl⟩ := hv
      exact hP.form z hz hzO a i j
    · intro v hv a b i j
      rw [← hUeq] at hv
      obtain ⟨z, ⟨hzO, hz⟩, rfl⟩ := hv
      exact hP.dbar z hz hzO a b i j
    · rintro _ ⟨z, hz, rfl⟩
      exact (GlobalTheory.T.contDiffAt_holomorphicComplexChart_of_smoothAt hP.holo (hP.sub hz) (hρ z)).contDiffWithinAt
    · rintro _ ⟨z, hz, rfl⟩ hK'
      rw [e.left_inv (hP.sub hz)]
      by_contra h0
      exact hK' ⟨z, subset_tsupport ρ h0, rfl⟩
  have hgi : IntegrableOn g (e '' (ptsIn X.str σ O ∩ W)) := by
    rw [hUeq]
    exact (hint.re).const_mul _
  have hval : (∫ v in e '' (ptsIn X.str σ O ∩ W), g v) = (Real.pi ^ X.dim)⁻¹ *
      (∫ v in offHyp S (e '' W), corrC (fun v => ρ (e.symm v)) (fun v => H₀ A (e.symm v) ()) (fun v => H A (e.symm v) ()) v).re := by
    rw [hUeq, hg]
    simp only [corrTop]
    rw [integral_const_mul]
    congr 1
    exact integral_re hint
  rw [← hval]
  refine GlobalTheory.T.topFormIntegral_of_support_in_holomorphicChart (fun c : AlgChart X.str σ X.dim => c.e) (fun i j => i.holo_trans j)
    (fun y => AlgChart.exists_mem_source y) (isOpen_ptsIn O).measurableSet e W g hP.isOpen hP.sub
    (fun j => GlobalTheory.T.differentiableOn_holomorphicChart_trans_etaleChart hP.holo j) (GlobalTheory.T.transgression_correction_isTopDegreeForm E O H H₀ hH hH₀ hρ) ?_ ?_ hgi
  · intro i y _ hyW hyi
    have hy : y ∉ tsupport ρ := fun h => hyW (hsupp h)
    have h0 : ρ =ᶠ[𝓝 y] fun _ => 0 := notMem_tsupport_iff_eventuallyEq.1 hy
    have h1 : (fun v => ρ (i.e.symm v)) =ᶠ[𝓝 (i.e y)] fun _ => 0 := by
      have ht := (i.e.continuousAt_symm (i.e.map_source hyi)).tendsto
      rw [i.e.left_inv hyi] at ht
      exact ht.eventually h0
    simp only [corrDens, corrTop]
    rw [GlobalTheory.T.transgressionTopCoeffComplex_eq_zero_of_cutoff_zero _ _ h1]
    simp
  · intro j y hyS hyW hyj
    exact GlobalTheory.T.transgressionDensity_holomorphicChart_etale E O H H₀ hH hH₀ hρ hP.holo j hyS (hP.sub hyW) hyj (hP.frame y hyW)
