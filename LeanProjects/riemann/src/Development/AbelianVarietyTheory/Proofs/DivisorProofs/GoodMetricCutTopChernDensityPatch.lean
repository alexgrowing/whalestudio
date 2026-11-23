import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EndValuedForm11Coeffs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopFormIntegralOfSupportInHolomorphicChartStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableOnCutoffTopChernFormPoincareGrowthStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousMulTopChernFormIsTopDegreeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopChernDensityHolomorphicChartEtaleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodPatchChartImagePropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramMatrixSmoothIsUnitInHolomorphicChartStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffAtHolomorphicComplexChartOfSmoothAtStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableOnHolomorphicChartTransEtaleChartStatement
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix
set_option autoImplicit false
noncomputable section

theorem GlobalTheory.GoodTop.hasInt_mul_topDens_goodPatch : ∀ {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {m : ℕ} (E : Fr (ratOf X) (fun _ : Unit => m) 0) (O : X.X.Opens) (H H₀ : Mat (fun _ : Unit => m) X.Fn → CxPts X.str σ → Mat (fun _ : Unit => m) ℂ), IsMetricOn E O H → IsMetricOn E ⊤ H₀ → ∀ {e : OpenPartialHomeomorph (CxPts X.str σ) (V X.dim)} {S : Finset (Fin X.dim)} {A : Mat (fun _ : Unit => m) X.Fn} {W : Set (CxPts X.str σ)} {c : ℝ}, GoodPatch E O H e S A W c → ∀ {ρ : CxPts X.str σ → ℝ}, (∀ y, CInfAt ρ y) → tsupport ρ ⊆ W → HasInt (fun c : AlgChart X.str σ X.dim => c.e) (fun c y => ρ y * topDens E H c y) (ptsIn X.str σ O) ((Real.pi ^ X.dim)⁻¹ * (∫ v in offHyp S (e '' W), (ρ (e.symm v) : ℂ) * mixTop fun _ => curvAt (fun v => H A (e.symm v) ()) v).re) := by
  intro F _ σ X m E O H H₀ hH hH₀ e S A W c hP ρ hρ hρW
  obtain ⟨hU, himg, hcpt⟩ := GlobalTheory.T.goodPatch_chart_image_properties E O H hP
  have hS : MeasurableSet (ptsIn X.str σ O) := (isOpen_ptsIn O).measurableSet
  have hd : ∀ i j : AlgChart X.str σ X.dim,
      DifferentiableOn ℂ (j.e ∘ i.e.symm) (i.e.target ∩ i.e.symm ⁻¹' j.e.source) := fun i j => i.holo_trans j
  have hcov : ∀ y, ∃ i : AlgChart X.str σ X.dim, y ∈ i.e.source := fun y => AlgChart.exists_mem_source y
  have hρc : Continuous ρ := continuous_iff_continuousAt.2 fun y => (hρ y).continuousAt
  have hρ0 : ∀ y, y ∉ W → ρ y = 0 := fun y hy => image_eq_zero_of_notMem_tsupport (fun h => hy (hρW h))
  set f : V X.dim → ℂ := fun v => (ρ (e.symm v) : ℂ) * mixTop fun _ => curvAt (fun v => H A (e.symm v) ()) v with hf
  have hint : IntegrableOn f (offHyp S (e '' W)) := by
    refine GlobalTheory.T.integrableOn_cutoff_topChernForm_poincareGrowth S (e '' W) (e '' tsupport ρ) (fun v => H₀ A (e.symm v) ()) (fun v => H A (e.symm v) ())
      (fun v => ρ (e.symm v)) c hU (hcpt _ (isClosed_tsupport ρ) hρW) (Set.image_mono hρW) ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · rintro _ ⟨z, hz, rfl⟩ a ha
      exact hP.small z hz a ha
    · rintro _ ⟨z, hz, rfl⟩
      exact GlobalTheory.T.gramMatrix_smooth_isUnit_in_holomorphicChart E ⊤ H₀ hH₀ hP.holo mem_ptsIn_top (hP.sub hz) (hP.frame z hz)
    · intro v hv
      rw [← himg] at hv
      obtain ⟨z, ⟨hzO, hz⟩, rfl⟩ := hv
      exact GlobalTheory.T.gramMatrix_smooth_isUnit_in_holomorphicChart E O H hH hP.holo hzO (hP.sub hz) (hP.frame z hz)
    · intro v hv
      rw [← himg] at hv
      obtain ⟨z, ⟨hzO, hz⟩, rfl⟩ := hv
      exact hP.form z hz hzO
    · intro v hv
      rw [← himg] at hv
      obtain ⟨z, ⟨hzO, hz⟩, rfl⟩ := hv
      exact hP.dbar z hz hzO
    · rintro _ ⟨z, hz, rfl⟩
      exact (GlobalTheory.T.contDiffAt_holomorphicComplexChart_of_smoothAt hP.holo (hP.sub hz) (hρ z)).contDiffWithinAt
    · rintro _ ⟨z, hz, rfl⟩ hK
      have hzK : z ∉ tsupport ρ := fun h => hK ⟨z, h, rfl⟩
      show ρ (e.symm (e z)) = 0
      rw [e.left_inv (hP.sub hz)]
      exact image_eq_zero_of_notMem_tsupport hzK
  have hre : IntegrableOn (fun v => (Real.pi ^ X.dim)⁻¹ * (f v).re) (offHyp S (e '' W)) :=
    (Integrable.re hint).const_mul _
  have key := GlobalTheory.T.topFormIntegral_of_support_in_holomorphicChart (fun c : AlgChart X.str σ X.dim => c.e) hd hcov hS
    (d := fun c y => ρ y * topDens E H c y) e W (fun v => (Real.pi ^ X.dim)⁻¹ * (f v).re) hP.isOpen hP.sub
    (fun j => GlobalTheory.T.differentiableOn_holomorphicChart_trans_etaleChart hP.holo j) (GlobalTheory.T.continuous_mul_top_chern_form_isTopDegree E O H hH hρc) ?_ ?_ (by rw [himg]; exact hre)
  · rw [himg, integral_const_mul] at key
    have h2 : ∫ v in offHyp S (e '' W), (f v).re = (∫ v in offHyp S (e '' W), f v).re := integral_re hint
    rw [h2] at key
    exact key
  · intro i y _ hy _
    simp [hρ0 y hy]
  · intro j y hyO hy hj
    have h1 := GlobalTheory.T.top_chern_density_holomorphic_chart_etale E O H hH hP.holo j hyO (hP.sub hy) hj (hP.frame y hy)
    simp only [hf, e.left_inv (hP.sub hy), Complex.re_ofReal_mul]
    rw [mul_left_comm, h1]
    ring
