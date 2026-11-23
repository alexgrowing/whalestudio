import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EndValuedForm11Coeffs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopFormIntegralOfSupportInHolomorphicChartStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableOnCutoffTopChernFormSmoothGramStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffAtHolomorphicComplexChartOfSmoothAtStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableOnHolomorphicChartTransEtaleChartStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramMatrixSmoothIsUnitInHolomorphicChartStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopChernDensityHolomorphicChartEtaleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousMulTopChernFormIsTopDegreeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodPatchChartImagePropertiesStatement
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix
set_option autoImplicit false

namespace GlobalTheory.GoodTop

theorem hasInt_cut_topDens_patch : ∀ {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {m : ℕ} (E : Fr (ratOf X) (fun _ : Unit => m) 0) (O : X.X.Opens) (H H₀ : Mat (fun _ : Unit => m) X.Fn → CxPts X.str σ → Mat (fun _ : Unit => m) ℂ), IsMetricOn E O H → IsMetricOn E ⊤ H₀ → ∀ {e : OpenPartialHomeomorph (CxPts X.str σ) (V X.dim)} {S : Finset (Fin X.dim)} {A : Mat (fun _ : Unit => m) X.Fn} {W : Set (CxPts X.str σ)} {c : ℝ}, GoodPatch E O H e S A W c → ∀ {ρ : CxPts X.str σ → ℝ}, (∀ y, CInfAt ρ y) → tsupport ρ ⊆ W → HasInt (fun c : AlgChart X.str σ X.dim => c.e) (fun c y => ρ y * topDens E H₀ c y) (ptsIn X.str σ ⊤) ((Real.pi ^ X.dim)⁻¹ * (∫ v in e '' W, (ρ (e.symm v) : ℂ) * mixTop fun _ => curvAt (fun v => H₀ A (e.symm v) ()) v).re) := by
  intro F _ σ X m E O H H₀ hH hH₀ e S A W c hp ρ hρ hsupp
  haveI := CxPts.secondCountableTopology_of_isProjOver σ X.isProjOver
  have hcont : Continuous ρ := continuous_iff_continuousAt.2 fun y => (hρ y).continuousAt
  have htop : ptsIn X.str σ ⊤ = Set.univ := Set.eq_univ_of_forall fun _ => mem_ptsIn_top
  set f : V X.dim → ℂ := fun v => (ρ (e.symm v) : ℂ) * mixTop fun _ => curvAt (fun v => H₀ A (e.symm v) ()) v with hf
  set g : V X.dim → ℝ := fun v => (Real.pi ^ X.dim)⁻¹ * (f v).re with hg
  obtain ⟨hUo, -, hK⟩ := GlobalTheory.T.goodPatch_chart_image_properties E O H hp

  have hfi : IntegrableOn f (e '' W) := by
    refine GlobalTheory.T.integrableOn_cutoff_topChernForm_smoothGram (e '' W) (e '' tsupport ρ) (fun v => H₀ A (e.symm v) ()) (fun v => ρ (e.symm v)) hUo
      (hK _ (isClosed_tsupport ρ) hsupp) (Set.image_mono hsupp) ?_ ?_ ?_
    · rintro _ ⟨z, hz, rfl⟩
      exact GlobalTheory.T.gramMatrix_smooth_isUnit_in_holomorphicChart E ⊤ H₀ hH₀ hp.holo mem_ptsIn_top (hp.sub hz) (hp.frame z hz)
    · rintro _ ⟨z, hz, rfl⟩
      exact (GlobalTheory.T.contDiffAt_holomorphicComplexChart_of_smoothAt hp.holo (hp.sub hz) (hρ z)).contDiffWithinAt
    · rintro _ ⟨z, hz, rfl⟩ hK'
      rw [e.left_inv (hp.sub hz)]
      by_contra h0
      exact hK' ⟨z, subset_tsupport ρ h0, rfl⟩
  have hgi : IntegrableOn g (e '' W) := hfi.re.const_mul _
  have key := GlobalTheory.T.topFormIntegral_of_support_in_holomorphicChart (fun c : AlgChart X.str σ X.dim => c.e)
    (fun i j => GlobalTheory.T.differentiableOn_holomorphicChart_trans_etaleChart i.holo j) (fun y => AlgChart.exists_mem_source y)
    (S := ptsIn X.str σ ⊤) (isOpen_ptsIn _).measurableSet (d := fun c y => ρ y * topDens E H₀ c y) e W g
    hp.isOpen hp.sub (fun j => GlobalTheory.T.differentiableOn_holomorphicChart_trans_etaleChart hp.holo j) (GlobalTheory.T.continuous_mul_top_chern_form_isTopDegree E ⊤ H₀ hH₀ hcont) ?_ ?_
    (by rw [htop, Set.univ_inter]; exact hgi)
  · rw [htop, Set.univ_inter] at key
    convert key using 1
    rw [hg, integral_const_mul]
    congr 1
    exact (integral_re hfi).symm
  · intro i y _ hyW _
    have : ρ y = 0 := by
      by_contra h0
      exact hyW (hsupp (subset_tsupport ρ h0))
    simp [this]
  · intro j y _ hyW hyj
    have ht := GlobalTheory.T.top_chern_density_holomorphic_chart_etale E ⊤ H₀ hH₀ hp.holo j mem_ptsIn_top (hp.sub hyW) hyj (hp.frame y hyW)
    simp only [hg, hf, e.left_inv (hp.sub hyW), Complex.re_ofReal_mul]
    rw [← mul_assoc, mul_comm _ (ρ y), mul_assoc, ht]
    ring

end GlobalTheory.GoodTop
