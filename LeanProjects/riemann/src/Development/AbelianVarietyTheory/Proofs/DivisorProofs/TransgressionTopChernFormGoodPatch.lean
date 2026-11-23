import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EndValuedForm11Coeffs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothMetricCutTopChernDensityPatchStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodMetricCutTopChernDensityPatchStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransgressionTermDensityGoodPatchStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodMetricLocalTransgressionFormulaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodPatchChartImagePropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramMatrixSmoothIsUnitInHolomorphicChartStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffAtHolomorphicComplexChartOfSmoothAtStatement
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

theorem hasInt_patch_transgression : ∀ {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {m : ℕ} (E : Fr (ratOf X) (fun _ : Unit => m) 0) (O : X.X.Opens) (H H₀ : Mat (fun _ : Unit => m) X.Fn → CxPts X.str σ → Mat (fun _ : Unit => m) ℂ), IsMetricOn E O H → IsMetricOn E ⊤ H₀ → ∀ {e : OpenPartialHomeomorph (CxPts X.str σ) (V X.dim)} {S : Finset (Fin X.dim)} {A : Mat (fun _ : Unit => m) X.Fn} {W : Set (CxPts X.str σ)} {c : ℝ}, GoodPatch E O H e S A W c → ∀ {ρ : CxPts X.str σ → ℝ}, (∀ y, CInfAt ρ y) → tsupport ρ ⊆ W → ∃ a b : ℝ, HasInt (fun c : AlgChart X.str σ X.dim => c.e) (fun c y => ρ y * topDens E H c y) (ptsIn X.str σ O) a ∧ HasInt (fun c : AlgChart X.str σ X.dim => c.e) (fun c y => ρ y * topDens E H₀ c y) (ptsIn X.str σ ⊤) b ∧ HasInt (fun c : AlgChart X.str σ X.dim => c.e) (corrDens E H₀ H ρ) (ptsIn X.str σ O) (a - b) := by
  intro F _ σ X m E O H H₀ hH hH₀ e S A W c hP ρ hρ hsupp
  obtain ⟨hUo, hUoff, hcpt⟩ := GlobalTheory.T.goodPatch_chart_image_properties E O H hP
  have h1 := GlobalTheory.T.goodMetric_cut_topChern_density_patch E O H H₀ hH hH₀ hP hρ hsupp
  have h0 := GlobalTheory.T.smoothMetric_cut_topChern_density_patch E O H H₀ hH hH₀ hP hρ hsupp
  have hc := GlobalTheory.T.transgression_term_density_good_patch E O H H₀ hH hH₀ hP hρ hsupp
  refine ⟨_, _, h1, h0, ?_⟩
  have hloc := GlobalTheory.T.goodMetric_local_transgression_formula S (e '' W) (e '' tsupport ρ) (fun v => H₀ A (e.symm v) ()) (fun v => H A (e.symm v) ())
    (fun v => ρ (e.symm v)) c hUo (hcpt _ (isClosed_tsupport ρ) hsupp) (Set.image_mono hsupp)
    (by
      rintro v ⟨z, hz, rfl⟩ a ha
      exact hP.small z hz a ha)
    (by
      rintro v ⟨z, hz, rfl⟩
      exact GlobalTheory.T.gramMatrix_smooth_isUnit_in_holomorphicChart E ⊤ H₀ hH₀ hP.holo mem_ptsIn_top (hP.sub hz) (hP.frame z hz))
    (by
      intro v hv
      rw [← hUoff] at hv
      obtain ⟨z, ⟨hzO, hz⟩, rfl⟩ := hv
      exact GlobalTheory.T.gramMatrix_smooth_isUnit_in_holomorphicChart E O H hH hP.holo hzO (hP.sub hz) (hP.frame z hz))
    (by
      intro v hv a i j
      rw [← hUoff] at hv
      obtain ⟨z, ⟨hzO, hz⟩, rfl⟩ := hv
      exact hP.form z hz hzO a i j)
    (by
      intro v hv a b i j
      rw [← hUoff] at hv
      obtain ⟨z, ⟨hzO, hz⟩, rfl⟩ := hv
      exact hP.dbar z hz hzO a b i j)
    (by
      rintro v ⟨z, hz, rfl⟩
      exact (GlobalTheory.T.contDiffAt_holomorphicComplexChart_of_smoothAt hP.holo (hP.sub hz) (hρ z)).contDiffWithinAt)
    (by
      rintro v ⟨z, hz, rfl⟩ hv
      rw [e.left_inv (hP.sub hz)]
      by_contra h
      exact hv ⟨z, subset_tsupport _ h, rfl⟩)
  convert hc using 1
  rw [← mul_sub, ← Complex.sub_re, hloc]

end GlobalTheory.GoodTop
