import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsMetricFrOfIsMetricOn
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ChernDegreeComplex
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlaggedBundleMetricSmoothUnitEtaleChartStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramLowerTriangularFactorGradedLengthSmooth
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramLowerTriangularFactorPosDefPropertiesStatement
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.AntisymmFibrePointTwo
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

namespace GlobalTheory.ChernCalc

theorem leviForm_neg_log_unit_sub_log_grD : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (ι : Type) [Finite ι] (m k : ι → ℕ) (E : Fr (ratOf X) m k)
    (H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ), IsMetricFr E H → ∀ (y : CxPts X.str σ), ∀ A ∈ E.S (under y),
    ∀ u : X.Fn, UnitAt (under y) u → ∀ (τ : ι) (i : Fin (m τ)) (c : AlgChart X.str σ X.dim), y ∈ c.e.source →
      leviForm (fun v => -Real.log (‖ratVal u (c.e.symm v)‖ ^ 2) - Real.log (grD (H A (c.e.symm v) τ) i)) (c.e y) =
        leviForm (fun v => -Real.log (grD (H A (c.e.symm v) τ) i)) (c.e y) := by
  intro F _ σ X ι _ m k E H hH y A hA u hu τ i c hy
  obtain ⟨W, hW, a, rfl⟩ := hu.regAt.exists_fnOf
  have hyW : y ∈ ptsIn X.str σ W := mem_ptsIn.2 hW
  have ho := ChartGlue.isOpen_over c.e (isOpen_ptsIn (p := X.str) (σ := σ) W)
  have hm := ChartGlue.mem_over c.e hy hyW
  have hg := c.holo W a
  have hf : ContDiffAt ℂ 2 (ev X.str σ W a ∘ c.e.symm) (c.e y) :=
    (SCV.analyticAt_of_differentiableOn (hg.mono fun v hv => ⟨hv.1, hv.2⟩) (ho.mem_nhds hm)).contDiffAt
  have h0 : (ev X.str σ W a ∘ c.e.symm) (c.e y) ≠ 0 := by
    have := ratVal_ne_zero hu
    rw [ratVal_fnOf hyW] at this
    simpa [Function.comp, c.e.left_inv hy] using this
  have hlog : ContDiffAt ℝ 2 (fun v => Real.log (‖(ev X.str σ W a ∘ c.e.symm) v‖ ^ 2)) (c.e y) :=
    ((hf.restrict_scalars ℝ).norm_sq ℂ).log (by simpa using h0)
  have hsm := ((GlobalTheory.T.flaggedBundleMetric_smoothUnit_etaleChart F σ X ι m k E H hH y A hA τ).2 c hy).self_of_nhds
  have hG := (ldPart_grD_smooth _ _ _ _ hsm.1 hsm.2).2 i
  have hpos := ((GlobalTheory.T.gramLowerTriangularFactor_posDef_properties _ _ hsm.2).2.1 i).1
  have hD : ContDiffAt ℝ 2 (fun v => Real.log (grD (H A (c.e.symm v) τ) i)) (c.e y) :=
    (hG.log hpos.ne').of_le (WithTop.coe_le_coe.2 le_top)
  rw [leviForm_congr (u' := fun v => -Real.log (‖(ev X.str σ W a ∘ c.e.symm) v‖ ^ 2) +
      -Real.log (grD (H A (c.e.symm v) τ) i)), leviForm_add hlog.neg hD.neg,
    leviForm_neg (fun v => Real.log (‖(ev X.str σ W a ∘ c.e.symm) v‖ ^ 2)), leviForm_log_normSq_eq_zero hf h0,
    neg_zero, zero_add]
  filter_upwards [ho.mem_nhds hm] with v hv
  simp only [Function.comp, sub_eq_add_neg]
  rw [ratVal_fnOf hv.2]

end GlobalTheory.ChernCalc
