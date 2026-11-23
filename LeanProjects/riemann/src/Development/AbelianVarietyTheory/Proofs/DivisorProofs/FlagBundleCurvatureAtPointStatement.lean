import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleCurvatureAtPoint
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LineSCShortExact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousOnCosSq
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_bundle_curvature_at_point : ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) [IsIntegral B] [IsIntegral Y] (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (d : ℕ)
    (hB : IsRegVar q d) (hY : IsRegVar p (d + 1)) (π : Y ⟶ B) (w : π ≫ q = p) (E : B.Modules) (h : VMetric q E 2) (H : h.IsCInf)
    (flB : Vert.Flag E 2) (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) 2),
    IsFlagBundle π (fun _ : Unit => E) (fun _ => 2) (fun _ => fl) → ∀ (σ : k →+* ℂ) (v : CxPts p σ → ℝ),
    GlobalTheory.CurveDens.IsCosSq ((h.pull π w).met σ) (fl.ι 1) ((Scheme.Modules.pullback π).map (flB.ι 1)) v →
    ∀ y : CxPts p σ, ∃ (c : AlgChart p σ (d + 1)) (G : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ) (s : Bool)
      (O : Set (ReciprocityTheory.L2DbarEstimates.V (d + 1))), y ∈ c.e.source ∧ IsOpen O ∧ c.e y ∈ O ∧ O ⊆ c.e.target ∧
      ContinuousOn (fun z => G (GlobalTheory.LineCos.base z)) O ∧
      ∀ z ∈ O, (G (GlobalTheory.LineCos.base z)).PosDef ∧
        v (c.e.symm z) = GlobalTheory.LineCos.cosSq s (G (GlobalTheory.LineCos.base z)) (GlobalTheory.LineCos.fib z) := by
  first | exact @GlobalTheory.LineChart.exists_chart_cosSq | exact GlobalTheory.LineChart.exists_chart_cosSq | (intros; apply GlobalTheory.LineChart.exists_chart_cosSq <;> assumption)
