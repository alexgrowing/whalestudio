import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleLineBundleChernRelation
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LineSCShortExact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FsOne
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open GlobalTheory.Points
open scoped Classical ComplexOrder

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_bundle_line_bundle_chern_relation : ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) [IsIntegral B] [IsIntegral Y] (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (d : ℕ)
    (hB : IsRegVar q d) (hY : IsRegVar p (d + 1)) (π : Y ⟶ B) (w : π ≫ q = p) (E : B.Modules) (h : VMetric q E 2) (H : h.IsCInf)
    (flB : Vert.Flag E 2) (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) 2),
    IsFlagBundle π (fun _ : Unit => E) (fun _ => 2) (fun _ => fl) → ∀ (A : HermLB q) (σ : k →+* ℂ),
    ∀ v : CxPts p σ → ℝ, GlobalTheory.CurveDens.IsCosSq ((h.pull π w).met σ) (fl.ι 1) ((Scheme.Modules.pullback π).map (flB.ι 1)) v →
    ∀ φ : (hB.atlas σ).Fld, (hB.atlas σ).IsForm φ → ∀ ε : ℤˣ, ∀ b₀ : CxPts q σ,
      ∃ U : Set (CxPts q σ), IsOpen U ∧ b₀ ∈ U ∧ ∃ G : CxPts q σ → Matrix (Fin 2) (Fin 2) ℂ, (∀ b ∈ U, (G b).PosDef) ∧
        ∀ S : Set (CxPts q σ), MeasurableSet S → S ⊆ U → ∀ J : Set ℝ, MeasurableSet J →
          (hY.atlas σ).part (evalF (hY.atlas σ) (fun i => c1F hY σ (fam5 π w H flB fl A i)) (X 0 - X 3) * pullF hB hY σ π w φ) ε
              (PtsOver.map π w (spMap σ) ⁻¹' S ∩ v ⁻¹' J) =
            ∫⁻ b in S, (∫⁻ x : ℂ, J.indicator (fun _ => (1 : ENNReal)) (GlobalTheory.FibCos.cos (G b) x) *
              ENNReal.ofReal (GlobalTheory.FibCos.fs (G b) x)) ∂((hB.atlas σ).part φ (-ε)) := by
  first | exact @GlobalTheory.FibLoc.local_product | exact GlobalTheory.FibLoc.local_product | (intros; apply GlobalTheory.FibLoc.local_product <;> assumption)
