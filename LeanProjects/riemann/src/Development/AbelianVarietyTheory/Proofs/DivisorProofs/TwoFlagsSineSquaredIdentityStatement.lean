import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoFlagsSineSquaredIdentity
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LineSCShortExact
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_bundle_hermitian_line_degree : ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) [IsIntegral B] [IsIntegral Y] (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (d : ℕ)
    (hB : IsRegVar q d) (hY : IsRegVar p (d + 1)) (π : Y ⟶ B) (w : π ≫ q = p) (E : B.Modules) (h : VMetric q E 2) (H : h.IsCInf)
    (flB : Vert.Flag E 2) (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) 2),
    IsFlagBundle π (fun _ : Unit => E) (fun _ => 2) (fun _ => fl) → ∀ (A : HermLB q) (σ : k →+* ℂ),
    ∀ v : CxPts p σ → ℝ, GlobalTheory.CurveDens.IsCosSq ((h.pull π w).met σ) (fl.ι 1) ((Scheme.Modules.pullback π).map (flB.ι 1)) v →
    GlobalTheory.HermFrame.kappa • ((hY.atlas σ).del ((hY.atlas σ).fn (fun y => 1 - v y)) * (hY.atlas σ).dbar ((hY.atlas σ).fn (fun y => 1 - v y))) = ((hY.atlas σ).fn (fun y => 1 - v y)) * ((hY.atlas σ).ddc ((hY.atlas σ).fn (fun y => 1 - v y)) + ((hY.atlas σ).fn (fun y => 1 - v y)) * evalF (hY.atlas σ) (fun i => c1F hY σ (fam5 π w H flB fl A i)) (X 4 - X 0)) := by
  first | exact @GlobalTheory.LocalLelong.local_identity | exact GlobalTheory.LocalLelong.local_identity | (intros; apply GlobalTheory.LocalLelong.local_identity <;> assumption)
