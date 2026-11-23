import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianFrameFormNormSqEq
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LineSCShortExact
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_frame_form_norm_sq_eq : ∀ (n : ℕ) (K A : ReciprocityTheory.L2DbarEstimates.V n → Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℂ) (v : ReciprocityTheory.L2DbarEstimates.V n → ℝ) (z : ReciprocityTheory.L2DbarEstimates.V n),
    GlobalTheory.HermFrame.MContDiffAt 2 K z → (∀ᶠ x in nhds z, (K x).PosDef) → (∀ a b, AnalyticAt ℂ (fun x => A x a b) z) → IsUnit (A z).det → v z = 1 →
    (∀ᶠ x in nhds z, ‖GlobalTheory.HermFrame.form (K x) (Pi.single (Sum.inl 0) 1) (fun i => A x i (Sum.inl 0))‖ ^ 2 =
      v x * (GlobalTheory.HermFrame.chg (A x) (K x) (Sum.inl 0) (Sum.inl 0)).re * (K x (Sum.inl 0) (Sum.inl 0)).re) →
    ((ofValues (GlobalTheory.HermFrame.ddc (fun x => 1 - v x) z) : Ev n) : Alt n) *
      (((ofValues (GlobalTheory.HermFrame.extTrace (fun x => GlobalTheory.HermFrame.chg (A x) (K x)) z) : Ev n) : Alt n) -
        ((ofValues (GlobalTheory.HermFrame.extTrace K z) : Ev n) : Alt n)) = 0 := by
  first | exact @GlobalTheory.LineForm.ddc_sinSq_mul_extTrace_sub | exact GlobalTheory.LineForm.ddc_sinSq_mul_extTrace_sub | (intros; apply GlobalTheory.LineForm.ddc_sinSq_mul_extTrace_sub <;> assumption)
