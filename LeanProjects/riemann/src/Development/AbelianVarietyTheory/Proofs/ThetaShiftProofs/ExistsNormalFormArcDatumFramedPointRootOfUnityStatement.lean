import Mathlib
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsNormalFormArcDatumFramedPointRootOfUnity
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_normalForm_arcDatum_framedPoint_rootOfUnity : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K₁ : Type) [Field K₁] [Algebra c.F K₁] [Algebra c.F (ArcS Dw K₁)] (d : ArcDatum Xo c K₁), ∃ (ζ : K₁) (N : ℕ), 0 < N ∧ ζ ^ N = 1 ∧ ((∀ τ k, GtTanR (d.e τ k)) → d.Normal ζ) ∧ ∃ (e₀ : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt (d.a.restrict (c.V d.Wp).subtype).D₀ (epsR K₁)) (y₀ : FrPt Xo c (ArcS Dw K₁)), (∀ τ k, GtComb (Pi.single k (1 : K₁)) (d.e τ) (e₀ τ k)) ∧ IsArcFr d.W e₀ d.th (arcι Dw K₁) y₀ ∧ FrChg (letM Dw K₁) (GlobalTheory.ArcQ.cst Dw ζ) y₀ d.yF := by
  first | exact @GlobalTheory.ArcQ.exists_normalForm | exact GlobalTheory.ArcQ.exists_normalForm | (intros; apply GlobalTheory.ArcQ.exists_normalForm <;> assumption)
