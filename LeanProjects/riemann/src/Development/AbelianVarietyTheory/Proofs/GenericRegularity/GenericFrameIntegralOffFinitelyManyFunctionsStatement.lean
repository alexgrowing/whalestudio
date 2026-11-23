import Mathlib
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.GenericFrameIntegralOffFinitelyManyFunctions
import Development.AbelianVarietyTheory.Definitions.RegularCharts.MatrixTwoByTwoCongr
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Formalism.LocalToGlobal.ProjectiveLattices.IsGenFrGenFr
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.genericFrame_integral_off_finitelyMany_functions : ReciprocityTheory.ChartRestriction.G.Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), FrBC Xo c → ∀ (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (h : GenFrEx Xo c) (Z : Comp Xo c), ∃ S : Finset (Om Z), (∀ s ∈ S, s ≠ 0) ∧ ∀ (T : CDVR) (io : c.F →+* T.Fr), letI := io.toAlgebra; ∀ ψ : Om Z →ₐ[c.F] T.Fr, (∀ s ∈ S, vV T.V (ψ s) = 0) → ∀ z : FrPt Xo c T.Fr, FrMap ψ (genFr h Z) z → Integral T io z := by
  first | exact @GlobalTheory.Reg.GenInt.genFr_integral | exact GlobalTheory.Reg.GenInt.genFr_integral | (intros; apply GlobalTheory.Reg.GenInt.genFr_integral <;> assumption)
