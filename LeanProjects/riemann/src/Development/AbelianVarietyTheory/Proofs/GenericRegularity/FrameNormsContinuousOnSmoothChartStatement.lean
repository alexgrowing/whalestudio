import Mathlib
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.FrameNormsContinuousOnSmoothChart
import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
import Development.AbelianVarietyTheory.Definitions.RegularCharts.Reframe
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import Formalism.LocalToGlobal.ProjectiveLattices.NrmContPf
import Formalism.LocalToGlobal.ProjectiveLattices.AxHSup
import Formalism.LocalToGlobal.ProjectiveLattices.DivFinOfLawA3
import Formalism.LocalToGlobal.ProjectiveLattices.FnTrdegOf
import Formalism.LocalToGlobal.ProjectiveLattices.RegQFree
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MaxBoundPf
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FrameNorm GlobalTheory.Reg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frameNorms_continuousOn_smoothChart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ r), (∀ σ, Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf (U σ)) → ∀ (xR : ℝ) (fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ), 0 < xR → FnPin U xR fn → ∀ (σ : c.F →+* ℂ) (A : Type) [CommRing A] [Algebra c.F A] [Algebra.Smooth c.F A] (yA : FrPt Xo c A) (X : Type) [TopologicalSpace X] (W : Set X) (φ : X → (A →ₐ[c.F] CAt σ)) (y : X → FrPt Xo c (CAt σ)), (∀ a, ContinuousOn (fun x => Formalism.L2.PjFree.toC (φ x a)) W) → (∀ x ∈ W, FrMap (φ x) yA (y x)) → ∀ i, ContinuousOn (fun x => |fn σ (y x) i|) W := by
  first | exact @GlobalTheory.FrameNorm.fn_continuousOn_smooth | exact GlobalTheory.FrameNorm.fn_continuousOn_smooth | (intros; apply GlobalTheory.FrameNorm.fn_continuousOn_smooth <;> assumption)
