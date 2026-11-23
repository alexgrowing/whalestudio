import Mathlib
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsChartGeneratorPullbackGeneratesFibre
import Development.AbelianVarietyTheory.Definitions.RegularCharts.MatrixTwoByTwoCongr
import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_chart_generator_pullback_generates_fibre : ReciprocityTheory.ChartRestriction.G.Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (M : MChart Y), ∀ (R : Type) [CommRing R] [Algebra c.F R] (f : Γ(Y.X, M.U) →+* R) (x : Sp R ⟶ Xo.X) (Λ : M.Lift f x), ∃ s : LB.Sec (PPx x), Λ.ThTie s ∧ ∀ s' : LB.Sec (PPx x), ∃! a : R, ∀ i, s'.f i = scal x a i * s.f i := by
  first | exact @GlobalTheory.Reg.ChartGenerator.exists_thTie_generator | exact GlobalTheory.Reg.ChartGenerator.exists_thTie_generator | (intros; apply GlobalTheory.Reg.ChartGenerator.exists_thTie_generator <;> assumption)
