import Mathlib
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermCut
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermBGen
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ChartPrimTrPfA
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.IntChartPf
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExistsTruncatedIntegralChart
import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.IsAbelianSchemePullbackUniversalTriple
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.PrimitiveIsoGPassesToPullbackStatement
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.PrimitiveIsoGUniqueOnAbelianStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)

namespace GlobalTheory

theorem chartPrimTr_holds : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ChartPrimTrSt Xo c := by
  intro E _ _ _ H Dw l Xo c T io y I wPT hT
  obtain ⟨wP, hP⟩ := GermB.exists_wP Xo.univ.t
  obtain ⟨w₁, hw₁, h₁⟩ := GlobalTheory.T.primitiveIsoG_passes_to_pullback E H _ _ _ _ _ I.m1 I.w1 I.rig1 wP hP
  obtain ⟨w₂, hw₂, h₂⟩ := GlobalTheory.T.primitiveIsoG_passes_to_pullback E H _ _ _ _ _ I.m2 I.w2 I.rig2 wPT hT
  have hab := GlobalTheory.isAbelianScheme_of_pullback_univ E H Dw l Xo _ _ _ I.m1
  have e : w₁ = w₂ := GlobalTheory.T.primitiveIsoG_unique_on_abelian GlobalTheory.firstFiveLaws.1.globalFns E H _ I.t' hab w₁ w₂ hw₁ hw₂
  subst e
  exact ⟨wP, (isPrim_iff wP).2 hP, w₁, hw₁.1, h₂, h₁⟩

end GlobalTheory
