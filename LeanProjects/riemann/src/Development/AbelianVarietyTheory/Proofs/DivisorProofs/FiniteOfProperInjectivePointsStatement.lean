import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteOfProperInjectivePoints
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagMat
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ArLieBase
open GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar
open GlobalTheory.FlagCls
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_of_proper_injective_points : ∀ (G Y Bg S : Scheme.{0}) (f : G ⟶ Y) (jG : G ⟶ Bg) (πB : Bg ⟶ S) (π : Y ⟶ S), jG ≫ πB = f ≫ π → IsFinite πB → IsProper f → (∀ (K : Type) [Field K] (z z' : Sp K ⟶ G), z ≫ f = z' ≫ f → z ≫ jG = z' ≫ jG → z = z') → IsFinite f := by
  first | exact @GlobalTheory.FlagCls.isFinite_of_isProper_of_fieldPoints | exact GlobalTheory.FlagCls.isFinite_of_isProper_of_fieldPoints | (intros; apply GlobalTheory.FlagCls.isFinite_of_isProper_of_fieldPoints <;> assumption)
