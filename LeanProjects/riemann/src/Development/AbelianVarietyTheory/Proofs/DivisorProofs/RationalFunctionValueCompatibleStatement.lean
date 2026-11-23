import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalFunctionValueCompatible
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieBaseIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieBaseAt
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ArLieBase
open GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rational_function_value_compatible : ∀ {k : Type} [CommRing k] {X G : Scheme.{0}} [IsIntegral X] [IsIntegral G] (qX : X ⟶ Sp k) (πG : G ⟶ X)
    (φ : X.functionField →+* G.functionField)
    (φs : G.fromSpecStalk (genericPoint G) ≫ πG = spMap φ ≫ X.fromSpecStalk (genericPoint X))
    (σ : k →+* ℂ) (z : CxPts (πG ≫ qX) σ) (y : CxPts qX σ), y.1 = z.1 ≫ πG → ∀ f : X.functionField,
    (RegAt (under y) f → RegAt (under z) (φ f) ∧ ratVal (φ f) z = ratVal f y) ∧
      (UnitAt (under y) f → UnitAt (under z) (φ f)) := by
  first | exact @GlobalTheory.RatValPull.regAt_ratVal_pull | exact GlobalTheory.RatValPull.regAt_ratVal_pull | (intros; apply GlobalTheory.RatValPull.regAt_ratVal_pull <;> assumption)
