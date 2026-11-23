import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralityCriterionNormalModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSplitting
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.ArLieBase
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integrality_criterion_normal_model : ∀ (F : Type) [Field F] [NumberField F] (X W : Scheme.{0}) (q : X ⟶ Sp (𝓞 F)) (s : W ⟶ Sp F) (jB : W ⟶ X) (d : ℕ), IsArithVar q d → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X → IsPullback jB s q (spMap (algebraMap (𝓞 F) F)) → IntCrit s jB := by
  first | exact @GlobalTheory.ArLieBase.IntCritPf.intCrit | exact GlobalTheory.ArLieBase.IntCritPf.intCrit | (intros; apply GlobalTheory.ArLieBase.IntCritPf.intCrit <;> assumption)
