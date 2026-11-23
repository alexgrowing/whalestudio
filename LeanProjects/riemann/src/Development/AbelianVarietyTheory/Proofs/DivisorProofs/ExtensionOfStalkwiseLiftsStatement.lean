import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtensionOfStalkwiseLifts
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagMat
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ArLieBase
open GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar
open GlobalTheory.FlagCls
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.extension_of_stalkwise_lifts : ∀ (G Y S : Scheme.{0}) [IsIntegral G] (s : G ⟶ S) (t : Y ⟶ S) [IsSeparated t] [LocallyOfFiniteType t] (p : Sp G.functionField ⟶ Y), p ≫ t = GlobalTheory.FlagCov.genPt G ≫ s → (∀ z : G, ∃ q : Sp (G.presheaf.stalk z) ⟶ Y, spMap (algebraMap (G.presheaf.stalk z) G.functionField) ≫ q = p ∧ q ≫ t = G.fromSpecStalk z ≫ s) → ∃ f : G ⟶ Y, GlobalTheory.FlagCov.genPt G ≫ f = p ∧ f ≫ t = s := by
  first | exact @GlobalTheory.FlagCls.exists_hom_of_forall_stalk | exact GlobalTheory.FlagCls.exists_hom_of_forall_stalk | (intros; apply GlobalTheory.FlagCls.exists_hom_of_forall_stalk <;> assumption)
