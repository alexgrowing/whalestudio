import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuativeCriterionExtension
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagMat
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ArLieBase
open GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar
open GlobalTheory.FlagCls
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valuative_criterion_extension : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsIntegrallyClosed R] (K : Type) [Field K] [Algebra R K] [IsFractionRing R K] (Y : Scheme.{0}) (p : Sp K ⟶ Y) (y : Y), (∀ (V : ValuationSubring K) (ρ : R →+* V), IsLocalHom ρ → V.subtype.comp ρ = algebraMap R K → ∃ q : Sp V ⟶ Y, spMap V.subtype ≫ q = p ∧ q (IsLocalRing.closedPoint V) = y) → ∃ q : Sp R ⟶ Y, spMap (algebraMap R K) ≫ q = p := by
  first | exact @GlobalTheory.FlagCls.ExtLoc.extends_of_forall_dominating | exact GlobalTheory.FlagCls.ExtLoc.extends_of_forall_dominating | (intros; apply GlobalTheory.FlagCls.ExtLoc.extends_of_forall_dominating <;> assumption)
