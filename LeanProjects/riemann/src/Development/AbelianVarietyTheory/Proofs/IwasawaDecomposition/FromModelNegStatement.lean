import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FromModelNeg
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFlagFrame
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.LineNorm MonObj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fromModel_neg' : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (Δ : Y.Dv) (t : Y.X → Y.Fnˣ) (φ : PtFn Y), (∀ y, Δ.IsEqn y (t y)) → FromModel Y Δ t φ → FromModel Y (-Δ) (fun y => (t y)⁻¹) (fun v e y => -φ v e y) := by
  first | exact @GlobalTheory.LineNorm.Neg.fromModel_neg | exact GlobalTheory.LineNorm.Neg.fromModel_neg | (intros; apply GlobalTheory.LineNorm.Neg.fromModel_neg <;> assumption)
