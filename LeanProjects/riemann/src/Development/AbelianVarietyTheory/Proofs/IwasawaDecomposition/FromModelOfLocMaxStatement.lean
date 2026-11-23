import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FromModelOfLocMax
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFlagFrame
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.LineNorm MonObj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fromModel_of_locMax' : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (M : GlobalTheory.TrueGeo.Model Y) (Δ : Y.Dv) (t : Y.X → Y.Fnˣ) (φ : PtFn Y), (∀ y, Δ.IsEqn y (t y)) → (∀ z, LocMax M t φ z) → FromModel Y Δ t φ := by
  first | exact @GlobalTheory.LineNorm.Glue.fromModel_of_locMax | exact GlobalTheory.LineNorm.Glue.fromModel_of_locMax | (intros; apply GlobalTheory.LineNorm.Glue.fromModel_of_locMax <;> assumption)
