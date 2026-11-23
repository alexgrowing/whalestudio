import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FromModelZeroLogConstant
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFlagFrame
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.LineNorm MonObj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fromModel_zero_log_constant : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (a : F) (n : ℕ), a ≠ 0 → n ≠ 0 → FromModel Y 0 (fun _ => 1) (fun _ e _ => Real.log (e.w (algebraMap F (AlgebraicClosure F) a)) / n) := by
  first | exact @GlobalTheory.LineNorm.fromModel_const | exact GlobalTheory.LineNorm.fromModel_const | (intros; apply GlobalTheory.LineNorm.fromModel_const <;> assumption)
