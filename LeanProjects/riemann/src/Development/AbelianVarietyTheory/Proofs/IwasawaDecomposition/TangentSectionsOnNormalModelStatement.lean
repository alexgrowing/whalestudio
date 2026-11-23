import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TangentSectionsOnNormalModel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFlagFrame
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.LineNorm MonObj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tangent_sections_on_normal_model : HTBoundSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) [IsLocallyNoetherian X] (t : SAB H X), X.IsSeparated → ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (M : GlobalTheory.TrueGeo.Model Y) (ρ' : M.X ⟶ X) (ρ : Y.X ⟶ X), IsNormalScheme M.X → M.j ≫ ρ' = ρ → ∀ (m : ℕ) (u₀ : Fin m → (Sp (DualNumber Y.Fn) ⟶ t.G.left)) (f : ∀ y : Y.X, Fin m → (Sp (DualNumber (Y.X.presheaf.stalk y)) ⟶ t.G.left)) (d : Y.X → Fin m → Y.Fnˣ), IsFlagFrame t ρ u₀ f d → ∀ (q k : ℕ) (hk : k ≤ m) (z : M.X), LocMax M (fun y => ∏ l : Fin k, d y (Fin.castLE hk l)) (fun v e y => ∑ l : Fin k, stepLog t ρ f q (Fin.castLE hk l) v e y) z := by
  first | exact @GlobalTheory.LineNorm.Chart.locMax_flag | exact GlobalTheory.LineNorm.Chart.locMax_flag | (intros; apply GlobalTheory.LineNorm.Chart.locMax_flag <;> assumption)
