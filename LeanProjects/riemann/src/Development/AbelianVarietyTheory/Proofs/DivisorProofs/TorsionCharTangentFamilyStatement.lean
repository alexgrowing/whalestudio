import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionCharTangentFamily
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitKOfIsAlgClosed
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.ArInt GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.Mean4O GlobalTheory.LineNorm GlobalTheory.CoverNorm GlobalTheory.VertForm GlobalTheory.HtGen
open Formalism.MainNotions.DIV.Cons (intO)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_char_tangent_family : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) [IsLocallyNoetherian X] (t : SAB H X), X.IsSeparated → ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (V : Cover Y) (ρ' : V.X ⟶ X) (ρ : Y.X ⟶ X), V.j ≫ ρ' = V.π ≫ ρ → ∀ (q : ℕ) [Fact q.Prime], CharFam t ρ' q 2 → ∀ (m : ℕ) (u₀ : Fin m → (Sp (DualNumber Y.Fn) ⟶ t.G.left)) (f : ∀ y : Y.X, Fin m → (Sp (DualNumber (Y.X.presheaf.stalk y)) ⟶ t.G.left)) (d : Y.X → Fin m → Y.Fnˣ), IsFlagFrame t ρ u₀ f d → ∀ (k : ℕ) (hk : k ≤ m), GenOver V (fun y => ((∏ l : Fin k, d y (Fin.castLE hk l) : Y.Fnˣ) : Y.Fn)) (fun v e y => -∑ l : Fin k, stepLog t ρ f q (Fin.castLE hk l) v e y) q := by
  first | exact @GlobalTheory.HtGen.genOver_flag | exact GlobalTheory.HtGen.genOver_flag | (intros; apply GlobalTheory.HtGen.genOver_flag <;> assumption)
