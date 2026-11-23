import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoverRefinementExists
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitKOfIsAlgClosed
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.ArInt GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.Mean4O GlobalTheory.LineNorm GlobalTheory.CoverNorm GlobalTheory.VertForm GlobalTheory.HtGen
open Formalism.MainNotions.DIV.Cons (intO)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cover_refinement_exists : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) [IsLocallyNoetherian X] (t : SAB H X) (F : Type) [Field F] [NumberField F] (Y : Var F) (M : TrueGeo.Model Y) (ρ' : M.X ⟶ X) (V₀ : Cover Y) (q : ℕ), q ≠ 0 → ∃ (V : Cover Y) (a : V.X ⟶ V₀.X) (g : V.G ⟶ V₀.G) (ρ'' : V.X ⟶ X), a ≫ V₀.p = V.p ∧ V.j ≫ a = g ≫ V₀.j ∧ g ≫ V₀.π = V.π ∧ g (genericPoint V.G) = genericPoint V₀.G ∧ V.j ≫ ρ'' = V.π ≫ M.j ≫ ρ' ∧ CharZero V.X.functionField ∧ (∃ ζ : V.X.functionField, IsPrimitiveRoot ζ q) ∧ SplitK t (K := V.X.functionField) (V.X.fromSpecStalk (genericPoint V.X) ≫ ρ'') q := by
  first | exact @GlobalTheory.HtGen.SplitCover.exists_cover | exact GlobalTheory.HtGen.SplitCover.exists_cover | (intros; apply GlobalTheory.HtGen.SplitCover.exists_cover <;> assumption)
