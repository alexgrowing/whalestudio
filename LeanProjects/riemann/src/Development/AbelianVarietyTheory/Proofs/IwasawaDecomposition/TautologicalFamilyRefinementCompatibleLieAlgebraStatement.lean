import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TautologicalFamilyRefinementCompatibleLieAlgebra
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TriIff
import Formalism.LocalToGlobal.ProjectiveLattices.MulCMemSec
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.FlagBundle
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tautologicalFamily_refinement_compatible_lieAlgebraFrame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (B Y : GlobalTheory.ProjVar.Var F) (j : B.X ⟶ gen Z) (f₀ : EigFrame Z (constF e B) (genericPt B ≫ j ≫ genι Z)) (S : Fr (ratOf B) Dw.mult 0) (A₀ : Mat Dw.mult B.Fn) (k : (E →+* ℂ) → ℕ) (S' : Fr (ratOf Y) Dw.mult k) (φ : B.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ B.X), Tied e B j f₀ S A₀ → Refines S S' φ f → ∃ (g₀ : EigFrame Z (constF e Y) (genericPt Y ≫ (f ≫ j) ≫ genι Z)) (A₁ : Mat Dw.mult Y.Fn), Tied e Y (f ≫ j) g₀ S' A₁ ∧ f₀.Coord (φ : B.Fn →+* Y.Fn) g₀ (A₁ * (A₀.map φ)⁻¹) := by
  first | exact @GlobalTheory.ShFam.TieUp.main | exact GlobalTheory.ShFam.TieUp.main | (intros; apply GlobalTheory.ShFam.TieUp.main <;> assumption)
