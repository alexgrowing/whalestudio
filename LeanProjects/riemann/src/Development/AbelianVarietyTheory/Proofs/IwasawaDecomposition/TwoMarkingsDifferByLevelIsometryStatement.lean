import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwoMarkingsDifferByLevelIsometry
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor
open scoped Matrix CategoryTheory.Obj Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.two_markings_differ_by_level_isometry : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Letter Dw) (Fu : Fam Xo c σ e) (a : CxFr Z σ), (∀ i j Q Q', Per Fu a i Q → Per Fu a j Q' → i = j) ∧ ∀ i Q Q', Per Fu a i Q → Per Fu a i Q' → ∃ gm : (Fu.Di i).La ≃ₗ[𝓞 E] (Fu.Di i).La, IsIsom (Fu.Di i) gm ∧ IsLev l (Fu.Di i) gm ∧ ∀ v, Q' (gm v) = Q v := by
  first | exact @GlobalTheory.ShFam.Hor.TwoMarkings.per_unique | exact GlobalTheory.ShFam.Hor.TwoMarkings.per_unique | (intros; apply GlobalTheory.ShFam.Hor.TwoMarkings.per_unique <;> assumption)
