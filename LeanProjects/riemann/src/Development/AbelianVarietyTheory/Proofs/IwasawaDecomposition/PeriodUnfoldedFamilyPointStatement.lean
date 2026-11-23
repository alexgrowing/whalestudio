import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodUnfoldedFamilyPoint
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PtFJQOver
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor
open ReciprocityTheory.ChartRestriction.G.FD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.period_unfolded_family_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (r g : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r) (e : Fin g ≃ Letter Dw) (Fu : Fam Xo c σ e) (k : U.Comp) (i : Fin Fu.n) (y : (U.X k).dom) (Pm : (Fu.Di i).La →+ (Fin g → ℂ)), IsPeriod (Fu.Di i) (fun j => Formalism.L2.PjFree.relab c σ (e j).1) Pm → (U.un k y).x = Fu.u i Pm → (∀ τ (a : Fin (Dw.mult τ)), IsDerivAt0 (fun z => (Fu.ex i Pm z).left) (Pi.single (e.symm ⟨τ, a⟩) 1) ((U.un k y).u τ a)) → ∀ Q : (Fu.Di i).La →+ (Letter Dw → ℂ), (∀ v z, Q v z = Pm v (e.symm z)) → Per Fu (GlobalTheory.ShFam.Horiz.cxOf Z (U.un k y)) i Q := by
  first | exact @GlobalTheory.ShFam.Horiz.per_cxOf | exact GlobalTheory.ShFam.Horiz.per_cxOf | (intros; apply GlobalTheory.ShFam.Horiz.per_cxOf <;> assumption)
