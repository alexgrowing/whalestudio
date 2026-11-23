import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CoordAtConstMulIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor
open ReciprocityTheory.ChartRestriction.G.FD

namespace GlobalTheory.ShFam.Horiz

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

def frameCast {Z : Model Xo c β} {R : Type} [CommRing R] {φ : c.F →+* R} {x x' : Sp R ⟶ Z.X} (h : x = x')
    (g : EigFrame Z φ x) : EigFrame Z φ x' := h ▸ g

theorem ptF_jQ_over (Z : Model Xo c β) {σ : c.F →+* ℂ} (P : FrPt Xo c (CAt σ)) :
    (GlobalTheory.AllWt.ptF (S := CAt σ) P ≫ Z.jQ) ≫ genStr Z = spMap σ := by
  rw [Category.assoc, Z.jQ_over]
  exact pullback.lift_snd _ _ _

def cxOf (Z : Model Xo c β) {σ : c.F →+* ℂ} (P : FrPt Xo c (CAt σ)) : CxFr Z σ :=
  ⟨⟨GlobalTheory.AllWt.ptF (S := CAt σ) P ≫ Z.jQ, ptF_jQ_over Z P⟩,
    frameCast (φ := σ) (Category.assoc _ _ _).symm (frameOf (R := CAt σ) Z P)⟩

end GlobalTheory.ShFam.Horiz
