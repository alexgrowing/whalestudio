import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

namespace GlobalTheory.FlatModel

def SecValAt {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
    {l l' : Level H} {Xo : Moduli Dw l} {Xo' : Moduli Dw l'} {c : Coeff l} {c' : Coeff l'} {W : ValuationSubring ℂ}
    (Y : Model Xo' c' (c'.V W).subtype) (r : Xo'.XF c' ⟶ Xo.XF c) (ν : SABMap Y.oF.t Xo.univ.t (r ≫ pullback.fst _ _))
    (τ : E →+* ℂ) (f : Rul Xo c) {A : Type} [CommRing A] (ξ : Sp A ⟶ Y.X) {g : ℕ}
    (e : Fin g → (Sp (DualNumber A) ⟶ Y.t.G.left)) (U₁ : Fin (Dw.mult τ) → Fin g → A)
    (U₂ : Fin (Dw.mult (conjEmb τ)) → Fin g → A) (k : Type) [Field k] (φ : A →+* k) (v : k) : Prop :=
  ∀ (_ : Algebra c.F k) (yy : Sp k ⟶ Xo'.XF c'), yy ≫ Y.j = spMap φ ≫ ξ →
    GVal Y r ν τ f yy (bcV Y.t φ e) (fun i b => φ (U₁ i b)) (fun i b => φ (U₂ i b)) v

end GlobalTheory.FlatModel

end
