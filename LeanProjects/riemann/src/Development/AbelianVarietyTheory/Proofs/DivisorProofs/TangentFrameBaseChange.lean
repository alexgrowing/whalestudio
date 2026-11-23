import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecValAt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntegralPointPullbackComparison
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartFlagBaseHolds

set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel

namespace GlobalTheory.FlatModel.LiftBC

theorem isCombAtG_unique {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}}
    (t : SAB H X) {S : Type} [CommRing S] {x : Sp S ⟶ X} {m : ℕ} {v : Fin m → (Sp (DualNumber S) ⟶ t.G.left)}
    {a : Fin m → S} {w₁ w₂ : Sp (DualNumber S) ⟶ t.G.left} (h₁ : IsCombAtG t x v a w₁) (h₂ : IsCombAtG t x v a w₂) :
    w₁ = w₂ := by
  obtain ⟨u₁, hu₁, hw₁⟩ := h₁
  obtain ⟨u₂, hu₂, hw₂⟩ := h₂
  have hu : u₁ = u₂ := funext fun i => Over.OverMorphism.ext ((hu₁ i).trans (hu₂ i).symm)
  rw [← hw₁, ← hw₂, hu]

theorem eq_bc_of_isCombAtG : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l' : Level H}
    {Xo' : Moduli Dw l'} {c' : Coeff l'} {W : ValuationSubring ℂ} (Y : Model Xo' c' (c'.V W).subtype) {L k : Type}
    [CommRing L] [CommRing k] (φ : L →+* k) (yL : Sp L ⟶ Xo'.XF c') {g : ℕ}
    (e : Fin g → (Sp (DualNumber L) ⟶ Y.t.G.left)) (cf : Fin g → L) (w : Sp (DualNumber L) ⟶ Y.oF.t.G.left)
    (w' : Sp (DualNumber k) ⟶ Y.oF.t.G.left),
    IsCombAtG Y.t (yL ≫ Y.j) e cf (w ≫ Y.m.φ) →
    IsCombAtG Y.t (spMap φ ≫ yL ≫ Y.j) (bcV Y.t φ e) (fun b => φ (cf b)) (w' ≫ Y.m.φ) →
    w' = spMap (dualMap φ) ≫ w := by
  intro E _ _ _ H Dw l' Xo' c' W Y L k _ _ φ yL g e cf w w' h₁ h₂
  have h₁' := GlobalTheory.LocM.Cht.FlagBase.isCombAtG_bc Y.t φ h₁
  have hφ : w' ≫ Y.m.φ = (spMap (dualMap φ) ≫ w) ≫ Y.m.φ := by
    rw [Category.assoc]
    exact isCombAtG_unique Y.t h₂ h₁'
  haveI : IsOpenImmersion Y.j := GlobalTheory.TriplesAlong.isOpenImmersion_j W Y
  have hc := Y.m.cart.1
  have hb : w' ≫ Y.oF.t.G.hom = (spMap (dualMap φ) ≫ w) ≫ Y.oF.t.G.hom := by
    rw [← cancel_mono Y.j]
    simp only [Category.assoc]
    have hw := hc.w
    change Y.m.φ ≫ Y.t.G.hom = Y.oF.t.G.hom ≫ Y.j at hw
    rw [← hw, ← Category.assoc, hφ, Category.assoc, Category.assoc]
  exact hc.hom_ext hφ hb

end GlobalTheory.FlatModel.LiftBC
