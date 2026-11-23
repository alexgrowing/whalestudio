import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecValAt

set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel

namespace GlobalTheory.FlatModel

theorem eigChar_model_eq_frPt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l l' : Level H) (Xo : Moduli Dw l) (Xo' : Moduli Dw l') (c : Coeff l) (c' : Coeff l') (W : ValuationSubring ℂ) (Y : Model Xo' c' (c'.V W).subtype) (r : Xo'.XF c' ⟶ Xo.XF c) (hle : c.F ≤ c'.F), OverIncl r hle → ∀ (σ : E →+* ℂ) (A : Type) [CommRing A] (ξ : Sp A ⟶ Y.X) (β : c'.V W →+* A), ξ ≫ Y.s = spMap β → ∀ (K : Type) [CommRing K] (φ : A →+* K) (io : c.F →+* K) (y : letI := io.toAlgebra; FrPt Xo c K) (yy : Sp K ⟶ Xo'.XF c'), yy ≫ Y.j = spMap φ ≫ ξ → (letI := io.toAlgebra; GlobalTheory.AllWt.ptF y = yy ≫ r) → ∀ a : 𝓞 E, φ (β (embV c' W σ a)) = io (embK c σ a) := by
  intro E _ _ _ H Dw l l' Xo Xo' c c' W Y r hle hOI σ A _ ξ β hξ K _ φ io y yy hyy hy a
  have e : ∀ {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (f : R →+* S) (g : S →+* T),
      spMap (g.comp f) = spMap g ≫ spMap f := by
    intro R S T _ _ _ f g
    show Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp]; rfl
  have inj : ∀ {R S : Type} [CommRing R] [CommRing S] (f g : R →+* S), spMap f = spMap g → f = g := by
    intro R S _ _ f g h
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective h)
  have h1 : Y.j ≫ Y.s = pullback.snd _ _ ≫ spMap (c'.V W).subtype := by
    show (Y.jQ ≫ pullback.fst _ _) ≫ Y.s = _
    rw [Category.assoc, pullback.condition, ← Category.assoc Y.jQ, Y.jQ_over]
  obtain ⟨ι', hι⟩ : ∃ ι' : c'.F →+* K, spMap ι' = yy ≫ pullback.snd _ _ :=
    ⟨(Spec.preimage (yy ≫ pullback.snd _ _)).hom, Spec.map_preimage _⟩
  have h2 : φ.comp β = ι'.comp (c'.V W).subtype := by
    apply inj
    rw [e, e, ← hξ, ← Category.assoc, ← hyy, Category.assoc, h1, ← Category.assoc, hι]
  have h3 : io = ι'.comp (IntermediateField.inclusion hle).toRingHom := by
    apply inj
    have h0 : (letI := io.toAlgebra; GlobalTheory.AllWt.ptF y) ≫ pullback.snd _ _ = spMap io := pullback.lift_snd _ _ _
    rw [e, hι, ← h0, hy, Category.assoc, hOI, Category.assoc]
  have h4 : (IntermediateField.inclusion hle) (embK c σ a) = embK c' σ a := Subtype.ext rfl
  calc φ (β (embV c' W σ a)) = ι' ((c'.V W).subtype (embV c' W σ a)) := RingHom.congr_fun h2 _
    _ = ι' (embK c' σ a) := rfl
    _ = io (embK c σ a) := by rw [h3, RingHom.comp_apply]; exact congrArg ι' h4.symm

end GlobalTheory.FlatModel
