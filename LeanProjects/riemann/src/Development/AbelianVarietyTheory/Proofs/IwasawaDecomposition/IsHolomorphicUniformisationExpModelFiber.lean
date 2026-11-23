import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PushExLeft
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsDerivAt0OfCart

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ShFam.Hor.LogCh

theorem pushEx_hol : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (σ₀ : KA l →+* ℂ) (Fu : FamilyUnif Xo σ₀ ty) (y : Sp ℂ ⟶ Xo.XF c) (i : Fin Fu.n) (P : (Fu.Di i).La →+ (Fin g → ℂ)) (p : Sp ℂ ⟶ Z.X) (hu : Fu.u i P = y ≫ pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)) (hp : y ≫ Z.jQ ≫ pullback.fst Z.s (spMap β) = p), IsPeriod (Fu.Di i) ty P → IsHolTo Set.univ (fun z => (pushEx Z Fu y i P p hu hp z).left) := by
  intro E _ _ _ H Dw l Xo c O _ β Z g ty σ₀ Fu y i P p hu hp hP
  have h1 := (Fu.hol i 0 Set.univ (fun _ => P) isOpen_univ
    ⟨fun _ _ => hP, fun _ => differentiableOn_const _⟩).2
  have hw : ∀ (b : Fin 0 → ℂ) (z : Fin g → ℂ), (Fu.ex i P z).left ≫ Xo.univ.t.G.hom =
      (fun _ => y) b ≫ pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) := fun _ z => by
    rw [Over.w (Fu.ex i P z), ← hu]; rfl
  have h2 := GlobalTheory.TrueCx.TorFrHolo.isHolTo_lift Z.m0.toSABMap.cart.1 isOpen_univ
    (fun (_ : Fin 0 → ℂ) z => (Fu.ex i P z).left) (fun _ => y) h1
    (GlobalTheory.TrueCx.TorHolo.isHolTo_const isOpen_univ y) hw
  have h3 := ReciprocityTheory.ChartRestriction.G.PullbackSections.isHolTo_comp h2 Z.m.φ
  exact GlobalTheory.LocLift.isHolTo_comp h3 isOpen_univ (β := fun z => ((0 : Fin 0 → ℂ), z)) (by fun_prop)
    fun _ _ => ⟨trivial, trivial⟩

end GlobalTheory.ShFam.Hor.LogCh
