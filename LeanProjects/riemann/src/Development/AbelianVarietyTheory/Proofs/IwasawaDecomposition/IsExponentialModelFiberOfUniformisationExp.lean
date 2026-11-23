import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PushExLeft
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsDerivAt0OfCart
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFrPtOfEigFrame
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExponentialDerivativeAtZeroIsTangent
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ThetaHol

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ShFam.Hor.LogCh

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ShFam.Hor.LogCh

open ReciprocityTheory.ChartRestriction.G.PullbackSections.ExpRows (isDerivAt0_comp_hom isDerivAt0_unique)
open GlobalTheory.TrueCx.TorFrHolo (isDerivAt0_of_cart isHolTo_lift)

section Push

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} (Z : Model Xo c β) {g : ℕ}
  {ty : Fin g → (E →+* ℂ)} {σ₀ : KA l →+* ℂ} (Fu : FamilyUnif Xo σ₀ ty) (y : Sp ℂ ⟶ Xo.XF c) (i : Fin Fu.n)
  (P : (Fu.Di i).La →+ (Fin g → ℂ))

theorem isHolTo_ex_fixed (hP : IsPeriod (Fu.Di i) ty P) : IsHolTo Set.univ fun z => (Fu.ex i P z).left := by
  have h1 := (Fu.hol i 0 Set.univ (fun _ => P) isOpen_univ
    ⟨fun _ _ => hP, fun _ => differentiableOn_const _⟩).2
  exact GlobalTheory.LocLift.isHolTo_comp h1 isOpen_univ (β := fun z => ((0 : Fin 0 → ℂ), z)) (by fun_prop)
    fun _ _ => ⟨trivial, trivial⟩

theorem isHolTo_liftEx (hP : IsPeriod (Fu.Di i) ty P)
    (hu : Fu.u i P = y ≫ pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)) :
    IsHolTo Set.univ fun z => liftEx Z Fu y i P hu z ≫ Z.m.φ := by
  have h1 := (Fu.hol i 0 Set.univ (fun _ => P) isOpen_univ
    ⟨fun _ _ => hP, fun _ => differentiableOn_const _⟩).2
  have h2 := isHolTo_lift Z.m0.toSABMap.cart.1 isOpen_univ (fun _ z => (Fu.ex i P z).left) (fun _ => y) h1
    (ReciprocityTheory.ChartRestriction.G.PullbackSections.ThetaHol.isHolTo_const y) (fun _ z => by rw [Over.w (Fu.ex i P z), ← hu]; rfl)
  have h3 := ReciprocityTheory.ChartRestriction.G.PullbackSections.isHolTo_comp h2 Z.m.φ
  exact GlobalTheory.LocLift.isHolTo_comp h3 isOpen_univ (β := fun z => ((0 : Fin 0 → ℂ), z)) (by fun_prop)
    fun _ _ => ⟨trivial, trivial⟩

theorem isDerivAt0_liftEx (hP : IsPeriod (Fu.Di i) ty P)
    (hu : Fu.u i P = y ≫ pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom))
    {w : Fin g → ℂ} {v : Sp (DualNumber ℂ) ⟶ Z.oF.t.G.left}
    (hv : v ≫ Z.oF.t.G.hom = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ y)
    (hd : IsDerivAt0 (fun z => (Fu.ex i P z).left) w (v ≫ Z.m0.toSABMap.φ)) :
    IsDerivAt0 (liftEx Z Fu y i P hu) w v :=
  isDerivAt0_of_cart Z.m0.toSABMap.cart.1 y (fun z => liftEx_snd Z Fu y i P hu z)
    (by simpa only [liftEx_fst] using isHolTo_ex_fixed Fu i P hP) hv
    (by simpa only [liftEx_fst] using hd)

theorem isDerivAt0_ex_of_push (hP : IsPeriod (Fu.Di i) ty P)
    (hu : Fu.u i P = y ≫ pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom))
    {w : Fin g → ℂ} {v : Sp (DualNumber ℂ) ⟶ Z.oF.t.G.left}
    (hv : v ≫ Z.oF.t.G.hom = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ y)
    (hd : IsDerivAt0 (fun z => liftEx Z Fu y i P hu z ≫ Z.m.φ) w (v ≫ Z.m.φ)) :
    IsDerivAt0 (fun z => (Fu.ex i P z).left) w (v ≫ Z.m0.toSABMap.φ) := by
  have h := isDerivAt0_comp_hom (isDerivAt0_of_cart Z.m.cart.1 y (fun z => liftEx_snd Z Fu y i P hu z)
    (isHolTo_liftEx Z Fu y i P hP hu) hv hd) Z.m0.toSABMap.φ
  simpa only [liftEx_fst] using h

end Push

theorem isExpAt_pushEx : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (σ₀ : KA l →+* ℂ) (Fu : FamilyUnif Xo σ₀ ty) (y : Sp ℂ ⟶ Xo.XF c) (i : Fin Fu.n) (P : (Fu.Di i).La →+ (Fin g → ℂ)) (p : Sp ℂ ⟶ Z.X) (hu : Fu.u i P = y ≫ pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)) (hp : y ≫ Z.jQ ≫ pullback.fst Z.s (spMap β) = p), IsPeriod (Fu.Di i) ty P → IsExpAt Z.t p (pushEx Z Fu y i P p hu hp) := by
  intro E _ _ _ H Dw l Xo c O _ β Z g ty σ₀ Fu y i P p hu hp hP
  subst hp
  obtain ⟨t1, t2, t3⟩ := GlobalTheory.isDerivAt0_ex_isTanAt E H Dw l Xo σ₀ g ty Fu i P hP
  refine ⟨fun a b => ?_, fun w => ?_, fun v hv => ?_⟩
  · let L : (Fin g → ℂ) → (Over.mk y ⟶ Z.oF.t.G) := fun z =>
      Over.homMk (liftEx Z Fu y i P hu z) (liftEx_snd Z Fu y i P hu z)
    have hL : (L (a + b)).left = (L a * L b).left := by
      refine Z.m0.toSABMap.cart.1.hom_ext ?_ ?_
      · have e1 := Z.m0.toSABMap.cart.2 (Over.mk y) (L a) (L b) (pushPt Z.m0.toSABMap.cart.1.w (L a))
          (pushPt Z.m0.toSABMap.cart.1.w (L b)) rfl rfl
        refine Eq.trans ?_ e1
        refine (liftEx_fst Z Fu y i P hu (a + b)).trans ?_
        rw [Fu.ex_add i P hP]
        exact mul_left_congr hu _ _ _ _ (liftEx_fst Z Fu y i P hu a).symm (liftEx_fst Z Fu y i P hu b).symm
      · rw [Over.w, Over.w]
    refine Over.OverMorphism.ext ?_
    have e2 := Z.m.cart.2 (Over.mk y) (L a) (L b) (pushEx Z Fu y i P _ hu rfl a) (pushEx Z Fu y i P _ hu rfl b) rfl rfl
    refine Eq.trans ?_ e2.symm
    exact congrArg (· ≫ Z.m.φ) hL
  · obtain ⟨v, hv, -⟩ := t2 w
    have ht := t1 w v hv
    obtain ⟨v', k1, rfl⟩ := GlobalTheory.ShFam.OpenReg.exists_lift Z.m0.toSABMap (spMap (algebraMap ℂ (DualNumber ℂ)) ≫ y) v
      (by rw [ht.1, hu, Category.assoc])
    refine ⟨v' ≫ Z.m.φ, ⟨(GlobalTheory.ShFam.OpenReg.tan_iff Z.m rfl k1).2
      ((GlobalTheory.ShFam.OpenReg.tan_iff Z.m0.toSABMap hu.symm k1).1 ht),
      isDerivAt0_comp_hom (isDerivAt0_liftEx Z Fu y i P hP hu k1 hv) Z.m.φ⟩, fun v₂ hv₂ => ?_⟩
    exact isDerivAt0_unique hv₂.2 (isDerivAt0_comp_hom (isDerivAt0_liftEx Z Fu y i P hP hu k1 hv) Z.m.φ)
  · obtain ⟨v', k1, rfl⟩ := GlobalTheory.ShFam.OpenReg.exists_lift Z.m (spMap (algebraMap ℂ (DualNumber ℂ)) ≫ y) v
      (by rw [hv.1, Category.assoc])
    have h1 := (GlobalTheory.ShFam.OpenReg.tan_iff Z.m rfl k1).1 hv
    have h2 := (GlobalTheory.ShFam.OpenReg.tan_iff Z.m0.toSABMap hu.symm k1).2 h1
    obtain ⟨w, hw, hw'⟩ := t3 _ h2
    exact ⟨w, isDerivAt0_comp_hom (isDerivAt0_liftEx Z Fu y i P hP hu k1 hw) Z.m.φ,
      fun w' h' => hw' w' (isDerivAt0_ex_of_push Z Fu y i P hP hu k1 h')⟩

end GlobalTheory.ShFam.Hor.LogCh
