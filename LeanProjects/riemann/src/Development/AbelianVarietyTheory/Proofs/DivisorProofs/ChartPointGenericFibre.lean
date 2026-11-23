import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitNatCastRes

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel
open GlobalTheory.UnitGlue

namespace GlobalTheory.UnitGlue.EvalPt

open GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits

theorem norm_algebraMap_unit (p : ℕ) [Fact p.Prime] (u : (𝓞_ℂ_[p])ˣ) :
    ‖algebraMap 𝓞_ℂ_[p] ℂ_[p] (u : 𝓞_ℂ_[p])‖ = 1 := by
  have hm : ∀ a : 𝓞_ℂ_[p], ‖(a : ℂ_[p])‖ ≤ 1 := fun a => by
    have this : (Valued.v (a : ℂ_[p]) : NNReal) ≤ 1 := a.2
    rw [PadicComplex.norm_eq_norm]
    exact (Valued.toNormedField.norm_le_one_iff).2 this
  have h1 : ((u : 𝓞_ℂ_[p]) : ℂ_[p]) * ((u⁻¹ : (𝓞_ℂ_[p])ˣ) : 𝓞_ℂ_[p]) = 1 := by
    exact_mod_cast u.mul_inv
  have h2 := congrArg norm h1
  rw [norm_mul, norm_one] at h2
  have h3 := hm (u : 𝓞_ℂ_[p])
  have h4 := hm ((u⁻¹ : (𝓞_ℂ_[p])ˣ) : 𝓞_ℂ_[p])
  show ‖((u : 𝓞_ℂ_[p]) : ℂ_[p])‖ = 1
  nlinarith [norm_nonneg ((u : 𝓞_ℂ_[p]) : ℂ_[p]), norm_nonneg (((u⁻¹ : (𝓞_ℂ_[p])ˣ) : 𝓞_ℂ_[p]) : ℂ_[p])]

theorem isUnit_natCast_fraction {F : Type} [Field F] [NumberField F] (V : ValuationSubring F) (p : ℕ)
    [Fact p.Prime] : IsUnit (p : FractionRing V) := by
  refine IsUnit.mk0 _ ?_
  intro h0
  have hV : (p : V) = 0 :=
    IsFractionRing.injective V (FractionRing V) (by rw [map_natCast, h0, map_zero])
  have hF : (p : F) = 0 := by
    have := map_natCast V.subtype p
    rw [hV, map_zero] at this
    exact this.symm
  exact (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero) hF

theorem isUnit_natCast_generic {F : Type} [Field F] [NumberField F] {V : ValuationSubring F}
    [IsDiscreteValuationRing V] (p : ℕ) [Fact p.Prime] {X : Scheme.{0}} (s : X ⟶ Sp V)
    (U : (genericFibre s).Opens) : IsUnit (p : Γ(genericFibre s, U)) := by
  have h1 : IsUnit (p : Γ(Spec (.of (FractionRing V)), ⊤)) := by
    have := (isUnit_natCast_fraction V p).map (Scheme.ΓSpecIso (.of (FractionRing V))).inv.hom
    rwa [map_natCast] at this
  have h2 := h1.map (genericStr s).appTop.hom
  rw [map_natCast] at h2
  have h3 := h2.map ((genericFibre s).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom
  rwa [map_natCast] at h3

theorem preimage_Xp_generic {F : Type} [Field F] [NumberField F] {V : ValuationSubring F}
    [IsDiscreteValuationRing V] (p : ℕ) [Fact p.Prime] {X : Scheme.{0}} (s : X ⟶ Sp V) :
    genericι s ⁻¹ᵁ Xp X p = ⊤ := by
  rw [Xp, Scheme.preimage_basicOpen, map_natCast]
  exact Scheme.basicOpen_of_isUnit _ (isUnit_natCast_generic p s _)

theorem appLE_congr {T Z : Scheme.{0}} {f g : T ⟶ Z} (e : f = g) (U : Z.Opens) (V : T.Opens)
    (hV : V ≤ f ⁻¹ᵁ U) : f.appLE U V hV = g.appLE U V (e ▸ hV) := by
  subst e; rfl

theorem appLE_top_top {T Z : Scheme.{0}} (f : T ⟶ Z) (hV : ⊤ ≤ f ⁻¹ᵁ ⊤) : f.appLE ⊤ ⊤ hV = f.appTop :=
  Scheme.Hom.appLE_eq_app (f := f) (U := ⊤)

end GlobalTheory.UnitGlue.EvalPt

namespace GlobalTheory.UnitGlue.EvalPt
open GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits

theorem evalPt_norm : ∀ (F : Type) [Field F] [NumberField F] (V : ValuationSubring F) [IsDiscreteValuationRing V] (p : ℕ) [Fact p.Prime] (X : Scheme.{0}) (s : X ⟶ Sp V) (Xw : X.Opens) (K : (Sp 𝓞_ℂ_[p] ⟶ X) → Set ℂ_[p]) (h : ∀ x : X, UnitChartAt p Xw K x) (x : X) (φ : cR h x →+* 𝓞_ℂ_[p]) (yb : Sp 𝓞_ℂ_[p] ⟶ X), spMap φ ≫ cξ h x = yb → ∀ y : Spec (.of ℂ_[p]) ⟶ GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.genericFibre s, y ≫ GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.genericι s = Spec.map (CommRingCat.ofHom (algebraMap 𝓞_ℂ_[p] ℂ_[p])) ≫ yb → ∀ (e : ((glueLB h).pull yb).Gen) (cc : ℂ_[p]ˣ), GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.IsCoord s (glueLB h) (sigGen h s) yb y e cc → ∃ ψ : Localization.Away (p : cR h x) →+* ℂ_[p], ψ.comp (algebraMap (cR h x) _) = (algebraMap 𝓞_ℂ_[p] ℂ_[p]).comp φ ∧ ‖ψ (cu h x : Localization.Away (p : cR h x))‖ = ‖(cc : ℂ_[p])‖ := by
  intro F _ _ V _ p _ X s Xw K h x φ yb hyb y hy e cc hc
  subst hyb
  let j : PUnit → (glueLB h).ι := fun _ => x
  have hW : ∀ {T : Scheme.{0}} (f : T ⟶ X),
      LB.wchart (glueLB h) (fun _ : PUnit => f) j = f ⁻¹ᵁ Uc h x :=
    fun f => TopologicalSpace.Opens.ext (by ext z; simp [LB.wchart, glueLB, j])
  have hYb : (spMap φ ≫ cξ h x) ⁻¹ᵁ Uc h x = ⊤ := by
    change spMap φ ⁻¹ᵁ (cξ h x ⁻¹ᵁ (cξ h x ''ᵁ ⊤)) = ⊤
    rw [Scheme.Hom.preimage_image_eq]
    rfl
  have hYg : y ⁻¹ᵁ (genericι s ⁻¹ᵁ Uc h x) = ⊤ := by
    change (y ≫ genericι s) ⁻¹ᵁ Uc h x = ⊤
    rw [hy]
    change Spec.map _ ⁻¹ᵁ ((spMap φ ≫ cξ h x) ⁻¹ᵁ Uc h x) = ⊤
    rw [hYb]
    rfl
  have h₁ : (⊤ : (Spec (.of ℂ_[p])).Opens) ≤ y ⁻¹ᵁ ((glueLB h).pull (genericι s)).U j := by
    change ⊤ ≤ y ⁻¹ᵁ LB.wchart (glueLB h) (fun _ : PUnit => genericι s) j
    rw [hW, hYg]
  have h₂ : (⊤ : (Spec (.of ℂ_[p])).Opens) ≤
      Spec.map (CommRingCat.ofHom (algebraMap 𝓞_ℂ_[p] ℂ_[p])) ⁻¹ᵁ ((glueLB h).pull (spMap φ ≫ cξ h x)).U j := by
    change ⊤ ≤ Spec.map _ ⁻¹ᵁ LB.wchart (glueLB h) (fun _ : PUnit => spMap φ ≫ cξ h x) j
    rw [hW, hYb]
    exact le_top
  have hcond : LB.wchart (glueLB h) (fun _ : PUnit => genericι s) j ≤ genericι s ⁻¹ᵁ (Uc h x ⊓ Xp X p) := by
    rw [hW]
    intro z hz
    show z ∈ genericι s ⁻¹ᵁ Uc h x ⊓ genericι s ⁻¹ᵁ Xp X p
    rw [preimage_Xp_generic p s]
    exact ⟨hz, trivial⟩
  have hsig : (sigGen h s).s j = res hcond (pullU (genericι s) _ (Cx h x)) := dif_pos hcond
  have key := hc j ⊤ h₁ h₂
  rw [hsig] at key
  let χ : Γ(X, Uc h x ⊓ Xp X p) ⟶ Γ(Spec (.of ℂ_[p]), ⊤) :=
    (genericι s).appLE (Uc h x ⊓ Xp X p) _ hcond ≫ y.appLE _ ⊤ h₁
  let ψ : Localization.Away (p : cR h x) →+* ℂ_[p] :=
    (Scheme.ΓSpecIso (.of ℂ_[p])).hom.hom.comp (χ.hom.comp (ev h x))
  have hψc : ψ (cu h x : Localization.Away (p : cR h x)) = (Scheme.ΓSpecIso (.of ℂ_[p])).hom.hom
      ((res h₁ (pullU y _ (res hcond (pullU (genericι s) _ (Cx h x))))) : Γ(Spec (.of ℂ_[p]), ⊤)) := rfl
  have hF1 : (Scheme.ΓSpecIso (.of ℂ_[p])).hom.hom
      ((res (U := ⊤) (V := ⊤) le_top (constUnit (𝟙 (Spec (.of ℂ_[p]))) cc) : Γ(Spec (.of ℂ_[p]), ⊤))) = cc := by
    have hid : (homOfLE (le_top : (⊤ : (Spec (.of ℂ_[p])).Opens) ≤ ⊤)).op = 𝟙 _ := Subsingleton.elim _ _
    simp [res, constUnit, hid]
  have htop : (⊤ : (Sp 𝓞_ℂ_[p]).Opens) ≤ ((glueLB h).pull (spMap φ ≫ cξ h x)).U j := by
    change ⊤ ≤ LB.wchart (glueLB h) (fun _ : PUnit => spMap φ ≫ cξ h x) j
    rw [hW, hYb]
  have hM : (Spec.map (CommRingCat.ofHom (algebraMap 𝓞_ℂ_[p] ℂ_[p]))).app
        (((glueLB h).pull (spMap φ ≫ cξ h x)).U j) ≫
      (Spec (.of ℂ_[p])).presheaf.map (homOfLE h₂).op ≫ (Scheme.ΓSpecIso (.of ℂ_[p])).hom =
      (Sp 𝓞_ℂ_[p]).presheaf.map (homOfLE htop).op ≫ (Scheme.ΓSpecIso (.of 𝓞_ℂ_[p])).hom ≫
        CommRingCat.ofHom (algebraMap 𝓞_ℂ_[p] ℂ_[p]) := by
    have e1 : (Spec.map (CommRingCat.ofHom (algebraMap 𝓞_ℂ_[p] ℂ_[p]))).app
        (((glueLB h).pull (spMap φ ≫ cξ h x)).U j) ≫ (Spec (.of ℂ_[p])).presheaf.map (homOfLE h₂).op =
        (Spec.map (CommRingCat.ofHom (algebraMap 𝓞_ℂ_[p] ℂ_[p]))).appLE _ ⊤ h₂ := rfl
    rw [← Category.assoc, e1, ← Scheme.Hom.map_appLE _ (U := ⊤) (by simp) (homOfLE htop).op,
      Category.assoc]
    erw [appLE_top_top]
    rw [Scheme.ΓSpecIso_naturality]
  have hF2 : (Scheme.ΓSpecIso (.of ℂ_[p])).hom.hom
      ((res h₂ (pullU (Spec.map (CommRingCat.ofHom (algebraMap 𝓞_ℂ_[p] ℂ_[p]))) _ (e.s j))) :
        Γ(Spec (.of ℂ_[p]), ⊤)) =
      algebraMap 𝓞_ℂ_[p] ℂ_[p] ((Units.map (Scheme.ΓSpecIso (.of 𝓞_ℂ_[p])).hom.hom.toMonoidHom
        (res htop (e.s j)) : (𝓞_ℂ_[p])ˣ) : 𝓞_ℂ_[p]) := by
    have := congrArg (fun m => m.hom ((e.s j : Γ(Sp 𝓞_ℂ_[p], ((glueLB h).pull (spMap φ ≫ cξ h x)).U j)))) hM
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at this
    exact this
  have hinvapp : ((cξ h x).appIso ⊤).inv ≫ (cξ h x).app (Uc h x) =
      (Sp (cR h x)).presheaf.map (eqToHom (Scheme.Hom.preimage_image_eq (cξ h x) ⊤)).op := by
    show ((cξ h x).appIso ⊤).inv ≫ (cξ h x).app (cξ h x ''ᵁ ⊤) = _
    rw [Iso.inv_comp_eq, Scheme.Hom.appIso_hom, Category.assoc, ← Functor.map_comp]
    simp [Uc]
  have hinvapp' : ∀ {Z : CommRingCat.{0}} (k : Γ(Sp (cR h x), cξ h x ⁻¹ᵁ Uc h x) ⟶ Z),
      ((cξ h x).appIso ⊤).inv ≫ (cξ h x).app (Uc h x) ≫ k =
        (Sp (cR h x)).presheaf.map (eqToHom (Scheme.Hom.preimage_image_eq (cξ h x) ⊤)).op ≫ k := by
    intro Z k
    rw [← hinvapp]
    exact (Category.assoc _ _ _).symm
  have hmor : (Scheme.ΓSpecIso (.of (cR h x))).inv ≫ ((cξ h x).appIso ⊤).inv ≫
      X.presheaf.map (homOfLE (inf_le_left : Uc h x ⊓ Xp X p ≤ Uc h x)).op ≫ χ ≫
        (Scheme.ΓSpecIso (.of ℂ_[p])).hom =
      CommRingCat.ofHom φ ≫ CommRingCat.ofHom (algebraMap 𝓞_ℂ_[p] ℂ_[p]) := by
    rw [show χ = _ from Scheme.Hom.appLE_comp_appLE y (genericι s) _ _ _ hcond h₁]
    erw [reassoc_of% (Scheme.Hom.map_appLE (y ≫ genericι s) _ (homOfLE (inf_le_left : Uc h x ⊓ Xp X p ≤ Uc h x)).op)]
    rw [appLE_congr (hy.trans (Category.assoc _ _ _).symm), Scheme.Hom.comp_appLE, Category.assoc]
    erw [hinvapp']
    erw [reassoc_of% (Scheme.Hom.map_appLE (Spec.map (CommRingCat.ofHom (algebraMap 𝓞_ℂ_[p] ℂ_[p])) ≫ spMap φ) _ (eqToHom (Scheme.Hom.preimage_image_eq (cξ h x) ⊤)).op)]
    erw [appLE_top_top]
    rw [Scheme.Hom.comp_appTop, Category.assoc, Scheme.ΓSpecIso_naturality, reassoc_of% (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ)), Iso.inv_hom_id_assoc]
  refine ⟨ψ, ?_, ?_⟩
  · ext r
    have := congrArg (fun m => m.hom r) hmor
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at this
    show (Scheme.ΓSpecIso _).hom.hom (χ.hom (ev h x (algebraMap _ _ r))) = algebraMap 𝓞_ℂ_[p] ℂ_[p] (φ r)
    rw [← this, ev, IsLocalization.Away.lift, IsLocalization.lift_eq]
    rfl
  · have key' := congrArg (fun u : Γ(Spec (.of ℂ_[p]), ⊤)ˣ =>
      (Scheme.ΓSpecIso (.of ℂ_[p])).hom.hom (u : Γ(Spec (.of ℂ_[p]), ⊤))) key
    dsimp only at key'
    rw [Units.val_mul, map_mul] at key'
    rw [hψc, key', hF1, hF2, norm_mul, norm_algebraMap_unit, _root_.mul_one]
end GlobalTheory.UnitGlue.EvalPt
