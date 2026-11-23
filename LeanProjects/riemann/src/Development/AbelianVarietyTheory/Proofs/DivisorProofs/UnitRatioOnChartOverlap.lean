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

namespace GlobalTheory.UnitGlueTransport

theorem radical_map {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (p : ℕ) {a : R}
    (ha : a ∈ (Ideal.span {(p : R)}).radical) : f a ∈ (Ideal.span {(p : S)}).radical := by
  obtain ⟨n, hn⟩ := ha
  refine ⟨n, ?_⟩
  rw [Ideal.mem_span_singleton] at hn ⊢
  obtain ⟨c, hc⟩ := hn
  exact ⟨f c, by rw [← map_pow, hc, map_mul, map_natCast]⟩

theorem specMap_appLE {R A : Type} [CommRing R] [CommRing A] (a : R →+* A) (O : (Sp A).Opens)
    (e : O ≤ spMap a ⁻¹ᵁ ⊤) :
    (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (spMap a).appLE ⊤ O e =
    CommRingCat.ofHom a ≫ (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
      (Sp A).presheaf.map (homOfLE le_top : O ⟶ ⊤).op := by
  have h1 : (spMap a).appLE ⊤ O e =
      (spMap a).appLE ⊤ ⊤ le_top ≫ (Sp A).presheaf.map (homOfLE le_top : O ⟶ ⊤).op :=
    (Scheme.Hom.appLE_map _ _ _).symm
  have e1 : (spMap a).appTop = (spMap a).appLE ⊤ ⊤ le_top := Scheme.Hom.app_eq_appLE _
  rw [h1, ← e1, Scheme.ΓSpecIso_inv_naturality_assoc]

theorem appLE_chart {X : Scheme.{0}} {R A : Type} [CommRing R] [CommRing A] (c : Sp R ⟶ X)
    [IsOpenImmersion c] (a : R →+* A) (w : Sp A ⟶ X) (hw : spMap a ≫ c = w) (U : X.Opens)
    (hU : U ≤ c ''ᵁ ⊤) (O : (Sp A).Opens) (hO : O ≤ w ⁻¹ᵁ U) :
    (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (c.appIso ⊤).inv ≫ X.presheaf.map (homOfLE hU).op ≫
      w.appLE U O hO =
    CommRingCat.ofHom a ≫ (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
      (Sp A).presheaf.map (homOfLE le_top : O ⟶ ⊤).op := by
  subst hw
  rw [Scheme.Hom.map_appLE, ← Scheme.Hom.appLE_comp_appLE (spMap a) c (c ''ᵁ ⊤) ⊤ O
    (by rw [Scheme.Hom.preimage_image_eq]) le_top, Scheme.Hom.appIso_inv_appLE_assoc]
  erw [Scheme.Hom.map_appLE]
  exact specMap_appLE a O _

end GlobalTheory.UnitGlueTransport

namespace GlobalTheory.UnitGlueTransport

theorem map_map {X : Scheme.{0}} {U V W : X.Opens} (h1 : V ≤ U) (h2 : W ≤ V) (h3 : W ≤ U) (z : Γ(X, U)) :
    (X.presheaf.map (homOfLE h2).op).hom ((X.presheaf.map (homOfLE h1).op).hom z) =
      (X.presheaf.map (homOfLE h3).op).hom z := by
  rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, ← Functor.map_comp]; rfl

variable {p : ℕ} [Fact p.Prime] {X : Scheme.{0}} {Xw : X.Opens} {K : (Sp 𝓞_ℂ_[p] ⟶ X) → Set ℂ_[p]}
  (h : ∀ x : X, UnitChartAt p Xw K x)

theorem ev_transport (x : X) {A : Type} [CommRing A] (w : Sp A ⟶ X) (a : cR h x →+* A)
    (hw : spMap a ≫ cξ h x = w) (W : X.Opens) (hW : W ≤ Uc h x ⊓ Xp X p)
    (θ : Localization.Away (p : A) →+* Γ(Sp A, w ⁻¹ᵁ W))
    (hθ : θ.comp (algebraMap A _) = ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
      (Sp A).presheaf.map (homOfLE le_top : w ⁻¹ᵁ W ⟶ ⊤).op).hom)
    (χ : Localization.Away (p : cR h x) →+* Localization.Away (p : A))
    (hχ : χ.comp (algebraMap (cR h x) _) = (algebraMap A _).comp a)
    (c : Localization.Away (p : cR h x)) :
    (w.app W).hom ((X.presheaf.map (homOfLE hW).op).hom (ev h x c)) = θ (χ c) := by
  have m : (Scheme.ΓSpecIso (CommRingCat.of (cR h x))).inv ≫ ((cξ h x).appIso ⊤).inv ≫
      X.presheaf.map (homOfLE (inf_le_left : Uc h x ⊓ Xp X p ≤ cξ h x ''ᵁ ⊤)).op ≫
      X.presheaf.map (homOfLE hW).op ≫ w.appLE W (w ⁻¹ᵁ W) le_rfl =
      CommRingCat.ofHom a ≫ (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
        (Sp A).presheaf.map (homOfLE le_top : w ⁻¹ᵁ W ⟶ ⊤).op := by
    have hc := appLE_chart (cξ h x) a w hw W (hW.trans inf_le_left) (w ⁻¹ᵁ W) le_rfl
    erw [Scheme.Hom.map_appLE, Scheme.Hom.map_appLE]
    erw [Scheme.Hom.map_appLE] at hc
    exact hc
  have key : ((w.app W).hom.comp (X.presheaf.map (homOfLE hW).op).hom).comp (ev h x) = θ.comp χ := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (p : cR h x))
    ext r
    have e1 := congrArg (fun f => f.hom r) m
    have e2 := congrArg (fun f => f (a r)) hθ
    have e3 := congrArg (fun f => f r) hχ
    simp only [RingHom.comp_apply] at e2 e3 ⊢
    rw [e3, e2]
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e1
    rw [ev, IsLocalization.Away.lift, IsLocalization.lift_eq, Scheme.Hom.app_eq_appLE]
    exact e1
  exact congrArg (fun f => f c) key

end GlobalTheory.UnitGlueTransport

namespace GlobalTheory.UnitGlueTransport

theorem ratioProp_of_chart : ∀ (p : ℕ) [Fact p.Prime] (X : Scheme.{0}) (Xw : X.Opens) (K : (Sp 𝓞_ℂ_[p] ⟶ X) → Set ℂ_[p]) (h : ∀ x : X, UnitChartAt p Xw K x) (x y : X) (A : Type) [CommRing A] (w : Sp A ⟶ X) (a1 : cR h x →+* A) (a2 : cR h y →+* A), IsOpenImmersion w → spMap a1 ≫ cξ h x = w → spMap a2 ≫ cξ h y = w → Set.range w = Set.range (cξ h x) ∩ Set.range (cξ h y) → ∀ u : Aˣ, (u : A) - 1 ∈ (Ideal.span {(p : A)}).radical → (∀ (χ1 : Localization.Away (p : cR h x) →+* Localization.Away (p : A)) (χ2 : Localization.Away (p : cR h y) →+* Localization.Away (p : A)), χ1.comp (algebraMap (cR h x) _) = (algebraMap A _).comp a1 → χ2.comp (algebraMap (cR h y) _) = (algebraMap A _).comp a2 → algebraMap A (Localization.Away (p : A)) (u : A) * χ2 (cu h y : Localization.Away (p : cR h y)) = χ1 (cu h x : Localization.Away (p : cR h x))) → ∃ u' : Γ(X, Uc h x ⊓ Uc h y)ˣ, RatioProp h x y u' := by
  intro p _ X Xw K h x y A _ w a1 a2 hw hw1 hw2 hrange u hu hχ
  have hVeq : Uc h x ⊓ Uc h y = w.opensRange := by
    apply TopologicalSpace.Opens.ext
    simp only [TopologicalSpace.Opens.coe_inf, Uc, Scheme.Hom.image_top_eq_opensRange,
      Scheme.Hom.coe_opensRange]
    exact hrange.symm
  set V := Uc h x ⊓ Uc h y with hVdef
  set W := V ⊓ Xp X p with hWdef
  have hWV : W ≤ V := inf_le_left
  have hWx : W ≤ Uc h x ⊓ Xp X p := le_inf (inf_le_left.trans inf_le_left) inf_le_right
  have hWy : W ≤ Uc h y ⊓ Xp X p := le_inf (inf_le_left.trans inf_le_right) inf_le_right
  have hιiso : IsIso (w.app W) := Scheme.Hom.isIso_app w W (hWV.trans hVeq.le)
  have hιinj : Function.Injective (w.app W).hom := (ConcreteCategory.bijective_of_isIso (w.app W)).1
  have hV : ⊤ ≤ w ⁻¹ᵁ V := by rw [hVeq, Scheme.Hom.preimage_opensRange]
  have hφ : IsIso (w.appLE V ⊤ hV) := by
    have h1 : IsIso (w.app V) := Scheme.Hom.isIso_app w V hVeq.le
    have h2 : (⊤ : (Sp A).Opens) = w ⁻¹ᵁ V := le_antisymm hV le_top
    have h3 : IsIso (homOfLE hV) := by
      have : homOfLE hV = eqToHom h2 := rfl
      rw [this]; infer_instance
    rw [Scheme.Hom.appLE]; infer_instance
  let φ := w.appLE V ⊤ hV ≫ (Scheme.ΓSpecIso (CommRingCat.of A)).hom
  let e : Γ(X, V) ≃+* A := RingEquiv.ofBijective φ.hom (ConcreteCategory.bijective_of_isIso φ)
  have he : ∀ z, (w.appLE V ⊤ hV).hom (e.symm z) = (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom z := by
    intro z
    have h0 : (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom ((w.appLE V ⊤ hV).hom (e.symm z)) = z :=
      e.apply_symm_apply z
    have h1 : (w.appLE V ⊤ hV).hom (e.symm z) = (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
        ((Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom ((w.appLE V ⊤ hV).hom (e.symm z))) := by
      rw [← CommRingCat.comp_apply, Iso.hom_inv_id, CommRingCat.id_apply]
    exact h1.trans (congrArg _ h0)
  let u' : Γ(X, V)ˣ := Units.map e.symm.toRingHom.toMonoidHom u
  refine ⟨u', ?_⟩
  unfold RatioProp
  refine ⟨?_, ?_⟩
  · let gB : A →+* Γ(Sp A, w ⁻¹ᵁ W) := ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
      (Sp A).presheaf.map (homOfLE le_top : w ⁻¹ᵁ W ⟶ ⊤).op).hom
    have hpB : IsUnit ((p : Γ(Sp A, w ⁻¹ᵁ W))) := by
      have h0 := (isUnit_natCast_res h x).map ((w.app W).hom.comp (X.presheaf.map (homOfLE hWx).op).hom)
      erw [map_natCast, map_natCast] at h0
      exact h0
    have hgp : IsUnit (gB (p : A)) := by rw [map_natCast]; exact hpB
    let θ : Localization.Away (p : A) →+* Γ(Sp A, w ⁻¹ᵁ W) := IsLocalization.Away.lift (p : A) hgp
    have hθ : θ.comp (algebraMap A _) = gB := IsLocalization.Away.lift_comp _ hgp
    have hp1 : IsUnit (((algebraMap A (Localization.Away (p : A))).comp a1) (p : cR h x)) := by
      rw [map_natCast, ← map_natCast (algebraMap A (Localization.Away (p : A))) p]
      exact IsLocalization.Away.algebraMap_isUnit _
    have hp2 : IsUnit (((algebraMap A (Localization.Away (p : A))).comp a2) (p : cR h y)) := by
      rw [map_natCast, ← map_natCast (algebraMap A (Localization.Away (p : A))) p]
      exact IsLocalization.Away.algebraMap_isUnit _
    let χ1 : Localization.Away (p : cR h x) →+* Localization.Away (p : A) := IsLocalization.Away.lift _ hp1
    let χ2 : Localization.Away (p : cR h y) →+* Localization.Away (p : A) := IsLocalization.Away.lift _ hp2
    have hχ1 : χ1.comp (algebraMap _ _) = (algebraMap A _).comp a1 := IsLocalization.Away.lift_comp _ hp1
    have hχ2 : χ2.comp (algebraMap _ _) = (algebraMap A _).comp a2 := IsLocalization.Away.lift_comp _ hp2
    have key := hχ χ1 χ2 hχ1 hχ2
    have ex := ev_transport h x w a1 hw1 W hWx θ hθ χ1 hχ1 (cu h x)
    have ey := ev_transport h y w a2 hw2 W hWy θ hθ χ2 hχ2 (cu h y)
    have eu : (w.app W).hom ((X.presheaf.map (homOfLE hWV).op).hom (u' : Γ(X, V))) = gB u := by
      have m : X.presheaf.map (homOfLE hWV).op ≫ w.app W =
          w.appLE V ⊤ hV ≫ (Sp A).presheaf.map (homOfLE le_top : w ⁻¹ᵁ W ⟶ ⊤).op := by
        rw [Scheme.Hom.app_eq_appLE]
        erw [Scheme.Hom.map_appLE, Scheme.Hom.appLE_map]
      have m' := congrArg (fun f => f.hom (u' : Γ(X, V))) m
      simp only [CommRingCat.hom_comp, RingHom.comp_apply] at m'
      rw [m']
      have : (u' : Γ(X, V)) = e.symm (u : A) := rfl
      rw [this, he]
      rfl
    have goalEq : (w.app W).hom ((X.presheaf.map (homOfLE hWV).op).hom (u' : Γ(X, V))) *
        (w.app W).hom ((X.presheaf.map (homOfLE hWy).op).hom (ev h y (cu h y))) =
        (w.app W).hom ((X.presheaf.map (homOfLE hWx).op).hom (ev h x (cu h x))) := by
      rw [eu, ey, ex, ← key, map_mul]
      congr 1
      exact (congrArg (fun f => f (u : A)) hθ).symm
    apply Units.ext
    apply hιinj
    rw [Units.val_mul, map_mul]
    exact goalEq
  · have h0 : ((u' : Γ(X, V)) - 1) = e.symm ((u : A) - 1) := by
      rw [map_sub, map_one]; rfl
    rw [h0]
    exact radical_map e.symm.toRingHom p hu

end GlobalTheory.UnitGlueTransport
