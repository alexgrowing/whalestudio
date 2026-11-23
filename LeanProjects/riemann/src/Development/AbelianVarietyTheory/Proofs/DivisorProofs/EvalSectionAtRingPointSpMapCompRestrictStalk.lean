import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatPath

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.Nef

theorem evAt_eq_comp {R : Type} [CommRing R] {X : Scheme.{0}} (b : Sp R ⟶ X) {U : X.Opens} (h : ⊤ ≤ b ⁻¹ᵁ U) :
    CommRingCat.ofHom (evAt b h) = b.appLE U ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom := rfl

theorem evAt_spMap_comp (R R' : Type) [CommRing R] [CommRing R'] (X : Scheme.{0}) (φ : R →+* R') (b : Sp R ⟶ X)
    (U : X.Opens) (h : ⊤ ≤ b ⁻¹ᵁ U) (h' : ⊤ ≤ (spMap φ ≫ b) ⁻¹ᵁ U) (f : Γ(X, U)) :
    evAt (spMap φ ≫ b) h' f = φ (evAt b h f) := by
  have e2 := Scheme.Hom.appLE_comp_appLE (spMap φ) b U ⊤ ⊤ h le_rfl
  have e3 : (spMap φ).appLE ⊤ ⊤ le_rfl = (spMap φ).appTop := (Scheme.Hom.app_eq_appLE _).symm
  have e4 : (spMap φ ≫ b).appLE U ⊤ h' ≫ (Scheme.ΓSpecIso (CommRingCat.of R')).hom =
      b.appLE U ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom ≫ CommRingCat.ofHom φ := by
    rw [← e2, e3, Category.assoc]
    erw [Scheme.ΓSpecIso_naturality]
  exact congrArg (fun ψ => ψ.hom f) e4

theorem evAt_comp (R : Type) [CommRing R] (X Y : Scheme.{0}) (b : Sp R ⟶ X) (g : X ⟶ Y) (U : X.Opens) (V : Y.Opens)
    (h : ⊤ ≤ b ⁻¹ᵁ U) (h' : ⊤ ≤ (b ≫ g) ⁻¹ᵁ V) (e : U ≤ g ⁻¹ᵁ V) (f : Γ(Y, V)) :
    evAt (b ≫ g) h' f = evAt b h (g.appLE V U e f) := by
  have e2 := Scheme.Hom.appLE_comp_appLE b g V U ⊤ e h
  have e4 : (b ≫ g).appLE V ⊤ h' ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom =
      g.appLE V U e ≫ b.appLE U ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom := by
    rw [← Category.assoc, e2]
  exact congrArg (fun ψ => ψ.hom f) e4

theorem evAt_res (R : Type) [CommRing R] (X : Scheme.{0}) (b : Sp R ⟶ X) (U U' : X.Opens) (e : U' ≤ U)
    (h : ⊤ ≤ b ⁻¹ᵁ U) (h' : ⊤ ≤ b ⁻¹ᵁ U') (f : Γ(X, U)) :
    evAt b h' (X.presheaf.map (homOfLE e).op f) = evAt b h f := by
  have e2 := Scheme.Hom.map_appLE b h' (homOfLE e).op
  have e4 : X.presheaf.map (homOfLE e).op ≫ b.appLE U' ⊤ h' ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom =
      b.appLE U ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom := by
    rw [← Category.assoc, e2]
  exact congrArg (fun ψ => ψ.hom f) e4

theorem top_le_iff_closedPoint_mem (R : Type) [CommRing R] [IsLocalRing R] (X : Scheme.{0}) (b : Sp R ⟶ X)
    (U : X.Opens) : ⊤ ≤ b ⁻¹ᵁ U ↔ b (IsLocalRing.closedPoint R) ∈ U := by
  refine ⟨fun h => h (Set.mem_univ _), fun hb q _ => ?_⟩
  exact ((IsLocalRing.specializes_closedPoint (q : PrimeSpectrum R)).map b.continuous).mem_open U.2 hb

theorem eq_of_evAt_eq (R : Type) [CommRing R] (X : Scheme.{0}) (b b' : Sp R ⟶ X) (U : X.Opens) (hU : IsAffineOpen U)
    (h : ⊤ ≤ b ⁻¹ᵁ U) (h' : ⊤ ≤ b' ⁻¹ᵁ U) (he : evAt b h = evAt b' h') : b = b' := by
  have k0 : b.appLE U ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom =
      b'.appLE U ⊤ h' ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom := by
    rw [← evAt_eq_comp, ← evAt_eq_comp, he]
  have k : b.appLE U ⊤ h = b'.appLE U ⊤ h' := (cancel_mono _).1 k0
  have e1 := IsAffineOpen.SpecMap_appLE_fromSpec b hU (isAffineOpen_top (Sp R)) h
  have e2 := IsAffineOpen.SpecMap_appLE_fromSpec b' hU (isAffineOpen_top (Sp R)) h'
  rw [k] at e1
  have e3 := e1.symm.trans e2
  rw [IsAffineOpen.fromSpec_top] at e3
  exact (cancel_epi _).1 e3

theorem exists_evAt_eq (R : Type) [CommRing R] (X : Scheme.{0}) (U : X.Opens) (hU : IsAffineOpen U)
    (φ : Γ(X, U) →+* R) : ∃ (b : Sp R ⟶ X) (h : ⊤ ≤ b ⁻¹ᵁ U), evAt b h = φ := by
  have hfs : ⊤ ≤ hU.fromSpec ⁻¹ᵁ U := by rw [hU.fromSpec_preimage_self]
  have h : ⊤ ≤ (Spec.map (CommRingCat.ofHom φ) ≫ hU.fromSpec : Sp R ⟶ X) ⁻¹ᵁ U :=
    fun _ _ => hU.range_fromSpec.subset ⟨_, rfl⟩
  refine ⟨Spec.map (CommRingCat.ofHom φ) ≫ hU.fromSpec, h, ?_⟩
  have e1 : hU.fromSpec.appLE U ⊤ hfs = (Scheme.ΓSpecIso Γ(X, U)).inv := by
    rw [Scheme.Hom.appLE, IsAffineOpen.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
    convert Category.comp_id _
    exact (Spec Γ(X, U)).presheaf.map_id _
  have e2 := Scheme.Hom.appLE_comp_appLE (Spec.map (CommRingCat.ofHom φ)) hU.fromSpec U ⊤ ⊤ hfs le_rfl
  have e3 : (Spec.map (CommRingCat.ofHom φ)).appLE ⊤ ⊤ le_rfl = (Spec.map (CommRingCat.ofHom φ)).appTop :=
    (Scheme.Hom.app_eq_appLE _).symm
  have e4 : CommRingCat.ofHom (evAt (Spec.map (CommRingCat.ofHom φ) ≫ hU.fromSpec : Sp R ⟶ X) h) =
      CommRingCat.ofHom φ := by
    rw [evAt_eq_comp, ← e2, e1, e3, Category.assoc]
    erw [Scheme.ΓSpecIso_naturality]
    exact (Scheme.ΓSpecIso Γ(X, U)).inv_hom_id_assoc _
  exact congrArg CommRingCat.Hom.hom e4

theorem evAt_fromSpecStalk' (R : Type) [CommRing R] (X : Scheme.{0}) (p : X) (φ : X.presheaf.stalk p →+* R)
    (U : X.Opens) (hp : p ∈ U) :
    ∃ h : ⊤ ≤ (Spec.map (CommRingCat.ofHom φ) ≫ X.fromSpecStalk p : Sp R ⟶ X) ⁻¹ᵁ U,
      ∀ f, evAt (Spec.map (CommRingCat.ofHom φ) ≫ X.fromSpecStalk p : Sp R ⟶ X) h f =
        φ (X.presheaf.germ U p hp f) := by
  have h0 : ⊤ ≤ X.fromSpecStalk p ⁻¹ᵁ U := fun q _ =>
    ((IsLocalRing.specializes_closedPoint (q : PrimeSpectrum _)).map (X.fromSpecStalk p).continuous).mem_open U.2
      (by rw [Scheme.fromSpecStalk_closedPoint]; exact hp)
  refine ⟨fun q _ => h0 (Set.mem_univ _), fun s => ?_⟩
  have e1 : (X.fromSpecStalk p).appLE U ⊤ h0 = X.presheaf.germ U p hp ≫ (Scheme.ΓSpecIso _).inv := by
    rw [Scheme.Hom.appLE, Scheme.fromSpecStalk_app hp, Category.assoc, Category.assoc, ← Functor.map_comp]
    exact congrArg (_ ≫ ·) ((congrArg (_ ≫ ·) ((Spec (X.presheaf.stalk p)).presheaf.map_id _)).trans (Category.comp_id _))
  have e2 := Scheme.Hom.appLE_comp_appLE (Spec.map (CommRingCat.ofHom φ)) (X.fromSpecStalk p) U ⊤ ⊤ h0 le_rfl
  have e3 : (Spec.map (CommRingCat.ofHom φ)).appLE ⊤ ⊤ le_rfl = (Spec.map (CommRingCat.ofHom φ)).appTop :=
    (Scheme.Hom.app_eq_appLE _).symm
  have e4 : (Spec.map (CommRingCat.ofHom φ) ≫ X.fromSpecStalk p).appLE U ⊤ (fun q _ => h0 (Set.mem_univ _)) ≫
      (Scheme.ΓSpecIso (CommRingCat.of R)).hom = X.presheaf.germ U p hp ≫ CommRingCat.ofHom φ := by
    rw [← e2, e1, e3, Category.assoc, Category.assoc]
    erw [Scheme.ΓSpecIso_naturality]
    exact congrArg (_ ≫ ·) ((Scheme.ΓSpecIso (X.presheaf.stalk p)).inv_hom_id_assoc _)
  exact congrArg (fun ψ => ψ.hom s) e4

theorem evAt_calculus : (∀ (R R' : Type) [CommRing R] [CommRing R'] (X : Scheme.{0}) (φ : R →+* R') (b : Sp R ⟶ X) (U : X.Opens) (h : ⊤ ≤ b ⁻¹ᵁ U) (h' : ⊤ ≤ (spMap φ ≫ b) ⁻¹ᵁ U) (f : Γ(X, U)), evAt (spMap φ ≫ b) h' f = φ (evAt b h f)) ∧ (∀ (R : Type) [CommRing R] (X Y : Scheme.{0}) (b : Sp R ⟶ X) (g : X ⟶ Y) (U : X.Opens) (V : Y.Opens) (h : ⊤ ≤ b ⁻¹ᵁ U) (h' : ⊤ ≤ (b ≫ g) ⁻¹ᵁ V) (e : U ≤ g ⁻¹ᵁ V) (f : Γ(Y, V)), evAt (b ≫ g) h' f = evAt b h (g.appLE V U e f)) ∧ (∀ (R : Type) [CommRing R] (X : Scheme.{0}) (b : Sp R ⟶ X) (U U' : X.Opens) (e : U' ≤ U) (h : ⊤ ≤ b ⁻¹ᵁ U) (h' : ⊤ ≤ b ⁻¹ᵁ U') (f : Γ(X, U)), evAt b h' (X.presheaf.map (homOfLE e).op f) = evAt b h f) ∧ (∀ (R : Type) [CommRing R] [IsLocalRing R] (X : Scheme.{0}) (b : Sp R ⟶ X) (U : X.Opens), ⊤ ≤ b ⁻¹ᵁ U ↔ b (IsLocalRing.closedPoint R) ∈ U) ∧ (∀ (R : Type) [CommRing R] (X : Scheme.{0}) (b b' : Sp R ⟶ X) (U : X.Opens), IsAffineOpen U → ∀ (h : ⊤ ≤ b ⁻¹ᵁ U) (h' : ⊤ ≤ b' ⁻¹ᵁ U), evAt b h = evAt b' h' → b = b') ∧ (∀ (R : Type) [CommRing R] (X : Scheme.{0}) (U : X.Opens), IsAffineOpen U → ∀ φ : Γ(X, U) →+* R, ∃ (b : Sp R ⟶ X) (h : ⊤ ≤ b ⁻¹ᵁ U), evAt b h = φ) ∧ (∀ (R : Type) [CommRing R] (X : Scheme.{0}) (p : X) (φ : X.presheaf.stalk p →+* R) (U : X.Opens) (hp : p ∈ U), ∃ h : ⊤ ≤ (Spec.map (CommRingCat.ofHom φ) ≫ X.fromSpecStalk p : Sp R ⟶ X) ⁻¹ᵁ U, ∀ f, evAt (Spec.map (CommRingCat.ofHom φ) ≫ X.fromSpecStalk p : Sp R ⟶ X) h f = φ (X.presheaf.germ U p hp f)) :=
  ⟨evAt_spMap_comp, evAt_comp, evAt_res, top_le_iff_closedPoint_mem, eq_of_evAt_eq, exists_evAt_eq,
    evAt_fromSpecStalk'⟩

end GlobalTheory.Nef
