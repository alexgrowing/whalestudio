import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatPath

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

namespace GlobalTheory.Nef

theorem fromSpecStalk_preimage_top {X : Scheme.{0}} (x : X) (U : X.Opens) (hx : x ∈ U) :
    ⊤ ≤ X.fromSpecStalk x ⁻¹ᵁ U := by
  intro z _
  have hz : X.fromSpecStalk x z ⤳ x := by
    have : X.fromSpecStalk x z ∈ Set.range (X.fromSpecStalk x) := ⟨z, rfl⟩
    rwa [Scheme.range_fromSpecStalk] at this
  exact hz.mem_open U.2 hx

theorem fromSpecStalk_appLE_top {X : Scheme.{0}} (x : X) (U : X.Opens) (hx : x ∈ U) :
    (X.fromSpecStalk x).appLE U ⊤ (fromSpecStalk_preimage_top x U hx) =
      X.presheaf.germ U x hx ≫ (Scheme.ΓSpecIso (X.presheaf.stalk x)).inv := by
  rw [Scheme.Hom.appLE, Scheme.fromSpecStalk_app hx]
  simp only [Category.assoc, ← Functor.map_comp]
  have e : ((homOfLE le_top).op ≫ (homOfLE (fromSpecStalk_preimage_top x U hx)).op :
      Opposite.op (⊤ : (Spec (X.presheaf.stalk x)).Opens) ⟶ Opposite.op ⊤) = 𝟙 _ := rfl
  rw [e, CategoryTheory.Functor.map_id, Category.comp_id]

theorem appLE_eq_of_eq {X Y : Scheme.{0}} {g g' : X ⟶ Y} (hg : g = g') (V : Y.Opens) (W : X.Opens)
    (h : W ≤ g ⁻¹ᵁ V) (h' : W ≤ g' ⁻¹ᵁ V) : g.appLE V W h = g'.appLE V W h' := by
  subst hg; rfl

theorem germ_comp_of_spec {X Y : Scheme.{0}} {x : X} {y : Y} (φ : Y.presheaf.stalk y ⟶ X.presheaf.stalk x)
    (f : X ⟶ Y) (hφ : Spec.map φ ≫ Y.fromSpecStalk y = X.fromSpecStalk x ≫ f)
    (V : Y.Opens) (hy : y ∈ V) (U : X.Opens) (hx : x ∈ U) (h : U ≤ f ⁻¹ᵁ V) :
    Y.presheaf.germ V y hy ≫ φ = f.appLE V U h ≫ X.presheaf.germ U x hx := by
  have h1 : ⊤ ≤ (Spec.map φ ≫ Y.fromSpecStalk y) ⁻¹ᵁ V := by
    intro z _
    exact fromSpecStalk_preimage_top y V hy (Set.mem_univ _)
  have h2 : ⊤ ≤ (X.fromSpecStalk x ≫ f) ⁻¹ᵁ V := hφ ▸ h1
  have key := appLE_eq_of_eq hφ V ⊤ h1 h2
  have eL : (Spec.map φ ≫ Y.fromSpecStalk y).appLE V ⊤ h1 =
      (Y.fromSpecStalk y).appLE V ⊤ (fromSpecStalk_preimage_top y V hy) ≫
        (Spec.map φ).appLE ⊤ ⊤ (by simp) := by
    exact (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm
  have eR : (X.fromSpecStalk x ≫ f).appLE V ⊤ h2 =
      f.appLE V U h ≫ (X.fromSpecStalk x).appLE U ⊤ (fromSpecStalk_preimage_top x U hx) := by
    exact (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm
  have eT : (Spec.map φ).appLE ⊤ ⊤ (by simp) = (Spec.map φ).appTop := by
    simp only [Scheme.Hom.appLE, Scheme.Hom.preimage_top, Category.comp_id]
    first | rfl | simp
  rw [eL, eR, eT, fromSpecStalk_appLE_top y V hy, fromSpecStalk_appLE_top x U hx, Category.assoc,
    ← Scheme.ΓSpecIso_inv_naturality, ← Category.assoc, ← Category.assoc] at key
  exact (cancel_mono _).1 key

theorem germ_apply_of_spec {X Y : Scheme.{0}} {x : X} {y : Y} (φ : Y.presheaf.stalk y →+* X.presheaf.stalk x)
    (f : X ⟶ Y) (hφ : Spec.map (CommRingCat.ofHom φ) ≫ Y.fromSpecStalk y = X.fromSpecStalk x ≫ f)
    (V : Y.Opens) (hy : y ∈ V) (U : X.Opens) (hx : x ∈ U) (h : U ≤ f ⁻¹ᵁ V) (a : Γ(Y, V)) :
    φ (Y.presheaf.germ V y hy a) = X.presheaf.germ U x hx (f.appLE V U h a) := by
  have e := congrArg (fun g => g.hom a) (germ_comp_of_spec (CommRingCat.ofHom φ) f hφ V hy U hx h)
  exact e

theorem stalkData_germ : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], ∀ (s : S) (π : S.presheaf.stalk s →+* G.left.presheaf.stalk (unitSec G s)) (ε : G.left.presheaf.stalk (unitSec G s) →+* S.presheaf.stalk s) (m : G.left.presheaf.stalk (unitSec G s) →+* G.left.presheaf.stalk (unitSec G s)), StalkData G s π ε m → (∀ (V : S.Opens) (hs : s ∈ V) (U : G.left.Opens) (hU : unitSec G s ∈ U) (h : U ≤ G.hom ⁻¹ᵁ V) (a : Γ(S, V)), π (S.presheaf.germ V s hs a) = G.left.presheaf.germ U _ hU (G.hom.appLE V U h a)) ∧ (∀ (U : G.left.Opens) (hU : unitSec G s ∈ U) (V : S.Opens) (hs : s ∈ V) (h : V ≤ unitSec G ⁻¹ᵁ U) (f : Γ(G.left, U)), ε (G.left.presheaf.germ U _ hU f) = S.presheaf.germ V s hs ((unitSec G).appLE U V h f)) ∧ (∀ (U : G.left.Opens) (hU : unitSec G s ∈ U) (U' : G.left.Opens) (hU' : unitSec G s ∈ U') (h : U' ≤ sqr G ⁻¹ᵁ U) (f : Γ(G.left, U)), m (G.left.presheaf.germ U _ hU f) = G.left.presheaf.germ U' _ hU' ((sqr G).appLE U U' h f)) := by
  intro S G _ s π ε m hD
  exact ⟨fun V hs U hU h a => germ_apply_of_spec π G.hom hD.str V hs U hU h a,
    fun U hU V hs h f => germ_apply_of_spec ε (unitSec G) hD.unit U hU V hs h f,
    fun U hU U' hU' h f => germ_apply_of_spec m (sqr G) hD.sq U hU U' hU' h f⟩

end GlobalTheory.Nef
