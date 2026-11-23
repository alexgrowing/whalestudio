import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real

namespace GlobalTheory.AffinePointValues

lemma appLE_specMap_fromSpec {Y : Scheme.{0}} {V : Y.Opens} (hV : IsAffineOpen V) {R : CommRingCat.{0}}
    (f : Γ(Y, V) ⟶ R) (e) :
    (Spec.map f ≫ hV.fromSpec).appLE V ⊤ e ≫ (Scheme.ΓSpecIso R).hom = f := by

  apply Spec.map_injective
  rw [← cancel_mono hV.fromSpec, Spec.map_comp, Category.assoc,
    IsAffineOpen.SpecMap_appLE_fromSpec _ hV (isAffineOpen_top _) e,
    IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Category.assoc, ← Spec.map_comp,
    Iso.inv_hom_id, Spec.map_id, Category.id_comp]

lemma specMap_appLE_fromSpec {Y : Scheme.{0}} {V : Y.Opens} (hV : IsAffineOpen V) {R : CommRingCat.{0}}
    (x : Spec R ⟶ Y) (hx : ⊤ ≤ x ⁻¹ᵁ V) :
    Spec.map (x.appLE V ⊤ hx ≫ (Scheme.ΓSpecIso R).hom) ≫ hV.fromSpec = x := by
  rw [Spec.map_comp, Category.assoc, IsAffineOpen.SpecMap_appLE_fromSpec x hV (isAffineOpen_top _) hx,
    IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Category.assoc, ← Spec.map_comp,
    Iso.inv_hom_id, Spec.map_id, Category.id_comp]

lemma fromSpec_comp {Y : Scheme.{0}} {V : Y.Opens} (hV : IsAffineOpen V) {R : CommRingCat.{0}}
    (s : Y ⟶ Spec R) (h) :
    hV.fromSpec ≫ s = Spec.map ((Scheme.ΓSpecIso R).inv ≫ s.appLE ⊤ V h) := by
  rw [← IsAffineOpen.SpecMap_appLE_fromSpec s (isAffineOpen_top _) hV h,
    IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, Spec.map_comp]

end GlobalTheory.AffinePointValues

namespace GlobalTheory

open AffinePointValues in

theorem existsUnique_point_of_ringHom :
    (∀ (X : Over (Sp ℂ)) (U : X.left.Opens), IsAffineOpen U → ∀ e : Γ(X.left, U) →+* ℂ, (∀ a, e (constFn X.hom U a) = a) → ∃! x : (𝟙_ (Over (Sp ℂ)) ⟶ X), ⊤ ≤ (x).left ⁻¹ᵁ U ∧ ∀ f, valAt' x.left U f = e f) := by
  intro X U hU e he
  let φ : Γ(X.left, U) ⟶ CommRingCat.of ℂ := CommRingCat.ofHom e

  have hconst : (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ X.hom.appLE ⊤ U (fun _ _ => trivial) ≫ φ =
      𝟙 _ := by
    ext a
    exact he a
  have hw : (Spec.map φ ≫ hU.fromSpec) ≫ X.hom = (𝟙_ (Over (Sp ℂ))).hom := by
    rw [Category.assoc, fromSpec_comp hU X.hom (fun _ _ => trivial), ← Spec.map_comp,
      Category.assoc, hconst, Spec.map_id]
    rfl
  have hpre : ⊤ ≤ (Spec.map φ ≫ hU.fromSpec) ⁻¹ᵁ U := by
    intro p _
    show hU.fromSpec.base ((Spec.map φ).base p) ∈ U
    have h : (Spec.map φ).base p ∈ hU.fromSpec ⁻¹ᵁ U := by
      rw [IsAffineOpen.fromSpec_preimage_self]; trivial
    exact h
  refine ⟨Over.homMk (Spec.map φ ≫ hU.fromSpec) hw, ⟨hpre, fun f => ?_⟩, ?_⟩
  · show valAt' (Spec.map φ ≫ hU.fromSpec) U f = e f
    rw [valAt', dif_pos hpre]
    exact congrArg (fun g => g.hom f) (appLE_specMap_fromSpec hU φ hpre)
  · rintro y ⟨hy, hv⟩
    apply Over.OverMorphism.ext
    have h1 : y.left.appLE U ⊤ hy ≫ (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom = φ := by
      ext f
      have := hv f
      rw [valAt', dif_pos hy] at this
      exact this
    rw [← specMap_appLE_fromSpec hU y.left hy, h1]
    rfl

end GlobalTheory
