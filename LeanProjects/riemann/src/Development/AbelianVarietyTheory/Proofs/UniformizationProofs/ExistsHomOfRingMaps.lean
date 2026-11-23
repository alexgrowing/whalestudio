import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.RingGlue

noncomputable def loc {Y B : Scheme.{0}} {W : Y.Opens} {V : B.Opens} (hV : IsAffineOpen V)
    (ψ : Γ(B, V) ⟶ Γ(Y, W)) : W.toScheme ⟶ B :=
  W.toSpecΓ ≫ Spec.map ψ ≫ hV.fromSpec

theorem homOfLE_loc {Y B : Scheme.{0}} {W W' : Y.Opens} {V V' : B.Opens} (hV : IsAffineOpen V)
    (hV' : IsAffineOpen V') (ψ : Γ(B, V) ⟶ Γ(Y, W)) (ψ' : Γ(B, V') ⟶ Γ(Y, W'))
    (h : W' ≤ W) (e : V' ≤ V)
    (H : B.presheaf.map (homOfLE e).op ≫ ψ' = ψ ≫ Y.presheaf.map (homOfLE h).op) :
    Y.homOfLE h ≫ loc hV ψ = loc hV' ψ' := by
  unfold loc
  rw [← IsAffineOpen.map_fromSpec hV hV' (homOfLE e).op, ← Spec.map_comp_assoc, H,
    Spec.map_comp_assoc, Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_assoc]

theorem appLE_of_loc {Y B : Scheme.{0}} {W : Y.Opens} {V : B.Opens} (hV : IsAffineOpen V)
    (ψ : Γ(B, V) ⟶ Γ(Y, W)) (q : Y ⟶ B) (hq : W.ι ≫ q = loc hV ψ) :
    ∃ h : W ≤ q ⁻¹ᵁ V, q.appLE V W h = ψ := by
  have h : W ≤ q ⁻¹ᵁ V := by
    intro y hy
    have h1 : q y = hV.fromSpec ((W.toSpecΓ ≫ Spec.map ψ) ⟨y, hy⟩) := by
      have := congr($(hq) ⟨y, hy⟩)
      exact this
    change q y ∈ (V : Set B)
    rw [h1, ← hV.range_fromSpec]
    exact ⟨_, rfl⟩
  refine ⟨h, ?_⟩
  have h2 : W.toSpecΓ ≫ Spec.map (q.appLE V W h) ≫ hV.fromSpec = W.ι ≫ q := by
    rw [Scheme.Opens.toSpecΓ_SpecMap_appLE_assoc, IsAffineOpen.toSpecΓ_fromSpec,
      Scheme.Hom.resLE_comp_ι]
  rw [hq, loc, ← Category.assoc, ← Category.assoc, cancel_mono] at h2
  have h3 := congr(($h2).appTop)
  simp only [Scheme.Hom.comp_appTop, Scheme.Opens.toSpecΓ_appTop,
    Scheme.ΓSpecIso_naturality_assoc] at h3
  simpa only [cancel_epi, cancel_mono] using h3

set_option backward.isDefEq.respectTransparency false in

theorem exists_hom_of_ring_maps : (∀ (Y B : Scheme.{0}) (κ : Type) (W : κ → Y.Opens) (V : κ → B.Opens), (∀ k, IsAffineOpen (V k)) → ∀ (ψ : ∀ k, Γ(B, V k) ⟶ Γ(Y, W k)), (∀ y : Y, ∃ k, y ∈ W k) → (∀ (k l : κ) (y : Y), y ∈ W k → y ∈ W l → ∃ (m : κ) (h : W m ≤ W k) (h' : W m ≤ W l) (e : V m ≤ V k) (e' : V m ≤ V l), y ∈ W m ∧ B.presheaf.map (homOfLE e).op ≫ ψ m = ψ k ≫ Y.presheaf.map (homOfLE h).op ∧ B.presheaf.map (homOfLE e').op ≫ ψ m = ψ l ≫ Y.presheaf.map (homOfLE h').op) → ∃ q : Y ⟶ B, ∀ k, ∃ h : W k ≤ q ⁻¹ᵁ V k, q.appLE (V k) (W k) h = ψ k) := by
  intro Y B κ W V hV ψ hc hbas
  let 𝒱 : Y.OpenCover := Y.openCoverOfIsOpenCover W (by
    rw [TopologicalSpace.IsOpenCover, eq_top_iff]
    intro y _
    obtain ⟨k, hk⟩ := hc y
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨k, hk⟩)
  let q : Y ⟶ B := 𝒱.glueMorphisms (fun k ↦ loc (hV k) (ψ k)) (by
    intro k l
    apply Scheme.hom_ext_of_forall
    intro x
    have hx : (pullback.fst (𝒱.f k) (𝒱.f l) x).1 = (pullback.snd (𝒱.f k) (𝒱.f l) x).1 :=
      congr($(pullback.condition (f := 𝒱.f k) (g := 𝒱.f l)) x)
    obtain ⟨m, h1, h2, e1, e2, hxW, H1, H2⟩ := hbas k l _ (pullback.fst (𝒱.f k) (𝒱.f l) x).2
      (hx ▸ (pullback.snd (𝒱.f k) (𝒱.f l) x).2)
    let α : (W m).toScheme ⟶ pullback (𝒱.f k) (𝒱.f l) :=
      pullback.lift (Y.homOfLE h1) (Y.homOfLE h2) ((Y.homOfLE_ι h1).trans (Y.homOfLE_ι h2).symm)
    have hα1 : α ≫ pullback.fst _ _ = Y.homOfLE h1 := pullback.lift_fst _ _ _
    have hα2 : α ≫ pullback.snd _ _ = Y.homOfLE h2 := pullback.lift_snd _ _ _
    have : IsOpenImmersion (α ≫ pullback.fst _ _) := by rw [hα1]; infer_instance
    have : IsOpenImmersion α := .of_comp _ (pullback.fst _ _)
    refine ⟨α.opensRange, ⟨⟨_, hxW⟩, ?_⟩, ?_⟩
    · apply (pullback.fst (𝒱.f k) (𝒱.f l)).isOpenEmbedding.injective
      rw [← Scheme.Hom.comp_apply, hα1]
      exact Subtype.ext (Scheme.homOfLE_apply _ _)
    · rw [← cancel_epi α.isoOpensRange.hom]
      simp only [Scheme.Hom.isoOpensRange_hom_ι_assoc]
      rw [reassoc_of% hα1, reassoc_of% hα2]
      exact (homOfLE_loc (hV k) (hV m) _ _ h1 e1 H1).trans
        (homOfLE_loc (hV l) (hV m) _ _ h2 e2 H2).symm)
  exact ⟨q, fun k ↦ appLE_of_loc (hV k) (ψ k) q (𝒱.ι_glueMorphisms _ _ k)⟩

end GlobalTheory.RingGlue
