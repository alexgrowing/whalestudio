import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsKerTorusExtension
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.CurveRootGeometry GlobalTheory.NeronCurve GlobalTheory.SS GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TorusPart

private theorem key {S S' : Scheme.{0}} {f : S' ⟶ S} {G : Over S} [GrpObj G] {G' : Over S'} [GrpObj G']
    {φ : G'.left ⟶ G.left} (hφ : IsGrpPullback G' G f φ) {X : Type} [AddCommGroup X] {u : splitTorus S X ⟶ G}
    {u' : splitTorus S' X ⟶ G'} (h : TorusCompat f φ u' u) (Z : Over S') (t : Z ⟶ splitTorus S' X) (g : Z ⟶ G') :
    ∃ (t₀ : Over.mk (Z.hom ≫ f) ⟶ splitTorus S X) (g₀ : Over.mk (Z.hom ≫ f) ⟶ G),
      (∀ χ, t₀.left.appTop.hom (charUnit S X χ).val = t.left.appTop.hom (charUnit S' X χ).val) ∧
      g₀.left = g.left ≫ φ ∧ ((t₀ ≫ u) * g₀).left = ((t ≫ u') * g).left ≫ φ := by
  obtain ⟨τ, hτ, hχ, e⟩ := h
  let t₀ : Over.mk (Z.hom ≫ f) ⟶ splitTorus S X := Over.homMk (t.left ≫ τ) (by
    rw [Category.assoc, hτ, ← Category.assoc, Over.w]; rfl)
  let g₀ : Over.mk (Z.hom ≫ f) ⟶ G := Over.homMk (g.left ≫ φ) (by
    rw [Category.assoc, hφ.1.w, ← Category.assoc, Over.w]; rfl)
  refine ⟨t₀, g₀, fun χ => ?_, rfl, ?_⟩
  · show (t.left ≫ τ).appTop.hom _ = _
    rw [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply, hχ]
  · refine hφ.2 Z (t ≫ u') g _ _ ?_ rfl
    rw [Over.comp_left, Over.comp_left, Category.assoc, ← e, ← Category.assoc]; rfl

private theorem appLE_comp_exists {Z Y Y' : Scheme.{0}} (a : Z ⟶ Y') (φ : Y' ⟶ Y) (b : Z ⟶ Y) (e : b = a ≫ φ)
    (V : Y.Opens) (h : ⊤ ≤ a ⁻¹ᵁ φ ⁻¹ᵁ V) (s : Γ(Y, V)) :
    ∃ h' : ⊤ ≤ b ⁻¹ᵁ V, (b.appLE V ⊤ h').hom s = (a.appLE (φ ⁻¹ᵁ V) ⊤ h).hom ((φ.app V).hom s) := by
  subst e
  refine ⟨h, ?_⟩
  exact congrArg (fun q => q.hom s) (Scheme.Hom.comp_appLE a φ V ⊤ h)

theorem UpperTheory.good_open_pullback :
    ∀ (S S' : Scheme.{0}) (f : S' ⟶ S), IsAffineHom f → ∀ (G : Over S) [GrpObj G] (G' : Over S') [GrpObj G']
        (φ : G'.left ⟶ G.left), IsGrpPullback G' G f φ → ∀ (X : Type) [AddCommGroup X] (u : splitTorus S X ⟶ G)
        (u' : splitTorus S' X ⟶ G'), TorusCompat f φ u' u → ∀ V : G.left.Opens, GoodOpen u V → GoodOpen u' (φ ⁻¹ᵁ V) := by
  intro S S' f hf G _ G' _ φ hφ X _ u u' h V ⟨hV, hst, w, hw⟩
  have haff : IsAffineHom φ := MorphismProperty.of_isPullback hφ.1.flip hf
  refine ⟨hV.preimage φ, ?_, (Units.map (φ.app V).hom.toMonoidHom).comp w, fun χ Z t g h₁ h₂ => ?_⟩
  · obtain ⟨t₀, g₀, -, e₁, e₂⟩ := key hφ h _ (fst (splitTorus S' X) G') (snd (splitTorus S' X) G')
    intro x hx
    have h1 : g₀.left x ∈ V := by rw [e₁]; exact hx
    have h2 : (lift t₀ g₀).left x ∈ (snd (splitTorus S X) G).left ⁻¹ᵁ V := by
      show (lift t₀ g₀ ≫ snd _ _).left x ∈ V
      rwa [lift_snd]
    have h3 : (lift t₀ g₀ ≫ ((fst (splitTorus S X) G ≫ u) * snd (splitTorus S X) G)).left x ∈ V := hst h2
    rw [MonObj.comp_mul, lift_fst_assoc, lift_snd, e₂] at h3
    exact h3
  · obtain ⟨t₀, g₀, e₀, e₁, e₂⟩ := key hφ h Z t g
    obtain ⟨k₁, r₁⟩ := appLE_comp_exists _ φ _ e₂ V h₁ (w (Multiplicative.ofAdd χ)).val
    obtain ⟨k₂, r₂⟩ := appLE_comp_exists _ φ _ e₁ V h₂ (w (Multiplicative.ofAdd χ)).val
    have := hw χ _ t₀ g₀ k₁ k₂
    rw [r₁, r₂, e₀] at this
    exact this
