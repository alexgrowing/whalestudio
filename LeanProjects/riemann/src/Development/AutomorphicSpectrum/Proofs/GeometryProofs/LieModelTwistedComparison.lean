import Mathlib
import Development.AutomorphicSpectrum.Statements.GeometryStatements.HodgeComparisonCompatibility
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.LieIntertwining

theorem act_intertwine : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (g : HostAut H) (Ω : Type) [Field Ω]
    (X X' : Scheme.{0}) (ξ : Sp Ω ⟶ X) (ξ' : Sp Ω ⟶ X') (t : SAB H X) (t' : SAB H X') (tΩ : SAB H (Sp Ω))
    (m : SABMap tΩ t ξ) (m' : SABMap (twistSAB tΩ g) t' ξ') (V V' : Type) [AddCommGroup V] [Module Ω V]
    [AddCommGroup V'] [Module Ω V'] (M : LieModel t.G ξ V) (M' : LieModel t'.G ξ' V')
    (ρ : 𝓞 E →+* Module.End Ω V) (ρ' : 𝓞 E →+* Module.End Ω V') (φ : V ≃ₗ[Ω] V'),
    M.IsActOf t.act.act ρ → M'.IsActOf t'.act.act ρ' →
    (∀ v, ∃ w : epsAt (𝟙 (Sp Ω)) ⟶ tΩ.G, w.left ≫ m.φ = (M.pt v).left ∧ w.left ≫ m'.φ = (M'.pt (φ v)).left) →
    ∀ a v, φ (ρ (g.s a) v) = ρ' a (φ v) := by
  intro E _ _ _ H g Ω _ X X' ξ ξ' t t' tΩ m m' V V' _ _ _ _ M M' ρ ρ' φ hM hM' tie a v
  obtain ⟨w, hw, hw'⟩ := tie v
  obtain ⟨w₃, hw₃, hw₃'⟩ := tie (ρ (g.s a) v)

  have h1 : (M.pt (ρ (g.s a) v)).left = (M.pt v).left ≫ (t.act.act (g.s a)).left := by
    rw [hM (g.s a) v]; rfl
  have h2 : (w.left ≫ (tΩ.act.act (g.s a)).left) ≫ m.φ = w₃.left ≫ m.φ := by
    rw [hw₃, h1, ← hw, Category.assoc, Category.assoc, m.act]
  have h3 : (w.left ≫ (tΩ.act.act (g.s a)).left) ≫ tΩ.G.hom = w₃.left ≫ tΩ.G.hom := by
    rw [Category.assoc, Over.w, Over.w, Over.w]
  have h4 : w.left ≫ (tΩ.act.act (g.s a)).left = w₃.left := m.cart.1.hom_ext h2 h3
  have h5 : (M'.pt (φ (ρ (g.s a) v))).left = (M'.pt (ρ' a (φ v))).left := by
    have h6 : (tΩ.act.act (g.s a)).left ≫ m'.φ = m'.φ ≫ (t'.act.act a).left := m'.act a
    rw [← hw₃', ← h4, hM' a (φ v), Over.comp_left, ← hw']
    exact (Category.assoc _ _ _).trans ((congrArg (w.left ≫ ·) h6).trans (Category.assoc _ _ _).symm)
  exact M'.inj (Over.OverMorphism.ext h5)

end GlobalTheory.CompanionTheory.Ar.LieIntertwining
