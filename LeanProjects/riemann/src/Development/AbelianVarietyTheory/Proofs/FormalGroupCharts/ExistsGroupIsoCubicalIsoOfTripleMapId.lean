import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwoChartAtlas.AdditionLawSecondIdentity
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChartCmp

theorem isMonHom_of_mul_points {S : Scheme.{0}} {G G' : Over S} [GrpObj G] [GrpObj G'] (f : G ⟶ G')
    (h : ∀ (T : Over S) (x y : T ⟶ G), (x * y) ≫ f = (x ≫ f) * (y ≫ f)) : IsMonHom f where
  one_hom := by
    have e := h (𝟙_ _) 1 1
    rw [_root_.mul_one] at e
    have e2 : (1 : 𝟙_ (Over S) ⟶ G) ≫ f = 1 := by
      have := e.symm
      exact mul_eq_left.1 this
    simpa [Hom.one_def, toUnit_unique (toUnit (𝟙_ (Over S))) (𝟙 _)] using e2
  mul_hom := by
    have e := h _ (fst G G) (snd G G)
    rw [Hom.mul_def, Hom.mul_def, lift_fst_snd, Category.id_comp] at e
    rw [e, ← lift_fst_comp_snd_comp]

theorem exists_iso_of_sabMap_id : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] (t t' : SAB H (Sp V)) (n : SABMap t t' (𝟙 (Sp V))), ∃ ψ : t.G ≅ t'.G, ψ.hom.left = n.φ ∧ IsMonHom ψ.hom ∧ (∀ a, t.act.act a ≫ ψ.hom = ψ.hom ≫ t'.act.act a) ∧ n.cm.F3 = (ψ.hom ⊗ₘ ψ.hom ⊗ₘ ψ.hom).left ∧ ∃ w : LB.Iso t.PP.L (t'.PP.L.pull n.φ), CubIso n w := by
  intro E _ _ _ H V _ t t' n
  have hp := n.cart.1
  have hw : n.cm.F ≫ t'.G.hom = t.G.hom := by simpa using hp.w
  haveI : IsIso n.cm.F := hp.isIso_fst_of_isIso
  let ψ : t.G ≅ t'.G := Over.isoMk (asIso n.cm.F) hw
  have hψ : ψ.hom.left = n.cm.F := rfl
  refine ⟨ψ, rfl, ?_, fun a => ?_, ?_, ?_⟩
  · refine isMonHom_of_mul_points _ fun T x y => ?_
    apply Over.OverMorphism.ext
    have e := n.cart.2 T x y (pushPt hp.w x) (pushPt hp.w y) rfl rfl
    rw [Over.comp_left, hψ, ← e]
    exact mul_left_congr (Category.comp_id _) _ _ (x ≫ ψ.hom) (y ≫ ψ.hom) rfl rfl
  · apply Over.OverMorphism.ext
    exact n.act a
  · refine hom_ext_triple _ fun i => ?_
    rw [cubeMap_comp_proj_three, ← Over.comp_left, ← cubeProj_comp_map, Over.comp_left, hψ]
  · obtain ⟨w, h1, -, h3⟩ := n.lin
    exact ⟨w, h1, h3⟩

end GlobalTheory.ChartCmp
