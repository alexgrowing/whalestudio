import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExtVStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.HomExtDvrSt

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
  {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]

theorem extV_genIso (t : SAB H (Sp V)) (tK : SAB H (Sp (FractionRing V)))
    (m : SABMap tK t (spMap (algebraMap V (FractionRing V)))) :
    ∃ io : genFibre V t.G ≅ tK.G, IsMonHom io.hom ∧
      io.hom.left ≫ m.φ = pullback.fst t.G.hom (specMap V (FractionRing V)) :=
  grpPullback_iso (isGrpPullback_pullback t.G _) m.cart

theorem extV_genIso' (t : SAB H (Sp V)) (tK : SAB H (Sp (FractionRing V)))
    (m : SABMap tK t (spMap (algebraMap V (FractionRing V)))) :
    ∃ ko : tK.G ≅ genFibre V t.G, IsMonHom ko.hom ∧
      ko.hom.left ≫ pullback.fst t.G.hom (specMap V (FractionRing V)) = m.φ :=
  grpPullback_iso m.cart (isGrpPullback_pullback t.G _)

theorem extV_unique (hHom : HomExtDvrSt) (t t' : SAB H (Sp V)) (tK : SAB H (Sp (FractionRing V)))
    (m : SABMap tK t (spMap (algebraMap V (FractionRing V)))) (g₁ g₂ : t.G ⟶ t'.G) [IsMonHom g₁] [IsMonHom g₂]
    (h : m.φ ≫ g₁.left = m.φ ≫ g₂.left) : g₁ = g₂ := by
  obtain ⟨io, -, hio⟩ := extV_genIso t tK m
  have hmap : (Over.pullback (specMap V (FractionRing V))).map g₁ =
      (Over.pullback (specMap V (FractionRing V))).map g₂ := by
    have A : ∀ g : t.G ⟶ t'.G, ((Over.pullback (specMap V (FractionRing V))).map g).left ≫
        pullback.fst t'.G.hom (specMap V (FractionRing V)) =
          pullback.fst t.G.hom (specMap V (FractionRing V)) ≫ g.left := fun g => pullback.lift_fst _ _ _
    have B : ∀ g : t.G ⟶ t'.G, ((Over.pullback (specMap V (FractionRing V))).map g).left ≫
        pullback.snd t'.G.hom (specMap V (FractionRing V)) =
          pullback.snd t.G.hom (specMap V (FractionRing V)) := fun g => pullback.lift_snd _ _ _
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · rw [A, A, ← hio, Category.assoc, Category.assoc, h]
    · rw [B, B]
  obtain ⟨ψ₀, -, hu⟩ := hHom V t.G t'.G t.semi t'.semi ((Over.pullback (specMap V (FractionRing V))).map g₁)
    inferInstance
  exact (hu g₁ ⟨inferInstance, rfl⟩).trans (hu g₂ ⟨inferInstance, hmap.symm⟩).symm

theorem extV_exists (hHom : HomExtDvrSt) (t t' : SAB H (Sp V)) (tK : SAB H (Sp (FractionRing V)))
    (m : SABMap tK t (spMap (algebraMap V (FractionRing V))))
    (m' : SABMap tK t' (spMap (algebraMap V (FractionRing V)))) :
    ∃ ψ : t.G ⟶ t'.G, IsMonHom ψ ∧ m.φ ≫ ψ.left = m'.φ := by
  obtain ⟨io, hiom, hio⟩ := extV_genIso t tK m
  obtain ⟨ko, -, hko⟩ := extV_genIso' t tK m
  obtain ⟨ko', hko'm, hko'⟩ := extV_genIso' t' tK m'
  have := hiom
  have := hko'm
  obtain ⟨ψ, ⟨hψm, hψ⟩, -⟩ := hHom V t.G t'.G t.semi t'.semi (io.hom ≫ ko'.hom) inferInstance
  have hkoio : ko.hom ≫ io.hom = 𝟙 _ := by
    apply Over.OverMorphism.ext
    apply m.cart.1.hom_ext
    · rw [Over.comp_left, Category.assoc, hio, hko, Over.id_left, Category.id_comp]
    · rw [Over.w, Over.id_left, Category.id_comp]
  refine ⟨ψ, hψm, ?_⟩
  rw [← hko, Category.assoc]
  have e : pullback.fst t.G.hom (specMap V (FractionRing V)) ≫ ψ.left =
      ((Over.pullback (specMap V (FractionRing V))).map ψ).left ≫ pullback.fst t'.G.hom (specMap V (FractionRing V)) :=
    (pullback.lift_fst _ _ _).symm
  rw [e, hψ, ← Category.assoc, ← Over.comp_left, ← Category.assoc, hkoio, Category.id_comp, hko']

theorem extV_grp (hHom : HomExtDvrSt) (t t' : SAB H (Sp V)) (tK : SAB H (Sp (FractionRing V)))
    (m : SABMap tK t (spMap (algebraMap V (FractionRing V))))
    (m' : SABMap tK t' (spMap (algebraMap V (FractionRing V)))) :
    ∃ ψ : t.G ≅ t'.G, IsMonHom ψ.hom ∧ m.φ ≫ ψ.hom.left = m'.φ ∧
      ∀ a, t.act.act a ≫ ψ.hom = ψ.hom ≫ t'.act.act a := by
  obtain ⟨ψ, hψm, hψ⟩ := extV_exists hHom t t' tK m m'
  obtain ⟨ψ', hψ'm, hψ'⟩ := extV_exists hHom t' t tK m' m
  have := hψm
  have := hψ'm
  have h1 : ψ ≫ ψ' = 𝟙 _ := extV_unique hHom t t tK m _ _ (by rw [Over.comp_left, ← Category.assoc, hψ, hψ',
    Over.id_left, Category.comp_id])
  have h2 : ψ' ≫ ψ = 𝟙 _ := extV_unique hHom t' t' tK m' _ _ (by rw [Over.comp_left, ← Category.assoc, hψ', hψ,
    Over.id_left, Category.comp_id])
  refine ⟨⟨ψ, ψ', h1, h2⟩, hψm, hψ, fun a => ?_⟩
  have ha := t.act.hom a
  have ha' := t'.act.hom a
  refine extV_unique hHom t t' tK m _ _ ?_
  show m.φ ≫ (t.act.act a ≫ ψ).left = m.φ ≫ (ψ ≫ t'.act.act a).left
  rw [Over.comp_left, Over.comp_left, ← Category.assoc, ← m.act, Category.assoc, hψ, ← Category.assoc, hψ, m'.act]

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
