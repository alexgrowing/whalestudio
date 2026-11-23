import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsCan

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeckeEx

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)
attribute [local instance] Over.cartesianMonoidalCategory

theorem translT_comp_isCan : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {T Ω : Type} [CommRing T] [CommRing Ω] (χ : T →+* Ω) {x : Sp T ⟶ Xo.X} {x₁ : Sp Ω ⟶ Xo.X} {pm : Gx x₁ ⟶ Gx x} (c : Over.mk x ⟶ Xo.univ.t.G) (c₁ : Over.mk x₁ ⟶ Xo.univ.t.G), IsCan χ pm → c₁.left = spMap χ ≫ c.left → (translT Xo.univ.t.G c₁).left ≫ pm = pm ≫ (translT Xo.univ.t.G c).left := by
  intro E _ _ _ H Dw l Xo T Ω _ _ χ x x₁ pm c c₁ h hc
  have hw : pm ≫ (Over.mk x ⊗ Xo.univ.t.G).hom = (Over.mk x₁ ⊗ Xo.univ.t.G).hom := by
    rw [← Over.w (snd (Over.mk x) Xo.univ.t.G), ← Over.w (snd (Over.mk x₁) Xo.univ.t.G), ← Category.assoc, h.2.1]
  let P : Over.mk x₁ ⊗ Xo.univ.t.G ⟶ Over.mk x ⊗ Xo.univ.t.G := Over.homMk pm hw
  let Φ : Over.mk x₁ ⟶ Over.mk x := Over.homMk (spMap χ) h.1.symm
  have hPf : P ≫ fst (Over.mk x) Xo.univ.t.G = fst (Over.mk x₁) Xo.univ.t.G ≫ Φ :=
    Over.OverMorphism.ext (by simpa [P, Φ] using h.2.2)
  have hPs : P ≫ snd (Over.mk x) Xo.univ.t.G = snd (Over.mk x₁) Xo.univ.t.G :=
    Over.OverMorphism.ext (by simpa [P] using h.2.1)
  have hΦ : Φ ≫ c = c₁ := Over.OverMorphism.ext (by simpa [Φ] using hc.symm)
  have key : translT Xo.univ.t.G c₁ ≫ P = P ≫ translT Xo.univ.t.G c := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, Category.assoc, hPf, translT, translT, lift_fst, lift_fst_assoc]
      exact hPf.symm
    · rw [Category.assoc, Category.assoc, hPs, translT, translT, lift_snd, lift_snd, translPt, translPt,
        comp_lift_assoc, reassoc_of% hPf, hPs, hΦ]
  have := congrArg CommaMorphism.left key
  simpa [P] using this

end GlobalTheory.HeckeEx
