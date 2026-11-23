import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalCoeffF
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.LvCover

theorem exists_goodMap_rankZero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), D.p + D.q = 0 →
    ∀ (l l' : Level H) (Xo : Moduli D l) (Xo' : Moduli D l') (c : Coeff l) (c' : Coeff l') (h : c'.F ≤ c.F)
      (Y : GlobalTheory.TorRef.GMod Xo c) (Y' : GlobalTheory.TorRef.GMod Xo' c'), ∃ r, GlobalTheory.LvCover.GoodMap h Y Y' r := by
  intro E _ _ _ H D hD l l' Xo Xo' c c' h Y Y'
  obtain ⟨hs, hG⟩ := GlobalTheory.Models.RankZero.isIso_moduli GlobalTheory.card_torsion_abelianVariety hD Xo
  obtain ⟨hs', hG'⟩ := GlobalTheory.Models.RankZero.isIso_moduli GlobalTheory.card_torsion_abelianVariety hD Xo'
  haveI := c.fin
  let r : Xo.XF c ⟶ Xo'.XF c' := pullback.snd _ _ ≫ spMap (IntermediateField.inclusion h).toRingHom ≫
    inv (pullback.snd Xo'.s (spMap (IntermediateField.inclusion c'.le).toRingHom))
  have hY : IsIso Y.oF.t.G.hom :=
    MorphismProperty.of_isPullback (P := MorphismProperty.isomorphisms _) Y.m0.cart.1 hG
  have hY' : IsIso Y'.oF.t.G.hom :=
    MorphismProperty.of_isPullback (P := MorphismProperty.isomorphisms _) Y'.m0.cart.1 hG'
  obtain ⟨m⟩ := GlobalTheory.Models.RankZero.nonempty_sabMap hY hY' r
  haveI : Surjective (spMap (IntermediateField.inclusion h).toRingHom) :=
    (GlobalTheory.LevelQuotRep.finite_etale_onto_spMap _).2.2
  refine ⟨r, ⟨(GlobalTheory.ShFam.TwMap.reflEquiv _ _ _).symm m⟩, (inferInstance : Surjective r).surj, ?_⟩
  simp only [r, Category.assoc, IsIso.inv_hom_id, Category.comp_id]

end GlobalTheory.LvCover
