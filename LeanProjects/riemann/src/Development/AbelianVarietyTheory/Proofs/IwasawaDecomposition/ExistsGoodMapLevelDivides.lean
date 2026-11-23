import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalCoeffF
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ModuliSchemeLevelMapsHeckePoints
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.LvCover

theorem fieldMap_isPullback {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
    {l : Level H} (Xo : Moduli D l) {c c' : Coeff l} (h : c.F ≤ c'.F) :
    IsPullback (fieldMap Xo h) (pullback.snd _ _) (pullback.snd _ _)
      (spMap (IntermediateField.inclusion h).toRingHom) := by
  refine IsPullback.of_right (h₁₂ := pullback.fst _ _) (v₁₃ := Xo.s)
    (h₂₂ := spMap (IntermediateField.inclusion c.le).toRingHom) ?_ ?_ (IsPullback.of_hasPullback _ _)
  · have e : fieldMap Xo h ≫ pullback.fst _ _ = pullback.fst _ _ := pullback.lift_fst _ _ _
    rw [e, GlobalTheory.IndefiniteRowSideFullHecke.RelativeGroupHatForm.spMap_inclusion_comp]
    exact IsPullback.of_hasPullback _ _
  · exact pullback.lift_snd _ _ _

end GlobalTheory.LvCover

namespace GlobalTheory.LvCover

theorem fieldMap_surjective {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
    {l : Level H} (Xo : Moduli D l) {c c' : Coeff l} (h : c.F ≤ c'.F) : Surjective (fieldMap Xo h) := by
  haveI := c'.fin
  haveI : Surjective (spMap (IntermediateField.inclusion h).toRingHom) :=
    (GlobalTheory.LevelQuotRep.finite_etale_onto_spMap (IntermediateField.inclusion h).toRingHom).2.2
  exact MorphismProperty.of_isPullback (P := @Surjective) (fieldMap_isPullback Xo h).flip inferInstance

theorem exists_goodMap_of_dvd : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), 1 ≤ D.p + D.q →
    ∀ (l l' : Level H), l'.Dvd l → ∀ (Xo : Moduli D l) (Xo' : Moduli D l') (c : Coeff l) (c' : Coeff l') (h : c'.F ≤ c.F)
      (Y : GlobalTheory.TorRef.GMod Xo c) (Y' : GlobalTheory.TorRef.GMod Xo' c'), ∃ r, GlobalTheory.LvCover.GoodMap h Y Y' r := by
  intro E _ _ _ H D hpq l l' hd Xo Xo' c c' h Y Y'
  obtain ⟨-, hN⟩ := GlobalTheory.moduliScheme_levelMaps_heckePoints
  obtain ⟨r₀, -, m, -, -, -, -, -, hF⟩ := (hN E H D hpq).1 l' l Xo' Xo hd
  obtain ⟨rF, h₁, h₂, -, -, hsF, -⟩ := hF (GlobalTheory.IndefiniteRowSideFullHecke.RelativeGroupHatForm.lowerCoeff hd c) c rfl
  let c'' := GlobalTheory.IndefiniteRowSideFullHecke.RelativeGroupHatForm.lowerCoeff hd c
  have h' : c'.F ≤ c''.F := h
  refine ⟨rF ≫ fieldMap Xo' h', ⟨?_, ?_, ?_⟩⟩
  · have hfst : (rF ≫ fieldMap Xo' h') ≫ pullback.fst _ _ = pullback.fst _ _ ≫ r₀ := by
      rw [Category.assoc, show fieldMap Xo' h' ≫ pullback.fst _ _ = pullback.fst _ _ from pullback.lift_fst _ _ _, h₁]
    obtain ⟨n, -⟩ := GlobalTheory.LevelCover.sab_comp Y.m0.toSABMap m rfl
    obtain ⟨n', -⟩ := GlobalTheory.LevelCover.sab_cancel Y'.m0.toSABMap n _ hfst
    exact ⟨(GlobalTheory.ShFam.TwMap.reflEquiv _ _ _).symm n'⟩
  · haveI := fieldMap_surjective Xo' h'
    exact (rF ≫ fieldMap Xo' h').surjective
  · rw [Category.assoc, show fieldMap Xo' h' ≫ pullback.snd _ _ = pullback.snd _ _ ≫ _ from pullback.lift_snd _ _ _,
      ← Category.assoc, h₂, Category.assoc, GlobalTheory.IndefiniteRowSideFullHecke.RelativeGroupHatForm.spMap_inclusion_comp]

end GlobalTheory.LvCover
