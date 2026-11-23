import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.ConsAgree
import Development.AutomorphicArithmetic.LocalEmbeddings.ConsMatch
import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CardLiesOverEqIndex
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ConsGeo

theorem UpperTheory.nonempty_level_structure :
    ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p} {O : Type} [CommRing O] {β : O →+* i₀.c.F} (Z : LocM.Mdl Y i₀) (T : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model (Xo i₀.l) i₀.c β), 1 ≤ Dw.p + Dw.q → Nonempty (Lev Z T) := by
  intro E _ _ _ H Dw Xo p W Y i₀ O _ β Z T hpq
  obtain ⟨π, hπ, hpb, -⟩ :=
    (GlobalTheory.LevelCompare.levelMaps_iff hpq).1 (GlobalTheory.moduliScheme_levelMaps_heckePoints.2 E H Dw hpq).1 _ _ Z.dvd
      (Xo i₀.l) (Xo Z.i.l)
  have w : (pullback.fst _ _ ≫ π : (Xo Z.i.l).XF Z.i.c ⟶ _) ≫ (Xo i₀.l).s =
      (pullback.snd _ _ ≫ spMap (incl Z)) ≫ spMap (IntermediateField.inclusion i₀.c.le).toRingHom := by
    rw [Category.assoc, hπ, ← Category.assoc, pullback.condition, Category.assoc, Category.assoc,
      GlobalTheory.IndefiniteRowSideFullHecke.RelativeGroupHatForm.spMap_inclusion_comp]
    exact congrArg _ (GlobalTheory.IndefiniteRowSideFullHecke.RelativeGroupHatForm.spMap_inclusion_comp _ _).symm
  let r : (Xo Z.i.l).XF Z.i.c ⟶ (Xo i₀.l).XF i₀.c := pullback.lift _ _ w
  have hr : r ≫ pullback.fst _ _ = pullback.fst _ _ ≫ π := pullback.lift_fst _ _ _
  obtain ⟨m, hm⟩ := hpb
  obtain ⟨n, -⟩ := GlobalTheory.ObjMaps.exists_sab_comp m (Y Z.i).m0.toSABMap
  obtain ⟨ν, -⟩ := GlobalTheory.ObjMaps.exists_sab_cancel (g := r) T.m0.toSABMap (hr.symm ▸ n)
  exact ⟨⟨r, ν, pullback.lift_snd _ _ _, π, hπ, ⟨m, hm⟩, hr⟩⟩
