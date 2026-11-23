import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.VertCmp
import Development.AutomorphicArithmetic.LocalEmbeddings.ConsMatch
import Development.AutomorphicArithmetic.LocalEmbeddings.ConsAgree
import Development.AutomorphicArithmetic.DivisorFrames.NonemptyLevelStructure
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSysGlobalModels
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalSystemModelMap
open CategoryTheory Limits AlgebraicGeometry IsLocalRing NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.Toroidal

set_option maxHeartbeats 1600000 in
theorem UpperTheory.exists_level_abelian_maps :
    ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p} {O : Type} [CommRing O] {β : O →+* i₀.c.F} (Z : LocM.Mdl Y i₀) (T : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model (Xo i₀.l) i₀.c β), 1 ≤ Dw.p + Dw.q → ∃ L : GlobalTheory.ConsGeo.Lev Z T, ∀ (τ : (Y Z.i).X ⟶ (Y i₀).X) (mu : SABMap (Y Z.i).t (Y i₀).t τ), IsTrans i₀ Z.i τ mu → (Y Z.i).j ≫ τ = L.r ≫ (Y i₀).j ∧ ∃ ν₂ : SABMap (Y Z.i).oF.t (Y i₀).oF.t L.r, ν₂.φ ≫ (Y i₀).m.φ = (Y Z.i).m.φ ≫ mu.φ ∧ ν₂.φ ≫ (Y i₀).m0.toSABMap.φ = L.ν.φ ≫ T.m0.toSABMap.φ := by
  intro E _ _ _ H Dw Xo p W Y i₀ O _ β Z T hpq
  obtain ⟨L₁, L₂, L₃, -⟩ := GlobalTheory.allSixLaws
  obtain ⟨π, hπ, hpb, -⟩ :=
    (GlobalTheory.LevelCompare.levelMaps_iff hpq).1 (GlobalTheory.moduliScheme_levelMaps_heckePoints.2 E H Dw hpq).1 _ _ Z.dvd
      (Xo i₀.l) (Xo Z.i.l)
  have w : (pullback.fst _ _ ≫ π : (Xo Z.i.l).XF Z.i.c ⟶ _) ≫ (Xo i₀.l).s =
      (pullback.snd _ _ ≫ spMap (ConsGeo.incl Z)) ≫ spMap (IntermediateField.inclusion i₀.c.le).toRingHom := by
    rw [Category.assoc, hπ, ← Category.assoc, pullback.condition, Category.assoc, Category.assoc,
      GlobalTheory.IndefiniteRowSideFullHecke.RelativeGroupHatForm.spMap_inclusion_comp]
    exact congrArg _ (GlobalTheory.IndefiniteRowSideFullHecke.RelativeGroupHatForm.spMap_inclusion_comp _ _).symm
  obtain ⟨r, hr, hr₂⟩ : ∃ r : (Xo Z.i.l).XF Z.i.c ⟶ (Xo i₀.l).XF i₀.c,
      r ≫ pullback.fst _ _ = pullback.fst _ _ ≫ π ∧
      r ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap (ConsGeo.incl Z) :=
    ⟨pullback.lift _ _ w, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  obtain ⟨m, hm⟩ := hpb
  obtain ⟨n, hn⟩ := LevelCover.sab_comp (Y Z.i).m0.toSABMap m hr.symm
  obtain ⟨ν, hν⟩ := LevelCover.sab_cancel T.m0.toSABMap n r rfl
  refine ⟨⟨r, ν, hr₂, π, hπ, ⟨m, hm⟩, hr⟩, fun τ mu ⟨b, π', r', hb, h₁, h₂, _, hj, hη, hηA⟩ => ?_⟩
  obtain ⟨n', hn'⟩ := LevelCover.sab_comp (Y Z.i).m mu rfl
  obtain ⟨ν', hν'⟩ := LevelCover.sab_cancel (Y i₀).m n' r' hj.symm
  obtain ⟨k, hk⟩ := LevelCover.sab_comp ν' (Y i₀).m0.toSABMap rfl
  have hr' : r' ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap (ConsGeo.incl Z) := by
    have := mono_spMap_subtype (i₀.c.V W)
    have hσ : (ConsGeo.incl Z).comp (i₀.c.V W).subtype = (Z.i.c.V W).subtype.comp b :=
      RingHom.ext fun x => Subtype.ext (hb x).symm
    have e : τ ≫ (Y i₀).s = (Y Z.i).s ≫ spMap b := by
      rw [← h₁, ← h₂, Category.assoc, Category.assoc, pullback.condition]
    rw [← cancel_mono (spMap (i₀.c.V W).subtype), Category.assoc, Category.assoc, ← ModelRelProbe.j_over,
      ← Category.assoc, ← hj, Category.assoc, e, ← Category.assoc, ModelRelProbe.j_over, Category.assoc,
      ModelRelProbe.spMap_comp, ModelRelProbe.spMap_comp, hσ]
  have hl' : GlobalTheory.Models.LevComp (Y Z.i).oF (Y i₀).oF r' ν' :=
    ⟨fun a => LevelCover.sec_cancel ν' (Y i₀).m _ _ (by rw [hν', hn']; exact hη a),
      fun a => LevelCover.sec_cancel ν' (Y i₀).m _ _ (by rw [hν', hn']; exact hηA a)⟩
  have hla : GlobalTheory.Models.LevComp (Y Z.i).oF (Xo i₀.l).univ _ k := by
    refine ⟨fun x => ?_, fun x => ?_⟩
    · rw [hk, ← Category.assoc, hl'.1, Category.assoc, Category.assoc]
      exact congrArg _ ((Y i₀).m0.eta x)
    · rw [hk, ← Category.assoc, hl'.2, Category.assoc, Category.assoc]
      exact congrArg _ ((Y i₀).m0.etaA x)
  have hlb : GlobalTheory.Models.LevComp (Y Z.i).oF (Xo i₀.l).univ _ n := by
    refine ⟨fun x => ?_, fun x => ?_⟩
    · rw [hn, ← Category.assoc, LevelCover.sec_pow _ _ _ ((Y Z.i).m0.eta x), Category.assoc, hm.1, hr,
        Category.assoc]
    · rw [hn, ← Category.assoc, LevelCover.sec_pow _ _ _ ((Y Z.i).m0.etaA x), Category.assoc, hm.2, hr,
        Category.assoc]
  have hred : IsReduced ((Xo Z.i.l).XF Z.i.c) := by
    have := (Xo Z.i.l).smooth
    have : Smooth (Xo Z.i.l).s := SmoothOfRelativeDimension.smooth Dw.dim _
    exact (GlobalTheory.isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field Z.i.c.F _ (pullback.snd _ _)
      inferInstance).1
  obtain ⟨e₁, e₂⟩ := GlobalTheory.LevUniq.map_to_univ_unique L₁ L₂ L₃ E H Dw i₀.l Z.i.l (Xo i₀.l) _ _ _ _ (Y Z.i).oF _ _ k n
    hred (by rw [Category.assoc, Category.assoc, pullback.condition, reassoc_of% hr', reassoc_of% hr₂]) hla hlb
  obtain rfl : r' = r := pullback.hom_ext e₁ (hr'.trans hr₂.symm)
  exact ⟨hj, ν', hν'.trans hn', hk.symm.trans (e₂.trans hν.symm)⟩
