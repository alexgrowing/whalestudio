import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LevelSectionsExactKernelLocusOpen
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsGenericFlag
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.IsQProjOverOfIsProjOver
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsIsoStalkMapOfFlatOfSurjectiveOnStalks
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.GenRes

theorem genericFibre_closed {O K : Type} [CommRing O] [Field K] (β : O →+* K)
    (hinj : Function.Injective β) (hfr : ∀ x : K, ∃ a b : O, β b ≠ 0 ∧ x * β b = β a)
    (P : Scheme.{0}) (s : P ⟶ Sp O) (hs : IsProjOver s) (hn : IsNormalScheme P) :
    IsReduced (pullback s (spMap β)) ∧ IsLocallyNoetherian (pullback s (spMap β)) ∧
      ∃ (M : ℕ) (i : pullback s (spMap β) ⟶ PSpace K M), IsClosedImmersion i ∧
        i ≫ PSpace.str K M = pullback.snd s (spMap β) := by
  letI : Algebra O K := β.toAlgebra
  haveI : IsDomain O := hinj.isDomain β
  haveI : IsFractionRing O K :=
    { map_units := fun y => by
        have hy : β y.1 ≠ 0 := fun h => nonZeroDivisors.ne_zero y.2 (hinj (by rw [h, map_zero]))
        exact (IsUnit.mk0 _ hy)
      surj := fun z => by
        obtain ⟨a, b, hb, h⟩ := hfr z
        have hb0 : b ≠ 0 := fun h0 => hb (by rw [h0, map_zero])
        exact ⟨⟨a, ⟨b, mem_nonZeroDivisors_of_ne_zero hb0⟩⟩, h⟩
      exists_of_eq := fun {x y} h => ⟨1, by rw [hinj h]⟩ }
  have hp : IsProjOver (pullback.snd s (spMap β)) := GlobalTheory.ProjSpace.isProjOver_pullback_snd _ hs
  have hb : IsPreimmersion (spMap β) :=
    IsPreimmersion.of_isLocalization (R := CommRingCat.of O) (S := K) (nonZeroDivisors O)
  have hbf : Flat (spMap β) := by
    rw [Flat.SpecMap_iff]
    exact RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat K (nonZeroDivisors O))
  have h1 : IsPreimmersion (pullback.fst s (spMap β)) :=
    MorphismProperty.of_isPullback (P := @IsPreimmersion) (IsPullback.of_hasPullback _ _).flip hb
  have hiso := GlobalTheory.isIso_stalkMap_of_flat_of_surjectiveOnStalks (pullback.fst s (spMap β))
  have := GlobalTheory.SchemeWords.isProper_of_isProjOver hp
  refine ⟨?_, LocallyOfFiniteType.isLocallyNoetherian (pullback.snd s (spMap β)), hp⟩
  have : ∀ x, _root_.IsReduced ((pullback s (spMap β)).presheaf.stalk x) := fun x => by
    have := hiso x
    have i := (asIso ((pullback.fst s (spMap β)).stalkMap x)).commRingCatIsoToRingEquiv
    obtain ⟨_, _⟩ := hn (pullback.fst s (spMap β) x)
    exact isReduced_of_injective i.symm i.symm.injective
  exact isReduced_of_isReduced_stalk _

theorem isProper_of_closed {K : Type} [Field K] {M r : ℕ} {X X' : Scheme.{0}} (i : X ⟶ PSpace K M)
    [IsClosedImmersion i] (j : X' ⟶ pullback (PSpace.str K M) (PSpace.str K r)) [IsClosedImmersion j]
    (f : X' ⟶ X) (h : f ≫ i = j ≫ pullback.fst _ _) : IsProper f ∧ IsProper (f ≫ i ≫ PSpace.str K M) := by
  have := isProper_str K M
  have := isProper_str K r
  have hfst : IsProper (pullback.fst (PSpace.str K M) (PSpace.str K r)) :=
    MorphismProperty.of_isPullback (P := @IsProper) (IsPullback.of_hasPullback _ _).flip inferInstance
  have hfi : IsProper (f ≫ i) := by rw [h]; infer_instance
  have hf : IsProper f := IsProper.of_comp f i
  refine ⟨hf, ?_⟩
  rw [← Category.assoc]
  infer_instance

end GlobalTheory.CompanionTheory.Ar.Flat.GenRes

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem exists_resolution_genericFibre : Geo.ResK.ResKStatement → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β), (Function.Injective β ∧ IsNoetherianRing O ∧ ∀ x : c.F, ∃ a b : O, β b ≠ 0 ∧ x * β b = β a) → IsLocallyNoetherian (pullback Y.s (spMap β)) ∧ ∃ (X' : Scheme.{0}) (f : X' ⟶ pullback Y.s (spMap β)) (d : ℕ) (W' : X'.Opens) (jW : W'.toScheme ⟶ Xo.XF c), IsIso jW ∧ jW ≫ Y.jQ = W'.ι ≫ f ∧ IsProper f ∧ IsProper (f ≫ pullback.snd Y.s (spMap β)) ∧ SmoothOfRelativeDimension d (f ≫ pullback.snd Y.s (spMap β)) ∧ Geo.ResK.HasSncCoords (f ≫ pullback.snd Y.s (spMap β)) d (W' : Set X')ᶜ := by
  rintro hRes E _ _ _ H D l Xo c O _ β Y ⟨hinj, -, hfr⟩
  obtain ⟨hred, hln, M, i, hi, his⟩ := GenRes.genericFibre_closed β hinj hfr Y.X Y.s Y.proj Y.normal
  refine ⟨hln, ?_⟩
  have := Y.jQ_open
  let U : (pullback Y.s (spMap β)).Opens := Y.jQ.opensRange
  have hd : Dense (U : Set (pullback Y.s (spMap β) : Scheme.{0})) := by
    have : (U : Set (pullback Y.s (spMap β) : Scheme.{0})) = Set.range Y.jQ := Scheme.Hom.coe_opensRange _
    rw [this]; exact Y.jQ_dense
  have hιe : Y.jQ.isoOpensRange.inv ≫ Y.jQ = U.ι := by
    rw [Iso.inv_comp_eq, Scheme.Hom.isoOpensRange_hom_ι]
  have hXF : SmoothOfRelativeDimension D.dim
      (pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)) := by
    have := Xo.smooth
    have := smoothOfRelativeDimension_isStableUnderBaseChange D.dim
    exact MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension D.dim)
      (IsPullback.of_hasPullback _ _) Xo.smooth
  have hU : SmoothOfRelativeDimension D.dim (U.ι ≫ pullback.snd Y.s (spMap β)) := by
    rw [← hιe, Category.assoc, Y.jQ_over]
    have := smoothOfRelativeDimension_isStableUnderBaseChange D.dim
    exact MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension D.dim)
      (IsPullback.of_horiz_isIso ⟨by simp⟩ :
        IsPullback Y.jQ.isoOpensRange.inv (Y.jQ.isoOpensRange.inv ≫ pullback.snd _ _) (pullback.snd _ _) (𝟙 _)) hXF
  have hin : Geo.ResK.IsResInput M i U D.dim := ⟨hi, hred, hd, by rw [his]; exact hU⟩
  haveI : CharZero c.F := inferInstance
  obtain ⟨r, X', j, f, hj, hfj, hsm, hiso, hdense, hsnc⟩ := hRes c.F M D.dim _ i U hin
  obtain ⟨hp1, hp2⟩ := GenRes.isProper_of_closed i j f hfj
  rw [his] at hp2 hsm hsnc
  refine ⟨X', f, D.dim, f ⁻¹ᵁ U, (f ∣_ U) ≫ Y.jQ.isoOpensRange.inv, inferInstance, ?_, hp1, hp2, hsm, hsnc⟩
  rw [Category.assoc, hιe, morphismRestrict_ι]

end GlobalTheory.CompanionTheory.Ar.Flat
