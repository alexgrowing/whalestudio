import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsNormalSchemeSp
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SplitChartsTorusExtensionOverFieldStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.WeightedProjectiveChartsSplitGenericPointStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsDenseClosedPointsChartSplitting
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AbelianSchemeProperClosureDataBasicProperties
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsSemiAbelianOfSplitAll
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsSplitExtIsGtOfTorusExtension

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

namespace GlobalTheory.ZJ.FibreSplit

theorem exists_residue_factor {K : Type} [Field K] {Z : Scheme.{0}} (s : Sp K ⟶ Z) [SurjectiveOnStalks s]
    (z : Z) (hz : s (IsLocalRing.closedPoint K) = z) :
    ∃ f : Sp (Z.residueField z) ⟶ Sp K, f ≫ s = Z.fromSpecResidueField z := by
  subst hz
  let ρ := Z.descResidueField (Scheme.stalkClosedPointTo s)
  have hs : Function.Surjective (Scheme.stalkClosedPointTo s).hom := by
    unfold Scheme.stalkClosedPointTo
    exact (ConcreteCategory.bijective_of_isIso (stalkClosedPointIso (.of K)).hom).2.comp (s.stalkMap_surjective _)
  have hρ : Function.Surjective ρ.hom := by
    have h := congrArg CommRingCat.Hom.hom (Z.residue_descResidueField (Scheme.stalkClosedPointTo s))
    rw [← h] at hs
    rw [CommRingCat.hom_comp, RingHom.coe_comp] at hs
    exact Function.Surjective.of_comp hs
  have : IsIso ρ := (ConcreteCategory.isIso_iff_bijective ρ).2 ⟨ρ.hom.injective, hρ⟩
  refine ⟨inv (Spec.map ρ), ?_⟩
  rw [IsIso.inv_comp_eq]
  exact (Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K Z s).symm

theorem exists_splitExt_of_split (K : Type) [Field K] (H : Over (Sp K)) [GrpObj H] [IsCommMonObj H] [Smooth H.hom]
    [IsSeparated H.hom] [QuasiCompact H.hom] (C : Charts H.left) (d : ℕ) (c : Fin d → C.Cl) (h : C.Split c) :
    ∃ E : SplitExt (Sp K), E.IsGt H := by
  obtain ⟨hc, i, hT⟩ := h
  obtain ⟨B, gB, q, hB, hq, hf, hs, ha, hk, -⟩ := GlobalTheory.T.splitCharts_torus_extension_over_field K H C d c i hc hT
  exact GlobalTheory.exists_splitExt_isGt_of_torusExtension K H ⟨{
    X := Fin d → ℤ, B := B, grpB := gB, isAbelian := hB, i := i, q := q, i_hom := hT.hom, q_hom := hq,
    q_flat := hf, q_surjective := hs, q_quasiCompact := inferInstance, isKernel := hk }⟩

theorem splitAll_and_isSemiAbelian : ∀ (C : Core) (L : C.Law), C.HasTests → C.HasCharts → letI := L.grp; letI := L.comm; SplitAll C.GG ∧ IsSemiAbelian C.GG := by
  intro C L hT hC
  let := L.grp
  let := L.comm
  obtain ⟨hsep, -, hqc, -⟩ := core_basic C
  have := L.smooth
  have hsm : Smooth C.GG.hom := SmoothOfRelativeDimension.smooth C.g _
  have h : SplitAll C.GG := by
    intro z
    obtain ⟨R, _, _, _, t, _, ht, Ch, d, c, Sg, hd, hS, -⟩ := DenseSplit.exists_dense_splitOn C L hT hC z
    have : Smooth ((Over.pullback t).obj C.GG).hom := inferInstanceAs (Smooth (pullback.snd C.GG.hom t))
    have : IsSeparated ((Over.pullback t).obj C.GG).hom := inferInstanceAs (IsSeparated (pullback.snd C.GG.hom t))
    have : QuasiCompact ((Over.pullback t).obj C.GG).hom := inferInstanceAs (QuasiCompact (pullback.snd C.GG.hom t))
    have : Smooth ((Over.pullback (Out.jK R)).obj ((Over.pullback t).obj C.GG)).hom :=
      inferInstanceAs (Smooth (pullback.snd ((Over.pullback t).obj C.GG).hom _))
    have : IsSeparated ((Over.pullback (Out.jK R)).obj ((Over.pullback t).obj C.GG)).hom :=
      inferInstanceAs (IsSeparated (pullback.snd ((Over.pullback t).obj C.GG).hom _))
    have : QuasiCompact ((Over.pullback (Out.jK R)).obj ((Over.pullback t).obj C.GG)).hom :=
      inferInstanceAs (QuasiCompact (pullback.snd ((Over.pullback t).obj C.GG).hom _))
    have : IsAffineHom (pullback.fst ((Over.pullback t).obj C.GG).hom (Out.jK R)) :=
      isAffineHom_isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback _ _).flip inferInstance
    obtain ⟨E, hE⟩ := exists_splitExt_of_split (FractionRing R) _ _ d _
      (GlobalTheory.T.weightedProjectiveCharts_split_generic_point R ((Over.pullback t).obj C.GG) Ch d c Sg hd hS)
    have : IsPreimmersion (Out.jK R) := IsPreimmersion.of_isLocalization (nonZeroDivisors R)
    obtain ⟨f, hf⟩ := exists_residue_factor (Out.jK R ≫ t) z (by
      rw [← ht]
      refine (Scheme.Hom.comp_apply (Out.jK R) t _).trans (congrArg t (PrimeSpectrum.ext ?_))
      change Ideal.comap (algebraMap R (FractionRing R)) (IsLocalRing.maximalIdeal _) = ⊥
      rw [IsLocalRing.maximalIdeal_eq_bot, Ideal.comap_bot_of_injective _ (IsFractionRing.injective R _)])
    have : IsMonHom (pullCompIso (Out.jK R) t C.GG).symm.hom :=
      inferInstanceAs (IsMonHom (pullCompIso (Out.jK R) t C.GG).inv)
    obtain ⟨D⟩ := isGt_of_iso (pullCompIso (Out.jK R) t C.GG).symm hE
    have : IsMonHom (pullCompIso f (Out.jK R ≫ t) C.GG).symm.hom :=
      inferInstanceAs (IsMonHom (pullCompIso f (Out.jK R ≫ t) C.GG).inv)
    have key : ∀ s : Sp (C.Z.residueField z) ⟶ C.Z, f ≫ Out.jK R ≫ t = s →
        ∃ E : SplitExt (Sp (C.Z.residueField z)), E.IsGt ((Over.pullback s).obj C.GG) := by
      rintro _ rfl
      exact ⟨_, isGt_of_iso (pullCompIso f (Out.jK R ≫ t) C.GG).symm (GtBaseChange.isGt_extBC f E _ D)⟩
    exact key _ hf
  exact ⟨h, (isSemiAbelian_of_splitAll C.Z C.GG h).1⟩

end GlobalTheory.ZJ.FibreSplit
