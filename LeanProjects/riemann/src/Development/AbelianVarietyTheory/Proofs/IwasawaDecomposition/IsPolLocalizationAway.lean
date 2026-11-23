import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsChartOf
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GlueSchemesOverOpensAlongCocycle
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSemiAbelianTripleGlueCommonGenericPart
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SemiAbelianHomExtendsUniquelyOverDvr
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabDescentOfFieldExtension
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsAbelianTripleGlueTwoOpenImmersions
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsModelBaseChangeOverring
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabCancel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PhiDivisorArcBlowup
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationOpenImmersion
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.CoeNonzeroLocusCanonicalEqComplRange
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TorRef

namespace GlobalTheory.PolRestr

theorem exists_isPol_away : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l}
    {c : Coeff l} {R : Type} [CommRing R] {ω : R →+* c.F} (C : Model Xo c ω) (BD : EffCartierData C.X) (φ : InvFun (𝓞 E))
    (m : ℕ) (x : R) (ω' : Localization.Away x →+* c.F), Models.IsDedFrac ω → Models.IsDedFrac ω' →
    ω'.comp (algebraMap R (Localization.Away x)) = ω → IsPol φ m C BD →
    ∃ (C' : Model Xo c ω') (BD' : EffCartierData C'.X) (v : C'.X ⟶ C.X),
      IsPullback v C'.s C.s (spMap (algebraMap R (Localization.Away x))) ∧ C'.j ≫ v = C.j ∧ IsPol φ m C' BD' ∧
        BD'.idealSheaf = BD.idealSheaf.comap v := by
  intro E _ _ _ H D l Xo c R _ ω C BD φ m x ω' _ _ hb hpol
  set b := algebraMap R (Localization.Away x) with hbdef
  have : IsOpenImmersion (spMap b) := IsOpenImmersion.of_isLocalization x
  have hsp : spMap ω' ≫ spMap b = spMap ω := by
    rw [← hb, spMap, spMap, spMap, ← Spec.map_comp]
    rfl
  have hp : IsPullback (pullback.fst (pullback.snd C.s (spMap b)) (spMap ω') ≫ pullback.fst C.s (spMap b))
      (pullback.snd (pullback.snd C.s (spMap b)) (spMap ω')) C.s (spMap ω) := by
    rw [← hsp]
    exact (IsPullback.of_hasPullback _ _).paste_horiz (IsPullback.of_hasPullback _ _)
  have hj : ((C.jQ ≫ hp.isoPullback.inv) ≫ pullback.fst (pullback.snd C.s (spMap b)) (spMap ω')) ≫
      pullback.fst C.s (spMap b) = C.jQ ≫ pullback.fst _ _ := by
    simp only [Category.assoc, hp.isoPullback_inv_fst]
  obtain ⟨t', ⟨mu⟩⟩ : ∃ t' : SAB H (pullback C.s (spMap b)), Nonempty (SABMap t' C.t (pullback.fst C.s (spMap b))) := by
    obtain ⟨_, _, _, _, _, m, -⟩ := sabPull Out.CubePf.cubePull (pullback.fst C.s (spMap b)) C.t
    exact ⟨_, ⟨m⟩⟩
  obtain ⟨m', -⟩ : ∃ m' : SABMap C.oF.t t' ((C.jQ ≫ hp.isoPullback.inv) ≫
      pullback.fst (pullback.snd C.s (spMap b)) (spMap ω')), C.m.φ = m'.φ ≫ mu.φ := by
    have aux : ∀ (g : Xo.XF c ⟶ pullback C.s (spMap b)) (e : Xo.XF c ⟶ C.X) (n : SABMap C.oF.t C.t e),
        g ≫ pullback.fst C.s (spMap b) = e → ∃ m' : SABMap C.oF.t t' g, n.φ = m'.φ ≫ mu.φ := by
      rintro g e n rfl
      exact ObjMaps.exists_sab_cancel mu n
    exact aux _ _ C.m hj
  have := C.flat
  have := C.jQ_open
  have hr : Set.range (C.jQ ≫ hp.isoPullback.inv) = hp.isoPullback.hom ⁻¹' Set.range C.jQ := by
    ext y
    constructor
    · rintro ⟨u, rfl⟩
      exact ⟨u, by simp⟩
    · rintro ⟨u, hu⟩
      exact ⟨u, by simp [hu]⟩
  let C' : Model Xo c ω' :=
    { X := pullback C.s (spMap b)
      s := pullback.snd _ _
      normal := isNormalScheme_of_flat_of_surjectiveOnStalks (pullback.fst C.s (spMap b)) C.normal
      proj := ProjSpace.isProjOver_pullback_snd b C.proj
      flat := inferInstance
      jQ := C.jQ ≫ hp.isoPullback.inv
      jQ_over := by rw [Category.assoc, hp.isoPullback_inv_snd, C.jQ_over]
      jQ_open := inferInstance
      jQ_dense := by
        rw [hr]
        exact C.jQ_dense.preimage hp.isoPullback.hom.isOpenEmbedding.isOpenMap
      t := t'
      oF := C.oF
      m0 := C.m0
      m := m'
      ab_gen := by
        rw [hr, ← C.ab_gen]
        ext y
        simp only [Set.mem_preimage]
        rw [← abLocus_pullback abLocusOne C.t.semi mu.cart.1, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply,
          hp.isoPullback_hom_fst] }
  have hv : IsOpenImmersion (pullback.fst C.s (spMap b)) := inferInstance
  have hjv : C'.j ≫ pullback.fst C.s (spMap b) = C.j := hj
  have : IsAffineHom (pullback.fst C.s (spMap b)) := MorphismProperty.of_isPullback (P := @IsAffineHom) (IsPullback.of_hasPullback C.s (spMap b)).flip inferInstance
  have hreg : BD.KeepsRegular (pullback.fst C.s (spMap b)) := BD.keepsRegular_of_flat _
  have hI := BD.idealSheaf_pull (pullback.fst C.s (spMap b)) hreg
  refine ⟨C', BD.pull _ hreg, pullback.fst C.s (spMap b), IsPullback.of_hasPullback _ _, hjv, ⟨?_, ?_⟩, hI⟩
  · intro W _ _ _ hW ϖ hϖ χ t n P hrng be hbe hmono
    obtain ⟨n', -⟩ := ObjMaps.exists_sab_comp mu n
    have hrng' : Set.range (Out.jK W ≫ χ ≫ pullback.fst C.s (spMap b)) ⊆ Set.range C.j := by
      rintro _ ⟨a, rfl⟩
      obtain ⟨y, hy⟩ := hrng ⟨a, rfl⟩
      refine ⟨y, ?_⟩
      rw [← hjv, Scheme.Hom.comp_apply, hy, ← Scheme.Hom.comp_apply, Category.assoc]
    obtain ⟨k, hk, hid⟩ := hpol.1 W hW ϖ hϖ (χ ≫ pullback.fst C.s (spMap b)) t n' P hrng' be hbe hmono
    refine ⟨k, hk, ?_⟩
    rw [hI, idlAlong_comap]
    exact hid
  · exact (PolOpen.isAmpleLB_polOf_iff_pull C C' _ BD (BD.pull _ hreg) m hv ⟨mu⟩ hI.symm).2
      (hpol.2.pull_of_isAffineHom _)

end GlobalTheory.PolRestr
