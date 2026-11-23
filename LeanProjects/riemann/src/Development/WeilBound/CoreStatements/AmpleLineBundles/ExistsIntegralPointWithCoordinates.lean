import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DvrModelOfNumberFieldPlace
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FiniteTypeOverIntegersModelStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocalRingPointsExistsUniqueStatement
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.SlopeBoundSt
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ArchBetween
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace CoverDenseAlt

namespace PtExt

variable {R L : Type} [CommRing R] [IsDedekindDomain R] [Field L] [Algebra R L] [IsFractionRing R L]

theorem valRing (P : Ideal R) [P.IsPrime] : ValuationRing (Localization.AtPrime P) := by
  by_cases hP : P = ⊥
  · have hF : IsField (Localization.AtPrime P) := by
      rw [IsLocalRing.isField_iff_maximalIdeal_eq, ← Localization.AtPrime.map_eq_maximalIdeal]
      exact (congrArg (Ideal.map _) hP).trans Ideal.map_bot
    let := hF.toField
    exact ValuationRing.of_field _
  · have := IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain R hP (Localization.AtPrime P)
    infer_instance

theorem local_ext {Y : Scheme.{0}} (s : Y ⟶ Spec (CommRingCat.of ℤ)) [IsProper s] (zL : Sp L ⟶ Y) (x : Sp R) :
    ∃ (W : (Sp R).Opens) (h : W.toScheme ⟶ Y), x ∈ W ∧
      ∀ u : Sp L ⟶ W.toScheme, u ≫ W.ι = spMap (algebraMap R L) → u ≫ h = zL := by
  have : x.asIdeal.IsPrime := PrimeSpectrum.isPrime x
  let T := Localization.AtPrime x.asIdeal
  have hu : ∀ y : x.asIdeal.primeCompl, IsUnit (algebraMap R L y) := fun y => by
    refine IsUnit.mk0 _ fun h0 => y.2 ?_
    have : (y : R) = 0 := IsFractionRing.injective R L (by rw [h0, map_zero])
    rw [this]
    exact x.asIdeal.zero_mem
  let : Algebra T L := (IsLocalization.lift (S := T) hu).toAlgebra
  have : IsScalarTower R T L := IsScalarTower.of_algebraMap_eq fun r => (IsLocalization.lift_eq hu r).symm
  have : IsFractionRing T L := IsFractionRing.isFractionRing_of_isDomain_of_isLocalization x.asIdeal.primeCompl T L
  have : ValuationRing T := valRing x.asIdeal
  have hE : ValuativeCriterion.Existence s :=
    (UniversallyClosed.eq_valuativeCriterion ▸ (inferInstance : UniversallyClosed s) :
      (ValuativeCriterion.Existence ⊓ @QuasiCompact) s).1
  obtain ⟨⟨l⟩⟩ := hE
    { R := T, K := L, i₁ := zL, i₂ := specZIsTerminal.from _, commSq := ⟨specZIsTerminal.hom_ext _ _⟩ }
  have hl : spMap (algebraMap T L) ≫ l.l = zL := l.fac_left
  let e := Spec.stalkIso (CommRingCat.of R) x
  obtain ⟨U, hxU, f, h₁, -⟩ := spread_out_of_isGermInjective' (specZIsTerminal.from (Sp R)) s
    (x := x) (Spec.map e.inv ≫ l.l) (specZIsTerminal.hom_ext _ _)
  refine ⟨U, f, hxU, fun u hu' => ?_⟩
  have e1 : u = spMap (algebraMap T L) ≫ Spec.map e.hom ≫ U.fromSpecStalkOfMem x hxU := by
    rw [← cancel_mono U.ι, hu', Category.assoc, Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι,
      Spec.fromSpecStalk_eq, ← Spec.algebraMap_stalkIso_inv, ← Spec.map_comp, ← Spec.map_comp]
    have h2 : (CommRingCat.ofHom (algebraMap R T) ≫ e.inv) ≫ e.hom = CommRingCat.ofHom (algebraMap R T) := by
      rw [Category.assoc, e.inv_hom_id, Category.comp_id]
    refine congrArg Spec.map (Eq.symm ((congrArg (· ≫ CommRingCat.ofHom (algebraMap T L)) h2).trans ?_))
    ext r
    exact (IsScalarTower.algebraMap_apply R T L r).symm
  rw [e1, Category.assoc, Category.assoc, ← h₁, ← Spec.map_comp_assoc e.inv, Iso.inv_hom_id, Spec.map_id,
    Category.id_comp, hl]

theorem ext_dedekind {Y : Scheme.{0}} (s : Y ⟶ Spec (CommRingCat.of ℤ)) [IsProper s] (zL : Sp L ⟶ Y) :
    ∃ z : Sp R ⟶ Y, spMap (algebraMap R L) ≫ z = zL := by
  choose W h hz hξ using fun x : Sp R => local_ext s zL x
  let gp : Sp L ⟶ Sp R := spMap (algebraMap R L)
  have hpt : ∀ y : Sp L, ∀ q : Sp R, gp y ⤳ q := by
    intro y q
    have h0 : (gp y).asIdeal = ⊥ := by
      have : y.asIdeal.IsPrime := PrimeSpectrum.isPrime y
      change Ideal.comap (algebraMap R L) y.asIdeal = ⊥
      rw [(Ideal.eq_bot_of_prime y.asIdeal), Ideal.comap_bot_of_injective _ (IsFractionRing.injective R L)]
    exact (PrimeSpectrum.le_iff_specializes _ _).1 (by
      change (gp y).asIdeal ≤ q.asIdeal
      rw [h0]; exact bot_le)
  have hd : IsDominant gp := ⟨fun q => by
    have := specializes_iff_mem_closure.1 (hpt (IsLocalRing.closedPoint L) q)
    exact closure_mono (Set.singleton_subset_iff.2 (Set.mem_range_self (f := gp) _)) this⟩
  have hx : ∀ z, ∃ x : Sp L ⟶ (W z).toScheme, x ≫ (W z).ι = gp := fun z =>
    ⟨_, IsOpenImmersion.lift_fac (W z).ι gp (by
      rintro _ ⟨y, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact (hpt y z).mem_open (W z).2 (hz z))⟩
  choose x hx using hx
  have hW : TopologicalSpace.IsOpenCover W :=
    top_unique fun z _ => TopologicalSpace.Opens.mem_iSup.2 ⟨z, hz z⟩
  let 𝒰 := (Sp R).openCoverOfIsOpenCover W hW
  have hc : ∀ a b, pullback.fst (W a).ι (W b).ι ≫ h a = pullback.snd (W a).ι (W b).ι ≫ h b := by
    intro a b
    let m : Sp L ⟶ pullback (W a).ι (W b).ι := pullback.lift (x a) (x b) ((hx a).trans (hx b).symm)
    have e : m ≫ pullback.fst _ _ ≫ (W a).ι = gp := by rw [pullback.lift_fst_assoc, hx]
    have : IsDominant (m ≫ pullback.fst _ _ ≫ (W a).ι) := e ▸ hd
    have : IsDominant m := .of_comp_of_isOpenImmersion m (pullback.fst _ _ ≫ (W a).ι)
    have : IsReduced (pullback (W a).ι (W b).ι) := isReduced_of_isOpenImmersion (pullback.fst _ _ ≫ (W a).ι)
    refine ext_of_isDominant_of_isSeparated s (specZIsTerminal.hom_ext _ _) m ?_
    rw [pullback.lift_fst_assoc, pullback.lift_snd_assoc, hξ _ _ (hx a), hξ _ _ (hx b)]
  have he : ∀ a, (W a).ι ≫ 𝒰.glueMorphisms h hc = h a := fun a => 𝒰.ι_glueMorphisms h hc a
  let a := gp (IsLocalRing.closedPoint L)
  refine ⟨𝒰.glueMorphisms h hc, ?_⟩
  change gp ≫ _ = _
  rw [← hx a, Category.assoc, he, hξ _ _ (hx _)]

end PtExt

theorem exists_integral_point_with_coordinates : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (ξ : Sp Ω ⟶ X), CharZero Ω → (∀ q : X, genPt ξ ⤳ q) → CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → ∀ (L : Type) [Field L] [NumberField L], ∀ w ∈ Small.ptsOver L (mCoordIdeal y), ∃ z : Sp (𝓞 L) ⟶ X, CoordsAt ξ y (spMap (algebraMap (𝓞 L) L) ≫ z) w := by
  classical
  intro X Ω _ K _ J _ y ξ _ hall tie L _ _ w hw
  obtain ⟨zL, ⟨-, hz⟩, -⟩ := (GlobalTheory.T.local_ring_points_existsUnique X Ω ξ K J y tie L).1 w
    (fun k => (hw.1 k).imp fun _ h => isUnit_iff_ne_zero.mpr h) hw.2
  obtain ⟨s, h1, h2, -⟩ := GlobalTheory.T.finite_type_over_integers_model X Ω ξ _ _ hall tie
  have := GlobalTheory.CompanionTheory.Ar.Flat.LocModel.isProper_of_coordTie hall tie s
  obtain ⟨z, hz'⟩ := PtExt.ext_dedekind (R := 𝓞 L) s zL
  exact ⟨z, hz' ▸ hz⟩

end CoverDenseAlt
