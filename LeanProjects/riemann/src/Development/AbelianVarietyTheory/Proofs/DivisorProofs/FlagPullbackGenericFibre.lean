import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairBaseIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleExistsArithmeticVarietyAltAlt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalOfGenericFibrePullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalDegreePullbackFinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DimensionOfDominantFlatCover
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIntegralClosureOfEssFiniteTypeField
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoNormalizationPullbackOfToIntegralClosure
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompleteCurveArithModelClosure
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ArLieBase
open GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TwoLat GlobalTheory.FlagCov
open scoped Classical
open CategoryTheory.Limits

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagExtend

theorem eq_zero_of_pullback_map {X G : Scheme.{0}} (j : G ⟶ X) [QuasiCompact j] [IsSchemeTheoreticallyDominant j]
    {A B : X.Modules} {r : ℕ} (hB : IsVB B r) (φ : A ⟶ B) (h : (Scheme.Modules.pullback j).map φ = 0) : φ = 0 := by
  have := hB.isQuasicoherent
  refine Scheme.Modules.hom_ext _ _ fun W => ?_
  ext s
  choose U e _ hx hle he using fun x : W => hB.exists_affine x.2
  refine Twist.sec_ext_of_cover U hle (fun x hxW => TopologicalSpace.Opens.mem_iSup.2 ⟨⟨x, hxW⟩, hx _⟩) fun x => ?_
  have h0 : QCoh.pullbackSections j B (le_refl (j ⁻¹ᵁ U x)) (φ.app (U x) (Twist.resM A (hle x) s)) = 0 := by
    rw [← QCoh.pullback_map_app_pullbackSections, h]
    rfl
  have h1 : φ.app (U x) (Twist.resM A (hle x) s) = 0 := by
    refine ((he x).basis le_rfl).repr.injective (Finsupp.ext fun i => ?_)
    have h2 := (he x).pullback_basis_repr j le_rfl (le_refl (j ⁻¹ᵁ U x)) (φ.app (U x) (Twist.resM A (hle x) s)) i
    rw [h0, map_zero, Finsupp.zero_apply, ← Scheme.Hom.app_eq_appLE] at h2
    rw [map_zero, Finsupp.zero_apply]
    exact j.app_injective (U x) (h2.symm.trans (map_zero _).symm)
  exact ((Twist.app_resM φ (hle x) s).symm.trans h1).trans (map_zero _).symm

theorem compat_of_pull {X G : Scheme.{0}} (j : G ⟶ X) [QuasiCompact j] [IsSchemeTheoreticallyDominant j]
    {E E' : X.Modules} {r : ℕ} {u : E ⟶ E'} {a : Vert.Flag E r} {b : Vert.Flag E' r}
    (h : Compat ((Scheme.Modules.pullback j).map u) (a.pull j) (b.pull j)) : Compat u a b := fun i => by
  obtain ⟨t, ht⟩ : ∃ t : (Scheme.Modules.pullback j).obj (a.F i) ⟶ (Scheme.Modules.pullback j).obj (b.F i),
      t ≫ (Scheme.Modules.pullback j).map (b.ι i) =
        (Scheme.Modules.pullback j).map (a.ι i) ≫ (Scheme.Modules.pullback j).map u := h i
  have h0 : (a.ι i ≫ u) ≫ cokernel.π (b.ι i) = 0 := by
    refine eq_zero_of_pullback_map j (b.isVB_cokernel i) _ ?_
    rw [Functor.map_comp, Functor.map_comp, ← ht, Category.assoc, ← Functor.map_comp, cokernel.condition,
      Functor.map_zero, comp_zero]
  exact ⟨Abelian.monoLift _ _ h0, Abelian.monoLift_comp _ _ _⟩

theorem exists_fac_comp {G X P Y : Scheme.{0}} (j : G ⟶ X) (ν : X ⟶ P) (π : P ⟶ Y) {A E : Y.Modules} (c : A ⟶ E)
    {B : P.Modules} (b : B ⟶ (Scheme.Modules.pullback π).obj E)
    (t : (Scheme.Modules.pullback ((j ≫ ν) ≫ π)).obj A ⟶ (Scheme.Modules.pullback (j ≫ ν)).obj B)
    (ht : t ≫ (Scheme.Modules.pullback (j ≫ ν)).map b ≫ (Scheme.Modules.pullbackComp (j ≫ ν) π).hom.app E =
      (Scheme.Modules.pullback ((j ≫ ν) ≫ π)).map c) :
    ∃ t' : (Scheme.Modules.pullback j).obj ((Scheme.Modules.pullback (ν ≫ π)).obj A) ⟶
        (Scheme.Modules.pullback j).obj ((Scheme.Modules.pullback ν).obj B),
      t' ≫ (Scheme.Modules.pullback j).map ((Scheme.Modules.pullback ν).map b ≫
          (Scheme.Modules.pullbackComp ν π).hom.app E) =
        (Scheme.Modules.pullback j).map ((Scheme.Modules.pullback (ν ≫ π)).map c) := by
  let ε : Scheme.Modules.pullback (ν ≫ π) ⋙ Scheme.Modules.pullback j ≅ Scheme.Modules.pullback ((j ≫ ν) ≫ π) :=
    Scheme.Modules.pullbackComp j (ν ≫ π) ≪≫ Scheme.Modules.pullbackCongr (Category.assoc j ν π).symm
  have key : (Scheme.Modules.pullbackComp j ν).inv.app ((Scheme.Modules.pullback π).obj E) ≫
      (Scheme.Modules.pullback j).map ((Scheme.Modules.pullbackComp ν π).hom.app E) ≫ ε.hom.app E =
      (Scheme.Modules.pullbackComp (j ≫ ν) π).hom.app E := by
    have h := NatTrans.congr_app (Scheme.Modules.pseudofunctor_associativity j ν π) E
    simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.associator_hom_app,
      Functor.whiskerLeft_app, Category.id_comp, eqToHom_app] at h
    have e : ε.hom.app E = (Scheme.Modules.pullbackComp j (ν ≫ π)).hom.app E ≫ eqToHom (by simp) := by
      simp [ε, Scheme.Modules.pullbackCongr]
    rw [e, ← h]
    simp only [← Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app, Iso.hom_inv_id_app_assoc]
    simp
  refine ⟨ε.hom.app A ≫ t ≫ (Scheme.Modules.pullbackComp j ν).inv.app B, ?_⟩
  rw [← cancel_mono (ε.hom.app E)]
  refine Eq.trans ?_ (ε.hom.naturality c).symm
  rw [← ht, ← key, (Scheme.Modules.pullbackComp j ν).inv.naturality_assoc]
  simp

theorem normalization_lift {F : Type} [Field F] [NumberField F] {Y P Gs : Scheme.{0}} [IsIntegral Y] {p : Y ⟶ Sp (𝓞 F)}
    {d : ℕ} (hp : IsArithVar p d) (hn : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Y) (π : P ⟶ Y) (hP : IsProjOver (π ≫ p))
    {jY : Gs ⟶ Y} {s : Gs ⟶ Sp F} (pb : IsPullback jY s p (spMap (algebraMap (𝓞 F) F))) (g : Gs ⟶ P)
    (hg : g ≫ π = jY) :
    ∃ (X : Scheme.{0}) (_ : IsIntegral X) (ν : X ⟶ P) (j : Gs ⟶ X), j ≫ ν = g ∧ QuasiCompact j ∧
      IsSchemeTheoreticallyDominant j ∧ IsPullback j s ((ν ≫ π) ≫ p) (spMap (algebraMap (𝓞 F) F)) ∧
      FlagChain.IsCov p d (ν ≫ π) ∧ ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X := by
  have hpp : IsProper p := CommonModel.isProper_of_isProjOver hp.isProjOver
  have hπp : IsProper (π ≫ p) := CommonModel.isProper_of_isProjOver hP
  have hπ : IsSeparated π := IsSeparated.of_comp π p
  have hb : IsPreimmersion (spMap (algebraMap (𝓞 F) F)) :=
    IsPreimmersion.of_isLocalization (nonZeroDivisors (𝓞 F))
  have hbf : Flat (spMap (algebraMap (𝓞 F) F)) := by
    rw [Flat.SpecMap_iff]
    exact RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat F (nonZeroDivisors (𝓞 F)))
  have hj : IsPreimmersion jY := MorphismProperty.of_isPullback (P := @IsPreimmersion) pb.flip hb
  have hjf : Flat jY := MorphismProperty.of_isPullback (P := @Flat) pb.flip hbf
  have hja : IsAffineHom jY := MorphismProperty.of_isPullback (P := @IsAffineHom) pb.flip inferInstance
  have hs : IsProper s := MorphismProperty.of_isPullback (P := @IsProper) pb hpp

  have hη : genericPoint Y ∈ Set.range jY := by
    have hx : (p (genericPoint Y)).asIdeal = ⊥ := by
      have := hp.flat
      have h0 := RatFibreDeg.apply_genericPoint_of_flat (p ≫ spMap (Int.castRingHom (𝓞 F)))
      rw [genericPoint_eq_bot_of_affine] at h0
      have h' : Ideal.comap (algebraMap ℤ (𝓞 F)) (p (genericPoint Y)).asIdeal = ⊥ :=
        congrArg PrimeSpectrum.asIdeal h0
      exact Ideal.eq_bot_of_comap_eq_bot h'
    rw [← pb.isoPullback_hom_fst, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      pb.isoPullback.hom.surjective.range_eq, Set.image_univ, Scheme.Pullback.range_fst]
    refine ⟨(⊥ : PrimeSpectrum F), PrimeSpectrum.ext (Eq.trans ?_ hx.symm)⟩
    exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective (𝓞 F) F)
  have hGi : IsIntegral Gs := by
    have : IsReduced (pullback p (spMap (algebraMap (𝓞 F) F))) :=
      CurveClosure.isReduced_pullback_localization (𝓞 F) F (nonZeroDivisors (𝓞 F)) _ _
    have : IsReduced Gs := isReduced_of_isOpenImmersion pb.isoPullback.hom
    obtain ⟨z, hz⟩ := hη
    have : IrreducibleSpace Gs := by
      have hc : closure {z} = Set.univ := by
        rw [jY.isEmbedding.isInducing.closure_eq_preimage_closure_image, Set.image_singleton, hz,
          (genericPoint_spec Y).def, Set.preimage_univ]
      exact (irreducibleSpace_def _).2 (by
        have := isIrreducible_singleton (x := z).closure
        rwa [hc] at this)
    exact isIntegral_of_irreducibleSpace_of_isReduced Gs
  have hGn : GlobalTheory.IsNormalScheme Gs :=
    .of_pred (GlobalTheory.FlagCls.isNormalScheme_of_isPullback_fractionField (𝓞 F) F Y Gs p jY s pb hn)

  let g' : Gs ⟶ pullback π jY := pullback.lift g (𝟙 _) (by rw [hg, Category.id_comp])
  have h₁ : g' ≫ pullback.snd π jY = 𝟙 _ := pullback.lift_snd ..
  have h₂ : g = g' ≫ pullback.fst π jY := (pullback.lift_fst ..).symm
  have hc : IsClosedImmersion g' := by
    have : IsClosedImmersion (g' ≫ pullback.snd π jY) := by rw [h₁]; infer_instance
    exact IsClosedImmersion.of_comp g' (pullback.snd π jY)
  have hq : QuasiCompact g := by rw [h₂]; infer_instance
  have hq' : QuasiSeparated g := by rw [h₂]; infer_instance
  have pbP : IsPullback (pullback.fst π jY) (pullback.snd π jY ≫ s) (π ≫ p) (spMap (algebraMap (𝓞 F) F)) :=
    (IsPullback.of_hasPullback π jY).paste_vert pb
  have := PreservesNormalization.of_isPullback_localization (nonZeroDivisors (𝓞 F)) pbP
  have := isPreimmersion_of_isPullback_localization (nonZeroDivisors (𝓞 F)) pbP
  have pbX : IsPullback g.toNormalization s ((g.fromNormalization ≫ π) ≫ p) (spMap (algebraMap (𝓞 F) F)) := by
    have := (isPullback_toNormalization_of_mono g' (pullback.fst π jY) g h₂).paste_vert pbP
    rwa [reassoc_of% h₁, ← Category.assoc] at this
  have hfin : IsFinite g.fromNormalization :=
    isFinite_fromNormalization_of_over_fractionRing (o := .of (𝓞 F)) g (π ≫ p) F s (by rw [reassoc_of% hg, pb.w])
  have hXn : GlobalTheory.IsNormalScheme g.normalization := GlobalTheory.IsNormalScheme.normalization_of_isIntegral g
  have hXi : IsIntegral g.normalization := inferInstance
  have hjX : Flat g.toNormalization := MorphismProperty.of_isPullback (P := @Flat) pbX.flip hbf
  have e : g.toNormalization ≫ g.fromNormalization ≫ π = jY := by
    rw [g.toNormalization_fromNormalization_assoc, hg]
  have hgen := RatFibreDeg.apply_genericPoint_of_flat g.toNormalization
  have hgen' : (g.fromNormalization ≫ π) (genericPoint _) = genericPoint Y := by
    rw [← hgen, ← Scheme.Hom.comp_apply, e, RatFibreDeg.apply_genericPoint_of_flat]
  have hdeg : (g.fromNormalization ≫ π).residueDegree (genericPoint _) ≠ 0 := by
    intro h0
    have h1 := CurveDegreesCompare.residueDegree_comp g.toNormalization (g.fromNormalization ≫ π) (genericPoint _)
    rw [e, RatFibreDeg.residueDegree_of_surjectiveOnStalks, hgen, h0, zero_mul] at h1
    exact one_ne_zero h1
  have hproj : IsProjOver ((g.fromNormalization ≫ π) ≫ p) := by
    rw [Category.assoc]
    exact isProjOver_comp_of_isFinite _ hP
  have hflat : Flat (((g.fromNormalization ≫ π) ≫ p) ≫ spMap (Int.castRingHom (𝓞 F))) := by
    have : CharZero Γ(Gs, ⊤) :=
      charZero_of_injective_ringHom (s.appTop.hom.comp (Scheme.ΓSpecIso (.of F)).inv.hom : F →+* Γ(Gs, ⊤)).injective
    exact (flat_int_iff_charZero _).2 g.toNormalization.appTop.hom.charZero
  exact ⟨g.normalization, hXi, g.fromNormalization, g.toNormalization, g.toNormalization_fromNormalization,
    inferInstance, inferInstance, pbX, ⟨⟨hp.isDomain, hp.finite, hXi, hproj, hflat,
      DimCover.topologicalKrullDim_eq _ Y _ p _ d hp hproj hflat _ rfl hgen' hdeg⟩, hgen', hdeg⟩,
    GlobalTheory.IsNormalScheme.pred _⟩

theorem main : ∀ (F : Type) [Field F] [NumberField F] (Y : Scheme.{0}) [IsIntegral Y] (p : Y ⟶ Sp (𝓞 F)) (d : ℕ), IsArithVar p d →
    ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Y → ∀ (ι : Type) [Fintype ι] (N N' : ι → Y.Modules) (n : ι → ℕ),
    (∀ a, IsVB (N' a) (n a)) → ∀ (u : ∀ a, N a ⟶ N' a) (fl : ∀ a, Vert.Flag (N a) (n a))
      (Gs : Scheme.{0}) (jY : Gs ⟶ Y) (s : Gs ⟶ Sp F), IsPullback jY s p (spMap (algebraMap (𝓞 F) F)) →
    (∀ a, IsIso ((Scheme.Modules.pullback jY).map (u a))) →
    ∃ (X : Scheme.{0}) (_ : IsIntegral X) (ρ : X ⟶ Y) (fl' : ∀ a, Vert.Flag ((Scheme.Modules.pullback ρ).obj (N' a)) (n a)) (j : Gs ⟶ X),
      j ≫ ρ = jY ∧ IsPullback j s (ρ ≫ p) (spMap (algebraMap (𝓞 F) F)) ∧ FlagChain.IsCov p d ρ ∧
      ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X ∧ ∀ a, Compat ((Scheme.Modules.pullback ρ).map (u a)) ((fl a).pull ρ) (fl' a) := by
  intro F _ _ Y _ p d hp hn ι _ N N' n hN' u fl Gs jY s pb hu
  obtain ⟨P, _, π, fu, hfb, hP, -⟩ := GlobalTheory.FlagEx.main (𝓞 F) Y p d hp hn ι N' n hN'
  obtain ⟨g, ⟨hg, hfl⟩, -⟩ := hfb Gs jY fun a =>
    ((fl a).pull jY).ofIso (asIso ((Scheme.Modules.pullback jY).map (u a)))
  obtain ⟨X, _, ν, j, rfl, _, _, h₁, h₂, h₃⟩ := normalization_lift hp hn π hP.isProjOver pb g hg
  subst hg
  refine ⟨X, inferInstance, ν ≫ π, fun a => ((fu a).pull ν).ofIso ((Scheme.Modules.pullbackComp ν π).app (N' a)), j,
    (Category.assoc ..).symm, h₁, h₂, h₃, fun a => compat_of_pull j fun i => ?_⟩
  obtain ⟨e, he⟩ : ∃ e : (Scheme.Modules.pullback (j ≫ ν)).obj ((fu a).F i) ≅
      (Scheme.Modules.pullback ((j ≫ ν) ≫ π)).obj ((fl a).F i),
      e.hom ≫ (Scheme.Modules.pullback ((j ≫ ν) ≫ π)).map ((fl a).ι i) ≫
          (Scheme.Modules.pullback ((j ≫ ν) ≫ π)).map (u a) =
        (Scheme.Modules.pullback (j ≫ ν)).map ((fu a).ι i) ≫ (Scheme.Modules.pullbackComp (j ≫ ν) π).hom.app (N' a) ≫
          (Scheme.Modules.pullbackCongr rfl).hom.app (N' a) := hfl a i
  obtain ⟨t, ht⟩ := exists_fac_comp j ν π ((fl a).ι i ≫ u a) ((fu a).ι i) e.inv (by
    rw [Iso.inv_comp_eq, Functor.map_comp]
    rw [he]
    simp [Scheme.Modules.pullbackCongr])
  refine ⟨t, ht.trans ?_⟩
  rw [Functor.map_comp, Functor.map_comp]
  rfl

end GlobalTheory.FlagExtend
