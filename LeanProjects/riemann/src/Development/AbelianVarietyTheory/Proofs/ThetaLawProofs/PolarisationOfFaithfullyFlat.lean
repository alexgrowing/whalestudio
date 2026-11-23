import Mathlib
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ProperRelAmpleKTrivOfFieldExtension
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsGenOfGenericFibre
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SmoothOfRelativeDimensionOfFibre
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsGenOfLocalOnBase
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GroupSchemeMorphismDescends
import Development.AbelianVarietyTheory.Definitions.KeyFormula.IsSquareDeterminantComparison
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.IsPluriharmonicSiegel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.MapsAtLeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

noncomputable section

namespace GlobalTheory.PolFlatDescent

variable {S S' : Scheme.{0}} {f : S' ⟶ S} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A']
  {φ : A'.left ⟶ A.left}

theorem isCommMonObj_of_pull [Flat f] [Surjective f] (h : IsGrpPullback A' A f φ) [IsCommMonObj A'] :
    IsCommMonObj A := by
  refine ⟨GrpFlatDesc.hom_ext_of_points f fun T t => ?_⟩
  obtain ⟨x, hx⟩ := GrpDense.pushPt_surjective h.1 T (t ≫ fst _ _)
  obtain ⟨y, hy⟩ := GrpDense.pushPt_surjective h.1 T (t ≫ snd _ _)
  obtain rfl : t = lift (pushPt h.1.w x) (pushPt h.1.w y) :=
    CartesianMonoidalCategory.hom_ext _ _ (by rw [lift_fst, hx]) (by rw [lift_snd, hy])
  rw [lift_braiding_hom_assoc]
  exact Over.OverMorphism.ext ((h.2 T y x _ _ rfl rfl).trans
    ((congrArg (fun z => z.left ≫ φ) (_root_.mul_comm y x)).trans (h.2 T x y _ _ rfl rfl).symm))

theorem isAbelianScheme_of_pull [Flat f] [Surjective f] [QuasiCompact f] (h : IsGrpPullback A' A f φ)
    (hA : IsAbelianScheme A') : IsAbelianScheme A := by
  have := hA.comm
  have := hA.proper
  have := hA.geomConnected
  exact ⟨isCommMonObj_of_pull h, MorphismProperty.of_isPullback_of_descendsAlong (P := @Smooth)
      (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) h.1.flip ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ hA.smooth,
    GrpFlatDesc.isProper_of_isPullback h.1, GrpFlatDesc.geometricallyConnected_of_isPullback h.1⟩

theorem inv_left_comp (h : IsGrpPullback A' A f φ) :
    (GrpObj.inv : A' ⟶ A').left ≫ φ = φ ≫ (GrpObj.inv : A ⟶ A).left := by
  have e := congrArg (fun q => q.left) (map_inv (pushHom h A') (𝟙 A'))
  simp only [Hom.inv_def, Category.id_comp] at e
  exact e.trans (congrArg (· ≫ _) (Category.id_comp φ))

theorem exists_gen_pull_of_sym (hG : Out.GlobalFnsSt) (h : IsGrpPullback A' A f φ) (hA : IsAbelianScheme A')
    {L : LB A.left} {L' : LB A'.left} (hL : L.IsLB) (hL' : L'.IsLB) (hw : LBIso L' (L.pull φ)) (hS : Out.Sym A' L')
    {Y : Scheme.{0}} (r : Y ⟶ A'.left) :
    ∃ t : ((LB.LinComb L (K := Fin 2) ![(GrpObj.inv : A ⟶ A).left, 𝟙 _] ![1, -1]).pull (r ≫ φ)).Gen, t.IsGen := by
  obtain ⟨w, hw⟩ := hw
  obtain ⟨c, hc⟩ := exists_gen_neg_of_sym hG hA hL' hS
  obtain ⟨c₁, h₁⟩ := gen_chartPull (chartPullSame L' ![r ≫ (GrpObj.inv : A' ⟶ A').left, r] _ _ r fun k => by
    fin_cases k
    · rfl
    · exact (Category.comp_id r).symm) c hc
  obtain ⟨c₂, h₂, -⟩ := exists_up ((isGen_iff w).1 hw) hL hL' c₁ h₁
  exact gen_chartPull (chartPullOut L _ _ (r ≫ φ) _ fun k => by
      fin_cases k
      · exact (Category.assoc _ _ _).trans ((congrArg (r ≫ ·) (inv_left_comp h)).trans (Category.assoc _ _ _).symm)
      · exact (Category.comp_id _).symm) c₂ h₂

theorem polarisation_of_faithfullyFlat : Out.Laws → ∀ (R₀ R : Type) [CommRing R₀] [IsDomain R₀] [IsLocalRing R₀] [IsPrincipalIdealRing R₀] [CommRing R] [IsNoetherianRing R] [Algebra R₀ R] [Module.FaithfullyFlat R₀ R] (P : Out.PolAV (Sp R)) (A₀ : Over (Sp R₀)) [GrpObj A₀] [Flat A₀.hom] (L₀ : LB A₀.left) (π : P.A.left ⟶ A₀.left), IsProjBy A₀.hom → L₀.IsLB → IsGrpPullback P.A A₀ (spMap (algebraMap R₀ R)) π → LBIso P.L (L₀.pull π) → IsAbelianScheme A₀ ∧ SmoothOfRelativeDimension P.g A₀.hom ∧ Out.Rigidified A₀ L₀ ∧ Out.Sym A₀ L₀ ∧ Out.RelAmple A₀ L₀ ∧ Out.KTriv A₀ L₀ := by
  intro hL R₀ R _ _ _ _ _ _ _ _ P A₀ _ _ L₀ π _ hL₀ h hw
  have : Flat (spMap (algebraMap R₀ R)) := Flat.SpecMap_iff.2 (RingHom.flat_algebraMap_iff.2 inferInstance)
  have : Surjective (spMap (algebraMap R₀ R)) := ⟨PrimeSpectrum.comap_surjective_of_faithfullyFlat⟩
  have hA : IsAbelianScheme A₀ := isAbelianScheme_of_pull h P.isAb
  have := hA.smooth
  have := hA.proper
  have := P.isAb.proper
  have := forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ A₀.hom hA.smooth hA.geomConnected
  have : CompactSpace A₀.left := QuasiCompact.compactSpace_of_compactSpace A₀.hom
  have : QuasiSeparatedSpace A₀.left := quasiSeparatedSpace_of_quasiSeparated A₀.hom
  obtain ⟨q, hq⟩ := PrimeSpectrum.comap_surjective_of_faithfullyFlat (A := R₀) (B := R) ⊥
  let β : R →+* q.asIdeal.ResidueField := algebraMap _ _
  have hj : Function.Injective (β.comp (algebraMap R₀ R)) := by
    rw [RingHom.injective_iff_ker_eq_bot, ← RingHom.comap_ker, Ideal.ker_algebraMap_residueField]
    exact congrArg PrimeSpectrum.asIdeal hq
  have H : IsPullback (pullback.fst P.A.hom (spMap β) ≫ π) (pullback.snd P.A.hom (spMap β)) A₀.hom
      (spMap (β.comp (algebraMap R₀ R))) := by
    rw [show spMap (β.comp (algebraMap R₀ R)) = spMap β ≫ spMap (algebraMap R₀ R) from
      Spec.map_comp (CommRingCat.ofHom (algebraMap R₀ R)) (CommRingCat.ofHom β)]
    exact (IsPullback.of_hasPullback P.A.hom (spMap β)).paste_horiz h.1
  refine ⟨hA, ?_, DVR.exists_gen_of_local L₀ hL₀ _ _, ?_, ?_, AmpleDescent.kTriv_of_pull h hL₀ P.isLB hw P.ktriv⟩
  · exact CM.smoothOfRelativeDimension_of_fibre R₀ _ _ A₀ _ _ _ P.g hA H
      ((smoothOfRelativeDimension_isStableUnderBaseChange P.g).of_isPullback
        (IsPullback.of_hasPullback P.A.hom (spMap β)) P.smoothDim)
  · have hN := DVR.linComb_isLB L₀ hL₀ (K := Fin 2) ![(GrpObj.inv : A₀ ⟶ A₀).left, 𝟙 _] ![1, -1]
    obtain ⟨ρ, hρ⟩ := DVR.exists_gen_of_local (V := R₀) _ hN (K := PUnit) (fun _ => eSec A₀) (fun _ => 1)
    obtain ⟨t, ht⟩ := exists_gen_pull_of_sym hL.globalFns h P.isAb hL₀ P.isLB hw P.sym
      (pullback.fst P.A.hom (spMap β))
    obtain ⟨c, hc⟩ := GenericTriv.exists_gen_of_fibre _ hj A₀.hom (eSec A₀) (Over.w η[A₀]) _ _ H
      (Out.TLinPf.const_pullback hL.globalFns (spMap β) P.A P.isAb) hN ρ hρ t ht
    intro s
    refine ⟨⊤, trivial, gen_chartPull (chartPullSame L₀ _ _ _ (A₀.hom ⁻¹ᵁ ⊤).ι fun k => ?_) c hc⟩
    fin_cases k
    · rfl
    · exact (Category.comp_id _).symm
  · have : Flat (Out.specOf (algebraMap R₀ R)) := ‹Flat (spMap (algebraMap R₀ R))›
    have : Surjective (Out.specOf (algebraMap R₀ R)) := ‹Surjective (spMap (algebraMap R₀ R))›
    refine (relAmple_iff_isAmpleLB_of_isAffine A₀ hL₀).2 (AmpleDescent.isAmpleLB_of_pull _ h.1 hL₀ ?_)
    exact (isAmpleLB_of_relAmple_of_isAffine P.A P.isLB P.ample).of_lbIso (LB.isLB_pull hL₀ π) hw.symm

end GlobalTheory.PolFlatDescent
