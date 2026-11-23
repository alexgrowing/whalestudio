import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkBaseChange
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ProperRelAmpleKTrivOfFieldExtension
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RelAmpleOfAmpleGeometricFibresAbelianScheme
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PolarisationExtendsOverDvrGoodReduction
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.KTrivOfKTrivNonemptyOpenNormalCharZero
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SurjectiveCubeBaseChange
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PolBaseChangeOfRelAmpleLocal
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PolPoint

theorem isProper_of_image {S T : Scheme.{0}} (A : Over S) (B : Over T) (g : T ⟶ S) (φ : B.left ⟶ A.left)
    (h : IsPullback φ B.hom A.hom g) (W : S.Opens) (hg : ∀ t, g t ∈ W) (hpr : IsProper (A.hom ∣_ W)) :
    IsProper B.hom := by
  have hr : Set.range g ⊆ Set.range W.ι := by
    rintro _ ⟨y, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact hg y
  have hr' : Set.range φ ⊆ Set.range (A.hom ⁻¹ᵁ W).ι := by
    rintro _ ⟨y, rfl⟩
    rw [Scheme.Opens.range_ι]
    show A.hom (φ y) ∈ W
    rw [← Scheme.Hom.comp_apply, h.w, Scheme.Hom.comp_apply]
    exact hg _
  let l := IsOpenImmersion.lift W.ι _ hr
  let ψ := IsOpenImmersion.lift (A.hom ⁻¹ᵁ W).ι φ hr'
  have hl : l ≫ W.ι = g := IsOpenImmersion.lift_fac _ _ hr
  have hψ : ψ ≫ (A.hom ⁻¹ᵁ W).ι = φ := IsOpenImmersion.lift_fac _ _ hr'
  have big : IsPullback (ψ ≫ (A.hom ⁻¹ᵁ W).ι) B.hom A.hom (l ≫ W.ι) := by rw [hψ, hl]; exact h
  have sq : IsPullback ψ B.hom (A.hom ∣_ W) l := by
    refine IsPullback.of_right big ?_ (isPullback_morphismRestrict A.hom W).flip
    rw [← cancel_mono W.ι, Category.assoc, morphismRestrict_ι, ← Category.assoc, hψ, h.w, Category.assoc, hl]
  exact MorphismProperty.of_isPullback (P := @IsProper) sq hpr

theorem exists_field_point_polarised : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ W : (Sp R).Opens, IsProper (G.hom ∣_ W) → ∀ y : PrimeSpectrum R, y ∈ W → y.asIdeal ≠ ⊥ → ∃ (K₁ : Type) (_ : Field K₁) (z : Sp K₁ ⟶ Sp R), z (closedPoint K₁) = y ∧ IsProper (pullback.snd G.hom z) ∧ RelAmple ((Over.pullback z).obj G) (U.LG.L.pull (pullback.fst G.hom z)) ∧ KTriv ((Over.pullback z).obj G) (U.LG.L.pull (pullback.fst G.hom z)) := by
  intro R _ _ _ hR D A G _ _ hG U W hW y hyW hy
  obtain ⟨⟨hN, -, -, -⟩, -⟩ := hR
  let O := Localization.AtPrime y.asIdeal
  have hiO : Function.Injective (algebraMap R O) :=
    IsLocalization.injective O y.asIdeal.primeCompl_le_nonZeroDivisors
  haveI : IsDomain O := IsLocalization.isDomain_localization y.asIdeal.primeCompl_le_nonZeroDivisors
  haveI : IsNoetherianRing O := IsLocalization.isNoetherianRing y.asIdeal.primeCompl O hN
  have hf : ¬ IsField O := by
    intro hfO
    apply hy
    have h1 : maximalIdeal O = ⊥ := (IsLocalRing.isField_iff_maximalIdeal_eq).1 hfO
    have h2 := Localization.AtPrime.comap_maximalIdeal (I := y.asIdeal)
    rw [← h2, Ideal.under, h1]
    exact Ideal.comap_bot_of_injective _ hiO
  obtain ⟨V, _, _, _, ρ, hρ, hloc⟩ := GlobalTheory.KTrivSpread.exists_dvr O hf
  let a : R →+* V := ρ.comp (algebraMap R O)
  have ha : Function.Injective a := hρ.comp hiO
  have hgen : ∀ q : PrimeSpectrum V, spMap a q ∈ W := by
    intro q
    have hle : PrimeSpectrum.comap a q ≤ y := by
      show Ideal.comap a q.asIdeal ≤ y.asIdeal
      intro s hs
      rw [← Localization.AtPrime.comap_maximalIdeal (I := y.asIdeal)]
      exact IsLocalRing.le_maximalIdeal (q.isPrime.comap ρ).ne_top hs
    exact ((PrimeSpectrum.le_iff_specializes _ _).1 hle).mem_open W.isOpen hyW
  let B := (Over.pullback (spMap a)).obj G
  have hcart : IsPullback (pullback.fst G.hom (spMap a)) B.hom G.hom (spMap a) := IsPullback.of_hasPullback _ _
  have hpB : IsProper B.hom := isProper_of_image G B (spMap a) _ hcart W hgen hW
  have hsB := IsSemiAbelian.pullback (spMap a) G hG
  have hAb : IsAbelianScheme B := ⟨hsB.comm, hsB.smooth, hpB, hsB.geomConnected⟩
  obtain ⟨hL, hL2, -⟩ := GlobalTheory.allSixLaws
  let M := GlobalTheory.ValueForm.modelCP U.toUnifPre hL.globalFns
  let φ := U.gen.inv.left ≫ pullback.fst G.hom (jK R)
  have hφ : IsGrpPullback A.A G (spMap (algebraMap R (FractionRing R))) φ :=
    GlobalTheory.ThetaBaseChange.grp_generic U.toUnifPre
  have hgi : U.gen.inv.left ≫ U.gen.hom.left = 𝟙 _ := by
    rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
  have hLφ : LBIso A.L (M.L.L.pull φ) := LBIso.chartPull (h := U.gen.inv.left) (chartPullSec A.L _ _ hgi)
    (chartPullSame U.LG.L _ (fun _ => pullback.fst G.hom (jK R)) _ _ fun _ => rfl) U.ext
  obtain ⟨P', M', φ', hφ', hL', hM'⟩ :=
    GlobalTheory.PolExtendDVR.exists_baseChange (K' := FractionRing V) hL.polBaseChange a ha A G M φ hφ hLφ
  obtain ⟨hAB, hKB⟩ := GlobalTheory.polarisation_extends_dvr hL hL2 V (FractionRing V) P' B M' φ' hAb hφ' hL'
  let r := IsLocalRing.residue V
  obtain ⟨z, hz0⟩ : ∃ z : Sp (IsLocalRing.ResidueField V) ⟶ Sp R, z = spMap (r.comp a) := ⟨_, rfl⟩
  have hz : z = spMap r ≫ spMap a := by
    rw [hz0]
    unfold spMap
    rw [← Spec.map_comp]
    rfl
  let ψ : pullback G.hom z ⟶ B.left := pullback.lift (pullback.fst G.hom z) (pullback.snd G.hom z ≫ spMap r)
    (by rw [pullback.condition, hz, Category.assoc])
  have hψ : ψ ≫ pullback.fst G.hom (spMap a) = pullback.fst G.hom z := pullback.lift_fst _ _ _
  have hψ2 : ψ ≫ B.hom = ((Over.pullback z).obj G).hom ≫ spMap r := pullback.lift_snd _ _ _
  have hgz : IsGrpPullback ((Over.pullback z).obj G) B (spMap r) ψ :=
    (isGrpPullback_pullback G (spMap a)).cancel ((isGrpPullback_pullback G z).congr hz hψ.symm) hψ2
  have hiso : LBIso (U.LG.L.pull (pullback.fst G.hom z)) (M'.L.L.pull ψ) := by
    have e := GlobalTheory.PolExtendDVR.lbIso_pull_comp hM' ψ
    rw [hψ] at e
    exact e.symm
  obtain ⟨w, hw⟩ := hiso
  have hw' := (isGen_iff w).1 hw
  refine ⟨IsLocalRing.ResidueField V, inferInstance, z, ?_, ?_, ?_, ?_⟩
  · have e1 : PrimeSpectrum.comap r (IsLocalRing.closedPoint (IsLocalRing.ResidueField V)) =
        IsLocalRing.closedPoint V := IsLocalRing.comap_closedPoint r
    have e2 : PrimeSpectrum.comap ρ (IsLocalRing.closedPoint V) = IsLocalRing.closedPoint O :=
      IsLocalRing.comap_closedPoint ρ
    have e3 : PrimeSpectrum.comap (algebraMap R O) (IsLocalRing.closedPoint O) = y :=
      PrimeSpectrum.ext Localization.AtPrime.under_maximalIdeal
    rw [hz0]
    show PrimeSpectrum.comap (algebraMap R O) (PrimeSpectrum.comap ρ
      (PrimeSpectrum.comap r (IsLocalRing.closedPoint (IsLocalRing.ResidueField V)))) = y
    rw [e1, e2, e3]
  · exact MorphismProperty.of_isPullback (P := @IsProper) hgz.1 hpB
  · exact relAmple_pull hgz.1 M'.L.isLB (pull_isLB U.LG.isLB _) hw' ⊤ (isAffineOpen_top _) (fun _ => trivial) hAB
  · exact kTriv_pull hgz M'.L.isLB (pull_isLB U.LG.isLB _) hw' hKB

end GlobalTheory.PolPoint
