import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsMumfordFamOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RangeSubsetAbelianLocusOfGoodReduction
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HomExtensionSemiAbelianDiscreteValuationRing
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc
open ReciprocityTheory.AnForm.R
open scoped CategoryTheory.Obj
open GlobalTheory.GoodVal

theorem GlobalTheory.ChartAbelian.mem_abLocus_of_mem_range : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (S : Scheme.{0}) (j : F.X ⟶ S) [IsOpenImmersion j] (R : Type) [CommRing R] [IsRegularLocalRing R] [IsDomain R] (ξ : Sp R ⟶ S) (G₁ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] (y : Sp (FractionRing R) ⟶ F.X) (A₁ : Over (Sp (FractionRing R))) [GrpObj A₁] (i₁ : A₁.left ⟶ G₁.left) (β : A₁.left ⟶ F.univ.A.left), IsSemiAbelian G₁ → IsGrpPullback A₁ G₁ (jK R) i₁ → IsGrpPullback A₁ F.univ.A y β → y ≫ j = jK R ≫ ξ → ∀ p : Sp R, ξ p ∈ Set.range j → p ∈ abLocus G₁ := by
  intro g n F S j _ R _ _ _ ξ G₁ _ _ y A₁ _ i₁ β hG hA hB hy p hp
  have : IsNoetherianRing R := inferInstance
  let K := FractionRing R
  by_cases hp0 : p.asIdeal = ⊥
  · have hAprop : IsProper A₁.hom := MorphismProperty.of_isPullback (P := @IsProper) hB.1 F.univ.ab.proper
    refine abLocusOne _ G₁ hG K (jK R) (by rw [← hA.1.isoPullback_inv_snd]; infer_instance) ⟨(⊥ : PrimeSpectrum K), ?_⟩
    apply PrimeSpectrum.ext
    change Ideal.comap (algebraMap R K) ⊥ = p.asIdeal
    rw [hp0]
    exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective R K)
  · have := p.isPrime
    obtain ⟨T, hT, gT, hg, hgp⟩ := exists_dvr_centre (K := K) (L := K) p.asIdeal hp0
    have hc : spMap (algebraMap T K) ≫ spMap gT = jK R := by
      rw [← spMap_comp, hg]
    have hginj : Function.Injective gT := by
      refine Function.Injective.of_comp (f := algebraMap T K) ?_
      rw [← RingHom.coe_comp, hg]
      exact (algebraMap K K).injective.comp (IsFractionRing.injective R K)
    have hcl : spMap gT (IsLocalRing.closedPoint T) = p := PrimeSpectrum.ext hgp
    have hr : Set.range (spMap gT ≫ ξ) ⊆ Set.range j := by
      rintro _ ⟨q, rfl⟩
      by_cases hq : q.asIdeal = ⊥
      · have hq' : q = spMap (algebraMap T K) (⊥ : PrimeSpectrum K) := by
          apply PrimeSpectrum.ext
          change q.asIdeal = Ideal.comap (algebraMap T K) ⊥
          rw [hq]; exact (Ideal.comap_bot_of_injective _ (IsFractionRing.injective T K)).symm
        refine ⟨y (⊥ : PrimeSpectrum K), ?_⟩
        rw [hq']
        have e : spMap (algebraMap T K) ≫ spMap gT ≫ ξ = y ≫ j := by rw [hy, ← Category.assoc, hc]
        have e' := (congrArg (fun f : Sp K ⟶ S => f (⊥ : PrimeSpectrum K)) e).symm
        first | exact e' | (dsimp only at e'; rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at e'; exact e')
      · have hq' : q = IsLocalRing.closedPoint T :=
          PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal (Ring.DimensionLEOne.maximalOfPrime hq q.isPrime))
        rw [hq']
        have e : (spMap gT ≫ ξ) (IsLocalRing.closedPoint T) = ξ p := by rw [← hcl]; rfl
        rw [e]; exact hp
    haveI := hT
    let yT : Sp T ⟶ F.X := IsOpenImmersion.lift j (spMap gT ≫ ξ) hr
    have hyT : yT ≫ j = spMap gT ≫ ξ := IsOpenImmersion.lift_fac _ _ _
    have hyK : spMap (algebraMap T K) ≫ yT = y := by
      rw [← cancel_mono j, Category.assoc, hyT, ← Category.assoc, hc, hy]
    have hid : IsPullback (𝟙 F.univ.A.left) F.univ.A.hom F.univ.A.hom (𝟙 F.X) :=
      IsPullback.of_horiz_isIso ⟨by rw [Category.id_comp, Category.comp_id]⟩
    have := F.univ.ab.smooth
    have := F.univ.ab.proper
    have := F.univ.ab.geomConnected
    obtain ⟨hBs, hB'⟩ := isSemiAbelian_pullback_of_range_subset F.univ.A hid yT (by
      rintro _ ⟨x, rfl⟩; exact ⟨yT x, rfl⟩)
    have hH := IsSemiAbelian.pullback (spMap gT) G₁ hG
    have hPB := ((isGrpPullback_pullback ((Over.pullback yT).obj F.univ.A) (spMap (algebraMap T K))).comp
      (isGrpPullback_pullback F.univ.A yT)).congr hyK rfl
    obtain ⟨a, ha, -⟩ := grpPullback_iso hPB hB
    have hPG := ((isGrpPullback_pullback ((Over.pullback (spMap gT)).obj G₁) (spMap (algebraMap T K))).comp
      (isGrpPullback_pullback G₁ (spMap gT))).congr hc rfl
    obtain ⟨b, hb, -⟩ := grpPullback_iso hA hPG
    have hE : IsMonHom (a ≪≫ b).hom := inferInstanceAs (IsMonHom (a.hom ≫ b.hom))
    obtain ⟨Φ, ⟨-, hΦ⟩, -⟩ := GlobalTheory.homExtension_semiAbelian_dvr T K _ _ hBs hH (a ≪≫ b).hom hE
    obtain ⟨Ψ, ⟨-, hΨ⟩, -⟩ := GlobalTheory.homExtension_semiAbelian_dvr T K _ _ hH hBs (a ≪≫ b).inv inferInstance
    have hx := (abLocus_pullback abLocusOne hG (isGrpPullback_pullback G₁ (spMap gT)).1
      (IsLocalRing.closedPoint T)).2 (abLocus_subset_of_extends hBs hH _ Φ Ψ hΦ hΨ (hB' _))
    rw [hcl] at hx
    exact hx
