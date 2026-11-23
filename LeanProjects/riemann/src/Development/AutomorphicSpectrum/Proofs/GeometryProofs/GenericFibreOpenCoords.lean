import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsPeriodAtRestrict
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IntegralClosureHeightEqOneOfLiesOver
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatLineGenerator
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CardComapMulFinsumEqFinsumFibres
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SncPts
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ConstantsInCoordRatioField
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.UnitAtOfMulRight
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ProdUpdateDiv
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GermGenPtInjectiveRangeRegAtStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegAtIffChartLocalizationStatement
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsBasisKaehlerOfAlgebraicIndependent
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SpanFinrankMaximalIdealLeNcardOfLeSupSq
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ChartPrimeGivesComponent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCoordinateNearGenericPoint
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase GlobalTheory.CompanionTheory.Ar.GeoModel
open GroundTheory.Heights₂.Heights.LowerBoundFree

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.GenSmooth

open scoped KaehlerDifferential TensorProduct

theorem exists_away_of_smooth (k A L : Type) [Field k] [CharZero k] [CommRing A] [IsDomain A] [Algebra k A]
    [Algebra.Smooth k A] [Field L] [Algebra A L] [IsFractionRing A L] [Algebra k L] [IsScalarTower k A L]
    (e : ℕ) (he : Algebra.trdeg k L = e) (q : Ideal A) [q.IsPrime] :
    ∃ f ∉ q, Algebra.IsStandardSmoothOfRelativeDimension e k (Localization.Away f) := by
  have : Algebra.FormallySmooth k A := inferInstance
  have : Algebra.FinitePresentation k A := inferInstance
  let Aq := Localization.AtPrime q
  have : Algebra.FormallySmooth A Aq := .of_isLocalization q.primeCompl
  have hsm : Algebra.FormallySmooth k Aq := .comp k A Aq
  have : Algebra.IsSmoothAt k q := hsm
  refine GlobalTheory.exists_isStandardSmoothOfRelativeDimension_of_isSmoothAt k q ?_
  have hle : q.primeCompl ≤ nonZeroDivisors A := q.primeCompl_le_nonZeroDivisors
  let _ : Algebra Aq L := IsLocalization.localizationAlgebraOfSubmonoidLe _ _ _ _ hle
  have : IsScalarTower A Aq L := IsLocalization.localization_isScalarTower_of_submonoid_le _ _ _ _ hle
  have : IsScalarTower k Aq L := .to₁₃₄ k A _ _
  have := IsLocalization.isLocalization_of_submonoid_le Aq L _ _ hle
  have : Algebra.FormallyEtale Aq L := .of_isLocalization ((nonZeroDivisors A).map (algebraMap A Aq))
  have : Algebra.EssFiniteType A L := .of_isLocalization L (nonZeroDivisors A)
  have : Algebra.EssFiniteType k L := .comp k A L
  have : Algebra.EssFiniteType A Aq := .of_isLocalization Aq q.primeCompl
  have : Algebra.EssFiniteType k Aq := .comp k A Aq
  have : Module.Projective Aq Ω[Aq⁄k] := Algebra.FormallySmooth.projective_kaehlerDifferential
  have : Module.Finite Aq Ω[Aq⁄k] := inferInstance
  have : Module.FinitePresentation Aq Ω[Aq⁄k] := Module.finitePresentation_of_projective _ _
  have : Module.Flat Aq Ω[Aq⁄k] := Module.Flat.of_projective
  have : Module.Free Aq Ω[Aq⁄k] := Module.free_of_flat_of_isLocalRing
  have h1 := (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k Aq L).finrank_eq
  rw [Module.finrank_baseChange] at h1
  show Module.finrank Aq Ω[Aq⁄k] = e
  rw [h1, Module.finrank, GlobalTheory.rank_kaehler_eq_trdeg, he]
  simp

theorem smoothOfRelativeDimension_spec (k A L : Type) [Field k] [CharZero k] [CommRing A] [IsDomain A] [Algebra k A]
    [Algebra.Smooth k A] [Field L] [Algebra A L] [IsFractionRing A L] [Algebra k L] [IsScalarTower k A L]
    (e : ℕ) (he : Algebra.trdeg k L = e) :
    SmoothOfRelativeDimension e (Spec.map (CommRingCat.ofHom (algebraMap k A))) := by
  refine (HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension e)).2 ?_
  refine ⟨{f | Algebra.IsStandardSmoothOfRelativeDimension e k (Localization.Away f)}, ?_, fun f hf => ?_⟩
  · by_contra h
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ h
    obtain ⟨f, hf, hs⟩ := exists_away_of_smooth k A L e he m
    exact hf (hle (Ideal.subset_span hs))
  · have h : Algebra.IsStandardSmoothOfRelativeDimension e k (Localization.Away f) := hf
    simpa [RingHom.algebraMap_toAlgebra, IsScalarTower.algebraMap_eq k A (Localization.Away f)] using
      (RingHom.isStandardSmoothOfRelativeDimension_algebraMap e).2 h

theorem smooth_of_numberField (F A : Type) [Field F] [NumberField F] [CommRing A] [Algebra ℚ A] [Algebra F A]
    [IsScalarTower ℚ F A] [Algebra.Smooth ℚ A] : Algebra.Smooth F A := by
  have : Algebra.FormallySmooth ℚ A := inferInstance
  have : Algebra.FinitePresentation ℚ A := inferInstance
  have : Algebra.FormallyEtale ℚ F := Algebra.FormallyEtale.of_isSeparable ℚ F
  exact ⟨Algebra.FormallySmooth.of_restrictScalars ℚ F A,
    Algebra.FinitePresentation.of_restrict_scalars_finitePresentation ℚ F A⟩

open Algebra in

theorem trdeg_numberField (F Ω : Type) [Field F] [NumberField F] [Field Ω] [CharZero Ω] [Algebra F Ω] :
    Algebra.trdeg F Ω = Algebra.trdeg ℤ Ω := by
  let _ : Algebra ℚ Ω := DivisionRing.toRatAlgebra
  have hQ : Algebra.trdeg ℚ Ω = Algebra.trdeg ℤ Ω := GlobalTheory.GenericEtale.trdeg_eq ℤ ℚ Ω Ω
  have : IsScalarTower ℚ F Ω := IsScalarTower.of_algebraMap_eq fun r => by simp
  have h := trdeg_add_eq ℚ F (A := Ω)
  rw [trdeg_eq_zero, zero_add] at h
  rw [h, hQ]

theorem smooth_spec_numberField (F A Ω : Type) [Field F] [NumberField F] [CommRing A] [IsDomain A] [Algebra ℚ A]
    [Algebra.Smooth ℚ A] [Field Ω] [CharZero Ω] [Algebra A Ω] [IsFractionRing A Ω] (b : F →+* A) (n : ℕ)
    (ht : Algebra.trdeg ℤ Ω = n) : SmoothOfRelativeDimension n (spMap b) := by
  letI : Algebra F A := b.toAlgebra
  have t1 : IsScalarTower ℚ F A := IsScalarTower.of_algebraMap_eq fun r => RingHom.congr_fun
    (Subsingleton.elim (algebraMap ℚ A) ((algebraMap F A).comp (algebraMap ℚ F))) r
  have s1 : Algebra.Smooth F A := smooth_of_numberField F A
  letI : Algebra F Ω := ((algebraMap A Ω).comp b).toAlgebra
  have t2 : IsScalarTower F A Ω := IsScalarTower.of_algebraMap_eq' rfl
  exact smoothOfRelativeDimension_spec F A Ω n ((trdeg_numberField F Ω).trans ht)

theorem smooth_on_open {X S T Z Q : Scheme.{0}} (g : X ⟶ S) (b' : T ⟶ S) (U : X.Opens) (u : U.toScheme ≅ Z)
    (i : Z ⟶ S) (hu : u.hom ≫ i = U.ι ≫ g) (j : Q ⟶ Z) (b : Q ⟶ T) (hsq : IsPullback b j b' i) (n : ℕ)
    [SmoothOfRelativeDimension n b] :
    SmoothOfRelativeDimension n ((pullback.fst g b' ⁻¹ᵁ U).ι ≫ pullback.snd g b') := by
  have h1 := IsPullback.of_hasPullback g b'
  have h2 := isPullback_morphismRestrict (pullback.fst g b') U
  have h3 : IsPullback ((pullback.fst g b' ⁻¹ᵁ U).ι ≫ pullback.snd g b') (pullback.fst g b' ∣_ U) b' (U.ι ≫ g) :=
    h2.flip.paste_horiz h1.flip
  have h4 : IsPullback b (j ≫ u.inv) b' (U.ι ≫ g) :=
    hsq.of_iso (Iso.refl _) (Iso.refl _) u.symm (Iso.refl _) (by simp) (by simp) (by simp) (by rw [← hu]; simp)
  have he := IsPullback.isoIsPullback_hom_fst _ _ h3 h4
  rw [← he]
  have := smoothOfRelativeDimension_comp 0 n (IsPullback.isoIsPullback _ _ h3 h4).hom b
  rwa [zero_add] at this

theorem isPullback_spec (F Z Q : Type) [Field F] [NumberField F] [CommRing Z] [CommRing Q]
    (i : 𝓞 F →+* Z) (j : Z →+* Q) (b : F →+* Q) (h : j.comp i = b.comp (algebraMap (𝓞 F) F))
    (hj : Function.Injective j) (hu : ∀ m : ℕ, m ≠ 0 → IsUnit (m : Q))
    (hs : ∀ q : Q, ∃ m : ℕ, m ≠ 0 ∧ ∃ z : Z, j z = (m : Q) * q) :
    IsPullback (spMap b) (spMap j) (spMap (algebraMap (𝓞 F) F)) (spMap i) := by
  letI : Algebra (𝓞 F) Z := i.toAlgebra
  letI : Algebra Z Q := j.toAlgebra
  letI : Algebra F Q := b.toAlgebra
  letI : Algebra (𝓞 F) Q := (j.comp i).toAlgebra
  have t1 : IsScalarTower (𝓞 F) Z Q := IsScalarTower.of_algebraMap_eq' rfl
  have t2 : IsScalarTower (𝓞 F) F Q := IsScalarTower.of_algebraMap_eq' h
  have l1 : IsLocalization (Algebra.algebraMapSubmonoid (𝓞 F) (nonZeroDivisors ℤ)) F :=
    IsIntegralClosure.isLocalization ℤ ℚ F (𝓞 F)
  have l2 : IsLocalization (Algebra.algebraMapSubmonoid Z (Algebra.algebraMapSubmonoid (𝓞 F) (nonZeroDivisors ℤ))) Q := by
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨_, ⟨_, ⟨n, hn, rfl⟩, rfl⟩⟩
      have hn0 : n ≠ 0 := nonZeroDivisors.ne_zero hn
      have e : algebraMap Z Q (algebraMap (𝓞 F) Z (algebraMap ℤ (𝓞 F) n)) = (n : Q) := by simp
      show IsUnit (algebraMap Z Q (algebraMap (𝓞 F) Z (algebraMap ℤ (𝓞 F) n)))
      rw [e]
      have hu' := hu n.natAbs (Int.natAbs_ne_zero.2 hn0)
      rcases Int.natAbs_eq n with hh | hh
      · rw [hh]; simpa using hu'
      · rw [hh]; simpa using hu'
    · intro q
      obtain ⟨m, hm, z, hz⟩ := hs q
      refine ⟨⟨z, ⟨_, ⟨algebraMap ℤ (𝓞 F) (m : ℤ), ⟨(m : ℤ), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hm), rfl⟩, rfl⟩⟩⟩, ?_⟩
      show q * algebraMap Z Q (algebraMap (𝓞 F) Z (algebraMap ℤ (𝓞 F) (m : ℤ))) = algebraMap Z Q z
      have e : algebraMap Z Q (algebraMap (𝓞 F) Z (algebraMap ℤ (𝓞 F) (m : ℤ))) = (m : Q) := by simp
      rw [e, mul_comm]
      exact hz.symm
    · intro a c hac
      exact ⟨1, by rw [hj hac]⟩
  have hp : Algebra.IsPushout (𝓞 F) Z F Q :=
    Algebra.isPushout_of_isLocalization (Algebra.algebraMapSubmonoid (𝓞 F) (nonZeroDivisors ℤ)) F Z Q
  have hc := (CommRingCat.isPushout_iff_isPushout (R := 𝓞 F) (S := F) (R' := Z) (S' := Q)).2 hp
  exact (isPullback_SpecMap_of_isPushout _ _ _ _ hc).flip

theorem mem_regAt_gen {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} (hg : IsCptGen ξ) (a : Ω) :
    a ∈ regAt ξ ⟨genPt ξ, specializes_rfl⟩ := by
  obtain ⟨s, hs⟩ := hg.bij.2 a
  refine ⟨s, ?_⟩
  show (X.presheaf.stalkSpecializes specializes_rfl ≫ Scheme.stalkClosedPointTo ξ).hom s = a
  rw [TopCat.Presheaf.stalkSpecializes_refl, Category.id_comp]
  exact hs

theorem exists_chart {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {κ : Type} {x : κ → Ω}
    (hT : CoordTie ℤ ξ x) {O : Type} [CommRing O] (g : X ⟶ Sp O) (φ : O →+* Ω) (hg : ξ ≫ g = spMap φ) (c : κ)
    (hc : x c ≠ 0) :
    ∃ (U : X.Opens) (i : O →+* Algebra.adjoin ℤ (Set.range fun j => x j / x c))
      (u : U.toScheme ≅ Sp (Algebra.adjoin ℤ (Set.range fun j => x j / x c))),
      (∀ q : X, q ∈ U ↔ ∃ h : genPt ξ ⤳ q, InChart ξ x c ⟨q, h⟩) ∧ u.hom ≫ spMap i = U.ι ≫ g ∧
        ∀ o, (i o : Ω) = φ o := by
  obtain ⟨U, hU, hm⟩ := hT.affine c hc
  have hgen : genPt ξ ∈ U := (hm _).2 ⟨specializes_rfl, hc, fun c' => mem_regAt_gen hT.gen _⟩
  have hsp : ∀ q, q ∈ U → genPt ξ ⤳ q := fun q h => ((hm q).1 h).1
  obtain ⟨inj, ran⟩ := GlobalTheory.T.germ_genPt_injective_range_regAt X Ω ξ hT.gen U hgen hsp
  let val : Γ(X, U) →+* Ω := (X.presheaf.germ U (genPt ξ) hgen ≫ Scheme.stalkClosedPointTo ξ).hom
  have memZ : ∀ a, a ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c) ↔ a ∈ val.range := fun a =>
    (hT.ring c hc a).trans ((forall_congr' fun q => imp_congr
      ⟨fun h => (hm q.1).2 ⟨q.2, h⟩, fun h => ((hm q.1).1 h).2⟩ Iff.rfl).trans (ran a).symm)
  let eU : Γ(X, U) ≃+* Algebra.adjoin ℤ (Set.range fun j => x j / x c) := RingEquiv.ofBijective
    (val.codRestrict _ fun t => (memZ _).2 ⟨t, rfl⟩)
    ⟨fun a b hab => inj (congrArg Subtype.val hab), fun r => by
      obtain ⟨t, ht⟩ := (memZ r.1).1 r.2
      exact ⟨t, Subtype.ext ht⟩⟩
  have hA : Spec.map (CommRingCat.ofHom val) ≫ hU.fromSpec = ξ := by
    have h := Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ
    have h2 := hU.fromSpecStalk_eq_fromSpecStalk hgen
    rw [IsAffineOpen.fromSpecStalk] at h2
    have e : CommRingCat.ofHom val = X.presheaf.germ U (genPt ξ) hgen ≫ Scheme.stalkClosedPointTo ξ := rfl
    rw [e]
    refine (congrArg (· ≫ hU.fromSpec) (Spec.map_comp (X.presheaf.germ U (genPt ξ) hgen)
      (Scheme.stalkClosedPointTo ξ))).trans ?_
    rw [Category.assoc, h2]
    exact h
  let ρ : O →+* Γ(X, U) := (Spec.preimage (hU.fromSpec ≫ g)).hom
  have hρ : spMap ρ = hU.fromSpec ≫ g := by
    show Spec.map (CommRingCat.ofHom (Spec.preimage (hU.fromSpec ≫ g)).hom) = _
    rw [CommRingCat.ofHom_hom, Spec.map_preimage]
  have hval : ∀ o, val (ρ o) = φ o := by
    have h1 : spMap (val.comp ρ) = spMap φ := by
      rw [← hg, ← hA, Category.assoc, ← hρ]
      show Spec.map (CommRingCat.ofHom (val.comp ρ)) = _
      rw [CommRingCat.ofHom_comp, Spec.map_comp]
    have h2 := Spec.map_injective h1
    intro o
    exact congrArg (fun f => f.hom o) h2
  let i : O →+* Algebra.adjoin ℤ (Set.range fun j => x j / x c) := (eU : Γ(X, U) →+* _).comp ρ
  let eS := eU.symm.toRingHom
  have : IsIso (spMap eS) := by
    have : IsIso (CommRingCat.ofHom eS) := (eU.symm.toCommRingCatIso).isIso_hom
    infer_instance
  refine ⟨U, i, hU.isoSpec ≪≫ asIso (spMap eS), hm, ?_, fun o => hval o⟩
  have e : spMap eS ≫ spMap i = spMap ρ := by
    show Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext o
    simp only [i, CommRingCat.hom_ofHom, RingHom.comp_apply]
    exact eU.symm_apply_apply _
  simp only [Iso.trans_hom, asIso_hom, Category.assoc]
  rw [e, hρ, ← hU.isoSpec_inv_ι]
  simp

section Charts

variable {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type}

open GlobalTheory.CompanionTheory.Ar.SncBase.Mdl

theorem cst_mem_chartQ (F : Type) [Field F] [NumberField F] (cst : F →+* Ω) (x : κ → Ω) (c : κ)
    (h : ∀ a : 𝓞 F, cst (algebraMap (𝓞 F) F a) ∈ chartZ x c) (r : F) : cst r ∈ chartQ x c := by
  have halg : IsAlgebraic ℤ r := (IsFractionRing.isAlgebraic_iff ℤ ℚ F).2 (Algebra.IsAlgebraic.isAlgebraic r)
  obtain ⟨n, hn, hr⟩ := halg.exists_integral_multiple
  have hn' : (n : Ω) ≠ 0 := Int.cast_ne_zero.2 hn
  have e : cst r = algebraMap ℚ Ω (n : ℚ)⁻¹ * cst (algebraMap (𝓞 F) F (IsIntegralClosure.mk' (𝓞 F) (n • r) hr)) := by
    rw [IsIntegralClosure.algebraMap_mk', zsmul_eq_mul, map_mul, map_intCast]
    simp [hn']
  rw [e]
  exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) (chartZ_le x c (h _))

theorem isFractionRing_chartQ {X : Scheme.{0}} {ξ : Sp Ω ⟶ X} {x : κ → Ω} (hT : CoordTie ℤ ξ x) {c : κ} (hc : x c ≠ 0) :
    IsFractionRing (chartQ x c) Ω := by
  refine IsFractionRing.of_field _ _ fun a => ?_
  have hin : InChart ξ x c ⟨genPt ξ, specializes_rfl⟩ := ⟨hc, fun c' => mem_regAt_gen hT.gen _⟩
  obtain ⟨s, hs, hu, hsa⟩ := (GlobalTheory.T.regAt_iff_chart_localization X Ω ξ ℤ κ x hT c _ hin a).1 (mem_regAt_gen hT.gen a)
  refine ⟨⟨s * a, chartZ_le x c hsa⟩, ⟨s, chartZ_le x c hs⟩, ?_⟩
  show a = s * a / s
  rw [mul_div_cancel_left₀ _ hu.1]

theorem chartQ_segre {K : Type} [Fintype K] {J : K → Type} (y : (Σ k, J k) → Ω) (cc : (k : K) → J k)
    (hc : ∀ k, y ⟨k, cc k⟩ ≠ 0) :
    chartQ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) cc =
      Algebra.adjoin ℚ (Set.range fun p : Σ k, J k => y p / y ⟨p.1, cc p.1⟩) := by
  classical
  refine le_antisymm (Algebra.adjoin_le ?_) (Algebra.adjoin_le ?_)
  · rintro _ ⟨c', rfl⟩
    show (∏ k, y ⟨k, c' k⟩) / ∏ k, y ⟨k, cc k⟩ ∈ _
    rw [← Finset.prod_div_distrib]
    exact Subalgebra.prod_mem _ fun k _ => Algebra.subset_adjoin ⟨⟨k, c' k⟩, rfl⟩
  · rintro _ ⟨⟨k, i⟩, rfl⟩
    refine Algebra.subset_adjoin ⟨Function.update cc k i, ?_⟩
    show (∏ k', y ⟨k', Function.update cc k i k'⟩) / ∏ k', y ⟨k', cc k'⟩ = y ⟨k, i⟩ / y ⟨k, cc k⟩
    rw [← Finset.prod_div_distrib, Finset.prod_eq_single k]
    · simp
    · intro b _ hb
      rw [Function.update_of_ne hb, div_self (hc b)]
    · simp

theorem smooth_pullback {X : Scheme.{0}} {ξ : Sp Ω ⟶ X} (hall : ∀ q : X, genPt ξ ⤳ q) {x : κ → Ω}
    (hT : CoordTie ℤ ξ x) (F : Type) [Field F] [NumberField F] (g : X ⟶ Sp (𝓞 F)) (cst : F →+* Ω)
    (hg : ξ ≫ g = spMap (cst.comp (algebraMap (𝓞 F) F))) (n : ℕ)
    (hn : ∀ c, x c ≠ 0 → ∀ hb : ∀ r, cst r ∈ chartQ x c,
      SmoothOfRelativeDimension n (spMap (cst.codRestrict (chartQ x c) hb))) :
    SmoothOfRelativeDimension n (pullback.snd g (spMap (algebraMap (𝓞 F) F))) := by
  have key : ∀ c : {c // x c ≠ 0}, ∃ U : X.Opens,
      (∀ q : X, q ∈ U ↔ ∃ h : genPt ξ ⤳ q, InChart ξ x c.1 ⟨q, h⟩) ∧
      SmoothOfRelativeDimension n ((pullback.fst g (spMap (algebraMap (𝓞 F) F)) ⁻¹ᵁ U).ι ≫
        pullback.snd g (spMap (algebraMap (𝓞 F) F))) := by
    rintro ⟨c, hc⟩
    obtain ⟨U, i, u, hU, hu, hi⟩ := exists_chart hT g _ hg c hc
    have hb : ∀ r, cst r ∈ chartQ x c := cst_mem_chartQ F cst x c fun a => by
      rw [← RingHom.comp_apply, ← hi]
      exact (i a).2
    have := hn c hc hb
    refine ⟨U, hU, smooth_on_open g _ U u (spMap i) hu (spMap (chartIncl x c))
      (spMap (cst.codRestrict (chartQ x c) hb)) ?_ n⟩
    refine isPullback_spec F _ _ i (chartIncl x c) (cst.codRestrict (chartQ x c) hb) ?_ ?_ ?_ ?_
    · ext a
      exact hi a
    · intro a b hab
      exact Subtype.ext (congrArg (fun t : chartQ x c => (t : Ω)) hab)
    · intro m hm
      have hd : (m : Ω) ≠ 0 := Nat.cast_ne_zero.2 hm
      have hi' : (m : Ω)⁻¹ ∈ chartQ x c := by
        have := (chartQ x c).algebraMap_mem ((m : ℚ)⁻¹)
        simpa using this
      exact IsUnit.of_mul_eq_one ⟨_, hi'⟩ (Subtype.ext (by simp [hd]))
    · intro q
      obtain ⟨m, hm, hq⟩ := exists_natCast_mul_mem x c q.2
      exact ⟨m, hm, ⟨_, hq⟩, Subtype.ext (by simp [chartIncl])⟩
  choose U hU hS using key
  have : IsZariskiLocalAtSource (@SmoothOfRelativeDimension n) := HasRingHomProperty.instIsZariskiLocalAtSource
  refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension n)
    (fun c => pullback.fst g (spMap (algebraMap (𝓞 F) F)) ⁻¹ᵁ U c) ?_ hS
  refine top_le_iff.1 fun p _ => ?_
  obtain ⟨c, hc⟩ := hT.cover ⟨pullback.fst g (spMap (algebraMap (𝓞 F) F)) p, hall _⟩
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨c, hc.1⟩, (hU ⟨c, hc.1⟩ _).2 ⟨hall _, hc⟩⟩

end Charts

open GlobalTheory.CompanionTheory.Ar.SncBase.Mdl in

theorem smooth_genericFibre : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (M : PModel ℤ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩)) (f : M.X ⟶ Y.X) (y₀ : Sp Ω ⟶ Xo.XF c) (U : (pullback (f ≫ Y.s) (spMap (algebraMap (𝓞 c.F) c.F))).Opens), M.ξ ≫ f = y₀ ≫ Y.j → SmoothGenericFibreM y → Algebra.trdeg ℤ Ω = ((D.dim : ℕ) : Cardinal) → SmoothOfRelativeDimension D.dim (U.ι ≫ pullback.snd (f ≫ Y.s) (spMap (algebraMap (𝓞 c.F) c.F))) := by
  intro E _ _ _ H D l Xo c Y Ω _ _ K _ J _ y M f y₀ U hξ hsm htr
  haveI : FiniteDimensional ℚ c.F := c.fin
  haveI : NumberField c.F := { to_charZero := inferInstance, to_finiteDimensional := c.fin }
  obtain ⟨cst, hcst⟩ : ∃ cst : c.F →+* Ω, y₀ ≫ Y.j ≫ Y.s = spMap (cst.comp (algebraMap (𝓞 c.F) c.F)) := by
    refine ⟨(Spec.preimage (y₀ ≫ pullback.snd _ _)).hom, ?_⟩
    rw [Model.j, Category.assoc, pullback.condition, ← Category.assoc Y.jQ, Y.jQ_over, ← Category.assoc]
    unfold spMap
    rw [CommRingCat.ofHom_comp, Spec.map_comp, CommRingCat.ofHom_hom, Spec.map_preimage]
  have hg : M.ξ ≫ f ≫ Y.s = spMap (cst.comp (algebraMap (𝓞 c.F) c.F)) := by
    rw [← Category.assoc, hξ, Category.assoc]
    exact hcst
  have hP : SmoothOfRelativeDimension D.dim
      (pullback.snd (f ≫ Y.s) (spMap (algebraMap (𝓞 c.F) c.F))) := by
    refine smooth_pullback M.all M.tie c.F (f ≫ Y.s) cst hg D.dim fun c' hc' hb => ?_
    have hy : ∀ k, y ⟨k, c' k⟩ ≠ 0 := fun k => Finset.prod_ne_zero_iff.1 hc' k (Finset.mem_univ k)
    have hA : Algebra.Smooth ℚ (chartQ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) c') := by
      rw [chartQ_segre y c' hy]
      exact hsm c' hy
    have f1 : IsFractionRing (chartQ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) c') Ω :=
      isFractionRing_chartQ M.tie hc'
    exact smooth_spec_numberField c.F _ Ω _ D.dim htr
  have := smoothOfRelativeDimension_comp 0 D.dim U.ι
    (pullback.snd (f ≫ Y.s) (spMap (algebraMap (𝓞 c.F) c.F)))
  rwa [zero_add] at this

end GlobalTheory.CompanionTheory.Ar.GenSmooth
