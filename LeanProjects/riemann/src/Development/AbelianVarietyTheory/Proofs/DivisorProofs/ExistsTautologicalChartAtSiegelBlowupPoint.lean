import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.MinSt5OfMinSt4
import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
import Development.AbelianVarietyTheory.Definitions.Divisors.PullData
import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMember
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSiegelModuliTraitThroughCompactificationPtStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDegenerationDataTautologicalChartOfTraitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnifPullbackOfCanonicalOnStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMumfordFamilyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSiegelLevelStructureMumfordFamilyTautologiStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExtNormalisedBlowupStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProjOverLocallyOfFiniteType
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticCurveIsAffineAndFiniteInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRegularLocalRingAndIsRelParam
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplAtFactorOfIsAdicComplete
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDataFrom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitChartGenericFibresSameStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelAbelianLocusToroidalChartStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChartHit

theorem setup : ∀ {g n : ℕ} (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) (OZ : LB Z) (φ : InvFun ℤ) (d : ℕ) (S : Scheme.{0}) (π : S ⟶ Z) (j : F.X ⟶ S) (BD : GlobalTheory.EffCartierData S), MinAt5 F z i OZ → BlowAt F z i φ d π j BD → S.IsSeparated ∧ LocallyOfFiniteType (π ≫ z) ∧ IsLocallyNoetherian S ∧ Dense (Set.range j) ∧ j ≫ π ≫ z = F.s := by
  intro g n F Z z i OZ φ d S π j BD hMin hBlow
  obtain ⟨J, -, -, -, -, hproj, hdense, hji, -, -, -⟩ := hBlow
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, ⟨-, -, -, hiz, -⟩, -⟩ := hMin
  have hP := GlobalTheory.ArithCurve.isProper_of_projOver hproj
  have hlft : LocallyOfFiniteType (π ≫ z) := GlobalTheory.isProjOver_locallyOfFiniteType _ _ _ hproj
  haveI : IsNoetherianRing (cycAway n) := is_noetherian_subring_closure _ (Set.toFinite _)
  refine ⟨⟨by rw [← terminal.comp_from (π ≫ z)]; infer_instance⟩, hlft, LocallyOfFiniteType.isLocallyNoetherian (π ≫ z), hdense, ?_⟩
  rw [← Category.assoc, hji, hiz]

theorem away_hom_ext : ∀ (R : Type) [CommRing R] [IsDomain R] (t : R), t ≠ 0 → ∀ (l : Localization.Away t →+* FractionRing R), l.comp (algebraMap R (Localization.Away t)) = algebraMap R (FractionRing R) → ∀ (S : Scheme.{0}) [S.IsSeparated] (a b : Sp (Localization.Away t) ⟶ S), spMap l ≫ a = spMap l ≫ b → a = b := by
  intro R _ _ t ht l hl S _ a b h
  haveI : IsDomain (Localization.Away t) :=
    IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors ht)
  have hinj : Function.Injective l := by
    refine (injective_iff_map_eq_zero l).2 fun x hx => ?_
    obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers t) x
    have h1 : IsLocalization.mk' (Localization.Away t) r s * algebraMap R _ (s : R) = algebraMap R _ r :=
      IsLocalization.mk'_spec _ r s
    have h2 : algebraMap R (FractionRing R) r = 0 := by
      rw [← hl, RingHom.comp_apply, ← h1, map_mul, hx, zero_mul]
    have h3 : r = 0 := IsFractionRing.injective R (FractionRing R) (by rw [h2, map_zero])
    show IsLocalization.mk' (Localization.Away t) r s = 0
    rw [h3, IsLocalization.mk'_zero]
  have : IsDominant (spMap l) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2
    (((RingHom.injective_iff_ker_eq_bot _).1 hinj).le.trans bot_le)⟩
  exact ext_of_isDominant_of_isSeparated (terminal.from S) (terminal.hom_ext _ _) (spMap l) h

end GlobalTheory.ChartHit

namespace GlobalTheory.ChartHit

theorem lowBase_regular {n : ℕ} (L : LowBase (zetaAway n) n) : IsRegularLocalRing L.W := by
  haveI : IsNoetherianRing L.W := L.noeth
  let y := L.u (closedPoint L.W)
  let φ₀ := (Scheme.stalkClosedPointTo L.u).hom
  haveI : IsRegularLocalRing ((LowChart.powA L.F L.T.r).left.presheaf.stalk y) := LowChart.isRegularLocalRing_stalk L.F y
  have het := L.u_et
  letI : Algebra ((LowChart.powA L.F L.T.r).left.presheaf.stalk y) L.W := φ₀.toAlgebra
  haveI : Module.Flat ((LowChart.powA L.F L.T.r).left.presheaf.stalk y) L.W := het.1
  exact GlobalTheory.isRegularLocalRing_of_flat_of_map_eq_maximalIdeal _ _ (maximalIdeal _) het.2.1.symm

theorem chart : ∀ {g n : ℕ} (φ : InvFun ℤ), 3 ≤ n → ∀ (L : LowBase (zetaAway n) n) (m N : ℕ) (ε : Module.Basis (Fin m ⊕ Fin N) ℤ (balForms (id : ℤ → ℤ) (Fin L.T.r → ℤ))) (V' : Type) [CommRing V'] [IsDomain V'] [IsLocalRing V'] (κ : L.W →+* V') (s : Fin m ⊕ Fin N → V') (D' : DegData V' (maximalIdeal V')) (e : D'.toPre.X ≃+ (Fin L.T.r → ℤ)), L.h + L.T.r = g → IsCone id φ (fun k => (ε (.inl k) : LinearMap.BilinForm ℤ (Fin L.T.r → ℤ))) → (∀ x, x ≠ 0 → ∃ k, 0 < (ε (.inl k) : LinearMap.BilinForm ℤ (Fin L.T.r → ℤ)) x x) → IsCN V' → IsLocalHom κ → (∀ k, s (.inl k) ∈ maximalIdeal V' ∧ s (.inl k) ≠ 0) → (∀ k, IsUnit (s (.inr k))) → DegFrom L.T κ s (fun k => (ε k : LinearMap.BilinForm ℤ (Fin L.T.r → ℤ))) n D'.toPre e → ∃ (C : Taut (zetaAway n) g n φ) (θ : C.R →+* V') (e' : D'.toPre.X ≃+ (Fin C.T.r → ℤ)), IsLocalHom θ ∧ (∀ k, θ (C.s k) ≠ 0) ∧ θ.comp C.b = κ.comp L.T.b ∧ DegFrom C.T (θ.comp C.iw) (fun k => θ (C.s k)) C.form n D'.toPre e' := by
  intro g n φ hn L m N ε V' _ _ _ κ sv D' e hgen hcone hdef hV hκ hs1 hs2 hD
  haveI : IsRegularLocalRing L.W := lowBase_regular L
  have hψV : IsLocalHom ((MvPolynomial.eval₂Hom κ sv).comp MvPolynomial.C) := by
    rw [MvPolynomial.eval₂Hom_comp_C]; exact hκ
  obtain ⟨R, _, _, _, ψ, θ, hcompl, hθ, hθψ, hψl⟩ :=
    GlobalTheory.TChart.exists_complAt_factor_of_isAdicComplete L.W (Fin m ⊕ Fin N) V' hV.2.2.1 (MvPolynomial.eval₂Hom κ sv) hψV
  have hθX : ∀ k, θ (ψ (MvPolynomial.X k)) = sv k := fun k => by
    rw [← RingHom.comp_apply, hθψ, MvPolynomial.eval₂Hom_X']
  have hθC : θ.comp (ψ.comp MvPolynomial.C) = κ := by
    rw [← RingHom.comp_assoc, hθψ, MvPolynomial.eval₂Hom_comp_C]
  have hne : ∀ k, ψ (MvPolynomial.X k) ≠ 0 := fun k h => by
    have h' := hθX k
    rw [h, map_zero] at h'
    rcases k with k | k
    · exact (hs1 k).2 h'.symm
    · exact (hs2 k).ne_zero h'.symm
  obtain ⟨Q, eQ, hQ⟩ := GlobalTheory.TChart.FromEx.exists_dataFrom L.T (ψ.comp MvPolynomial.C) (fun k => ψ (MvPolynomial.X k))
    (fun k => (ε k : LinearMap.BilinForm ℤ (Fin L.T.r → ℤ))) n hne (fun k a b => (ε k).2.1 a b)
  have hbd : ∀ k, ψ (MvPolynomial.X (.inl k)) ∈ maximalIdeal R := fun k =>
    (IsLocalRing.mem_maximalIdeal _).2 fun hu =>
      (IsLocalRing.mem_maximalIdeal _).1 (hs1 k).1 (hθX (.inl k) ▸ hu.map θ)
  have htor : ∀ k, IsUnit (ψ (MvPolynomial.X (.inr k))) := fun k =>
    isUnit_of_map_unit θ _ (by rw [hθX]; exact hs2 k)
  let C : Taut (zetaAway n) g n φ :=
    { toLowBase := L
      genus := hgen
      m := m
      N := N
      ε := ε
      cone := hcone
      defin := hdef
      R := R
      ψ := ψ
      compl := hcompl
      ψ_loc := hψl
      bd := hbd
      tor := htor
      Q := Q
      e := eQ
      data := hQ }
  refine ⟨C, θ, e, hθ, fun k => ?_, ?_, ?_⟩
  · show θ (ψ (MvPolynomial.X k)) ≠ 0
    rw [hθX]
    rcases k with k | k
    · exact (hs1 k).2
    · exact (hs2 k).ne_zero
  · show θ.comp ((ψ.comp MvPolynomial.C).comp L.T.b) = κ.comp L.T.b
    rw [← RingHom.comp_assoc, hθC]
  · show DegFrom L.T (θ.comp (ψ.comp MvPolynomial.C)) (fun k => θ (ψ (MvPolynomial.X k)))
      (fun k => (ε k : LinearMap.BilinForm ℤ (Fin L.T.r → ℤ))) n D'.toPre e
    rw [hθC, show (fun k => θ (ψ (MvPolynomial.X k))) = sv from funext hθX]
    exact hD

end GlobalTheory.ChartHit

theorem GlobalTheory.TChart.exists_chart_at : ∀ g : ℕ, 1 ≤ g → ∀ φ : InvFun ℤ, IsPolFan id g φ → NoSelfInt id g φ → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) (OZ : LB Z) (d : ℕ) (S : Scheme.{0}) (π : S ⟶ Z) (j : F.X ⟶ S) [IsOpenImmersion j] (BD : GlobalTheory.EffCartierData S), MinAt5 F z i OZ → BlowAt F z i φ d π j BD → ∀ x : S, ∃ (C : Taut (zetaAway n) g n φ) (G₁ : Over (Sp C.R)) (_ : GrpObj G₁) (y : Sp (FractionRing C.R) ⟶ F.X) (α₁ : pullback G₁.hom (jK C.R) ⟶ F.univ.A.left) (ξ : Sp C.R ⟶ S), C.IsFam F G₁ y α₁ ∧ y ≫ j = jK C.R ≫ ξ ∧ ξ (closedPoint C.R) = x := by
  intro g hg φ hφ hns n hn hodd F Z z i OZ d S π j _ BD hMin hBlow x
  obtain ⟨hsep, hlft, hln, hdense, hjs⟩ := GlobalTheory.ChartHit.setup F Z z i OZ φ d S π j BD hMin hBlow
  obtain ⟨T, ξT, b, hx, hTj, hTb⟩ := GlobalTheory.T.exists_siegelModuli_trait_through_compactification_pt F S (π ≫ z) j hn hdense hjs x
  have hyb : T.y ≫ F.s = jK T.V ≫ spMap b := by
    rw [← hjs, ← Category.assoc, ← hTj, Category.assoc, hTb]
  obtain ⟨L, m, N, ε, V', _, _, _, f, κ, sv, D', e, G', _, _, πG, A', U', hgen, hcone, hdef, hV', hdvr, hfi, hff, hfl,
    hκl, hκb, hs1, hs2, hU, hD⟩ := GlobalTheory.T.exists_degeneration_data_tautologicalChart_of_trait g hg φ hφ n hn hodd F T b hyb
  obtain ⟨C, θ, e', hθl, hθs, hθb, hD'⟩ := GlobalTheory.ChartHit.chart φ hn L m N ε V' κ sv D' e hgen hcone hdef hV' hκl hs1 hs2 hD
  obtain ⟨G₁, _, _, P, hMP, hCan, hab, htors⟩ := GlobalTheory.T.exists_mumford_family g n φ hn hodd C
  have hle : nonZeroDivisors T.V ≤ (nonZeroDivisors V').comap f := nonZeroDivisors_le_comap_nonZeroDivisors_of_injective f hfi
  let fK : FractionRing T.V →+* FractionRing V' := IsLocalization.map (FractionRing V') f hle
  have hfK : ∀ a, fK (algebraMap T.V _ a) = algebraMap V' _ (f a) := fun a => IsLocalization.map_eq hle a
  have hprod : θ (∏ k, C.t k) ≠ 0 := by
    rw [map_prod]; exact Finset.prod_ne_zero_iff.2 fun k _ => hθs (.inl k)
  have htne : (∏ k, C.t k) ≠ 0 := fun h => hprod (by rw [h, map_zero])
  have hunit : IsUnit ((algebraMap V' (FractionRing V')).comp θ (∏ k, C.t k)) := by
    refine isUnit_iff_ne_zero.2 ?_
    simpa using (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hprod) :
      algebraMap V' (FractionRing V') (θ (∏ k, C.t k)) ≠ 0)
  let κ' : Localization.Away (∏ k, C.t k) →+* FractionRing V' := IsLocalization.Away.lift (∏ k, C.t k) hunit
  have hκ' : κ'.comp (algebraMap C.R (Localization.Away (∏ k, C.t k))) = (algebraMap V' (FractionRing V')).comp θ :=
    IsLocalization.Away.lift_comp (∏ k, C.t k) hunit
  have hSF := GlobalTheory.T.trait_chart_generic_fibres_same F C G₁ P hMP hCan T V' θ f fK hV' hθl hθs hfK D' e' hD' G' πG A' U' hU
  have hx₀ : (spMap fK ≫ T.y) ≫ F.s = spMap ((κ'.comp (algebraMap C.R (Localization.Away (∏ k, C.t k)))).comp C.b) := by
    rw [Category.assoc, hyb, hκ', RingHom.comp_assoc, hθb, hκb]
    simp only [jK, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext a
    simp [hfK]
  rw [← hκ'] at hSF
  obtain ⟨c, hc, hiso, hpt⟩ := GlobalTheory.T.exists_level_abelianLocus_toroidalChart hn hodd F C G₁ P hMP hab htors (FractionRing V') κ' (spMap fK ≫ T.y) hx₀ hSF
  obtain ⟨y, α₁, yU, l, hFam, hSPB, hl, hyl⟩ := GlobalTheory.T.exists_siegelLevelStructure_mumfordFamily_tautological g n φ hn hodd F C G₁ P hMP hab c hc hiso
  obtain ⟨ξ, hξ⟩ := GlobalTheory.T.exists_ext_normalised_blowup g hg φ hφ hns n hn hodd F Z z i OZ d S π j BD hMin hBlow C G₁ y α₁ hFam
  have hsA : spMap l ≫ spMap (algebraMap C.R (Localization.Away (∏ k, C.t k))) = jK C.R := by
    simp only [jK, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hl]
  have hyUs : yU ≫ F.s = spMap ((algebraMap C.R (Localization.Away (∏ k, C.t k))).comp C.b) := by
    refine GlobalTheory.ChartHit.away_hom_ext C.R (∏ k, C.t k) htne l hl (Sp (cycAway n)) _ _ ?_
    have h := hFam.2.2.2.2
    rw [hyl, Category.assoc] at h
    rw [h, ← hsA]
    simp only [jK, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, Category.assoc]
  have hκy := hpt yU hSPB hyUs
  have hξU : spMap (algebraMap C.R (Localization.Away (∏ k, C.t k))) ≫ ξ = yU ≫ j := by
    refine GlobalTheory.ChartHit.away_hom_ext C.R (∏ k, C.t k) htne l hl S _ _ ?_
    rw [← Category.assoc, hsA, ← hξ, hyl, Category.assoc]
  have hgen' : jK V' ≫ (spMap θ ≫ ξ) = jK V' ≫ (spMap f ≫ ξT) := by
    have e1 : jK V' ≫ spMap θ = spMap κ' ≫ spMap (algebraMap C.R (Localization.Away (∏ k, C.t k))) := by
      simp only [jK, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hκ']
    have e2 : jK V' ≫ spMap f = spMap fK ≫ jK T.V := by
      simp only [jK, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 2; ext a; simp [hfK]
    rw [← Category.assoc, e1, Category.assoc, hξU, ← Category.assoc, hκy, ← Category.assoc, e2, Category.assoc,
      Category.assoc, hTj]
  have hdom : IsDominant (jK V') := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2
    (((RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective V' (FractionRing V'))).le.trans bot_le)⟩
  have hext : spMap θ ≫ ξ = spMap f ≫ ξT :=
    ext_of_isDominant_of_isSeparated (terminal.from S) (terminal.hom_ext _ _) (jK V') hgen'
  refine ⟨C, G₁, inferInstance, y, α₁, ξ, hFam, hξ, ?_⟩
  have h1 : (spMap θ).base (closedPoint V') = closedPoint C.R := IsLocalRing.comap_closedPoint θ
  have h2 : (spMap f).base (closedPoint V') = closedPoint T.V := IsLocalRing.comap_closedPoint f
  rw [← hx, ← h1, ← h2]
  show (spMap θ ≫ ξ).base (closedPoint V') = (spMap f ≫ ξT).base (closedPoint V')
  rw [hext]
