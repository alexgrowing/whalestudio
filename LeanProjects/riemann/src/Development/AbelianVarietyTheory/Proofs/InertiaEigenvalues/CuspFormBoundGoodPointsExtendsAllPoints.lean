import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExtIn
import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
import Formalism.LocalToGlobal.ProjectiveLattices.MulCMemSec
import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridgeU
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.EvaluationLawsGenericFramesAtlasHold
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsFiniteIntegralChartCoverFlagSpace
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsValuationSubringComapEqNonunits
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CompactifiedModuliExistenceAndModuliScheme
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.DataAtTraitsOfTraitData
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ValuationExtension
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.DvrAdmissibleBaseAndPowerSeriesEvalUniformiser
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ArcClauseClosed
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.FiniteExtensionRamificationEmbedding
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsIsArcFr
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArcFramedPointUniqueAndBaseChange
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArcFramedPointIntegralOpenDisc
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FramedPointEvalNaturalWeightScaling
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.DegenerationDataBaseChangesExistPid
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsFramedPointOfArcBaseChange
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HasSumSectionValueArcFramedPoint
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArcModelWitnessExtension
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TorusExtExponentialDerivativeBijectiveTangent
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArcLetterAnalyticVectorsIndependentBlockType
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.EqZeroOfMulEventually
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.NonemptyUnifWitnessDataOfIsUnf
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IntegralFramedPointBaseChangeStable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsProperSemiAbelianTripleOfAbelianLocusEqUnivStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralFramedPointGoodReductionDefiniteSignaturStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRefinedFlagChartIntegralPointsInOpenStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralOfIntegralAtAlgebraicPointsSmoothStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsArcDataOfBadReductionFiniteExtensionStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsConstantIntegralArcFramesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaussPointStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsComplexEmbeddingFractionFieldCdvrStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormValuesBoundedOnHolomorphicArcStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LaurentCoeffNegEqZeroOfBoundedStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsOpenImmersionJKPowerSeries
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.RelabelEmbeddingsGoodBijectiveConjCompat
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.InjectiveAlgebraMapOfDvrOfIsIntegral

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GoodTransfer

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.ArcQ GlobalTheory.Frames GlobalTheory.Reg GlobalTheory.GoodPts
open scoped LaurentSeries

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l}

theorem inV_iff (T : CDVR) (x : T.Fr) : InV T x ↔ 0 ≤ vV T.V x := by
  by_cases h0 : x = 0
  · subst h0; simp [InV, vV]
  have hne := valV_ne_zero (V := T.V) h0
  constructor
  · rintro ⟨a, rfl⟩
    have h1 : valV T.V (algebraMap T.V T.Fr a) ≤ 1 := IsDedekindDomain.HeightOneSpectrum.valuation_le_one _ a
    have h2 := (WithZero.log_le_log hne one_ne_zero).2 h1
    rw [WithZero.log_one] at h2
    unfold vV; omega
  · intro h
    have h4 : valV T.V x ≤ 1 := by
      refine (WithZero.log_le_log hne one_ne_zero).1 ?_
      rw [WithZero.log_one]
      unfold vV at h
      omega
    exact IsDiscreteValuationRing.exists_lift_of_le_one (A := T.V) (K := T.Fr) h4

theorem inV_of_overLa {K : Type} [Field K] [NumberField K] {la : HeightOneSpectrum (𝓞 K)} {T : CDVR} {io : K →+* T.Fr}
    {e : ℕ} (ho : OverLa la T.V io e) (a : (la.valuation K).valuationSubring) : InV T (io a) := by
  rw [inV_iff, ho.2]
  refine mul_nonneg (Nat.cast_nonneg e) ?_
  by_cases h0 : (a : K) = 0
  · simp [h0, vLa]
  have hne : la.valuation K (a : K) ≠ 0 := (Valuation.ne_zero_iff _).2 h0
  have h2 := (WithZero.log_le_log hne one_ne_zero).2 a.2
  rw [WithZero.log_one] at h2
  unfold vLa; omega

theorem exists_factor {A : Type} [CommRing A] (T : CDVR) (f : A →+* T.Fr) (h : ∀ a, InV T (f a)) :
    ∃ b : A →+* T.V, (algebraMap T.V T.Fr).comp b = f := by
  let j := RingEquiv.ofBijective (algebraMap T.V T.Fr).rangeRestrict
    ⟨fun a b hab => IsFractionRing.injective T.V T.Fr (congrArg Subtype.val hab),
      RingHom.rangeRestrict_surjective _⟩
  exact ⟨j.symm.toRingHom.comp (f.codRestrict _ h),
    RingHom.ext fun a => congrArg Subtype.val (j.apply_symm_apply ⟨_, h a⟩)⟩

theorem good_of_extIn {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β) {T : CDVR} {io : c.F →+* T.Fr}
    (y : IntFr Xo c T io) (h : letI := io.toAlgebra; ExtIn Y (abLocus Y.t.G) T io y.1.x) : Good y := by
  let _ := io.toAlgebra
  obtain ⟨y', z, h1, -, h3, h4⟩ := h
  obtain ⟨t, ⟨m⟩⟩ := (GlobalTheory.ModelPoints.model_points_charts E H Dw l Xo c O β Y).2.1 _ y'
  obtain ⟨t', m₁, -, m₂, -⟩ := GlobalTheory.TraitDataIntrinsic.exists_generic Y m h3
  have hab : abLocus t.G = Set.univ := Set.eq_univ_of_forall fun p =>
    (abLocus_pullback abLocusOne Y.t.semi m.cart.1 p).1 (h4 ⟨_, rfl⟩)
  have hp := GlobalTheory.T.isProper_semiAbelian_triple_of_abelianLocus_eq_univ E H Dw l Xo T _ t t' m₂ m₁ hab
  exact ⟨t, t', h1 ▸ m₂, m₁, hp⟩

theorem inV_of_frBor {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {f : Rul Xo c} (hf : f ∈ sec Xo c a n) {T : CDVR}
    {io : c.F →+* T.Fr} (y y' : IntFr Xo c T io) (t : Ix Dw → T.Frˣ)
    (h : letI := io.toAlgebra; FrBor t y.1 y'.1) : InV T (evI y f) ↔ InV T (evI y' f) := by
  obtain ⟨hE, hU, -⟩ := GlobalTheory.Reg.evLaws_genFr_atlas E H Dw l Xo c
  have h1 := unitIndep_of hE.wt hU a n f hf T io y y' t h 1
  have key : ∀ x : T.Fr, InV T x ↔ 0 ≤ nval T.V 1 x := fun x => by
    by_cases h0 : x = 0
    · subst h0; simp [nval_zero, InV]
    · rw [nval_of_ne h0, inV_iff, EReal.coe_nonneg]; simp
  rw [key, key, h1]

theorem inV_of_extIn (la : HeightOneSpectrum (𝓞 c.F)) (Y : Model Xo c (la.valuation c.F).valuationSubring.subtype)
    (hP : PushInvertible Y.t.G Y.t.PP.L) (hop : IsOpen (abLocus Y.t.G)) {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {f : Rul Xo c}
    (hf : f ∈ sec Xo c a n) (hb : BddGood Xo c la 1 f) {T : CDVR} {io : c.F →+* T.Fr} {e : ℕ} (ho : OverLa la T.V io e)
    (y : IntFr Xo c T io) (h : letI := io.toAlgebra; ExtIn Y (abLocus Y.t.G) T io y.1.x) : InV T (evI y f) := by
  let _ := io.toAlgebra
  obtain ⟨hE, hU, -⟩ := GlobalTheory.Reg.evLaws_genFr_atlas E H Dw l Xo c
  have hev := GlobalTheory.ArcQ.evR_natural_weight_scaling E H Dw l Xo c hE a n f hf
  obtain ⟨J, _, P, hC⟩ := GlobalTheory.Reg.exists_finite_pchart_cover GlobalTheory.abelianSchemeLaws_all.2.secTwist E H Dw l Xo c hE.bc
    (la.valuation c.F).valuationSubring Y hP
  let W : ValuationSubring T.Fr := (valV T.V).valuationSubring
  have hW : ∀ x, x ∈ W ↔ InV T x := fun x =>
    ⟨fun h => IsDiscreteValuationRing.exists_lift_of_le_one (A := T.V) (K := T.Fr) h,
      by rintro ⟨a, rfl⟩; exact IsDedekindDomain.HeightOneSpectrum.valuation_le_one _ a⟩
  obtain ⟨j, e₀, he₀, ψ, z, t, hg, hz, ht⟩ := hC T.Fr W (fun a => (hW _).2 (inV_of_overLa ho a)) y.1
  obtain ⟨P', e', he', ψ', hg', hz', hall⟩ := GlobalTheory.T.exists_refined_flagChart_integral_points_in_open E H Dw l Xo c (la.valuation c.F).valuationSubring Y
    (abLocus Y.t.G) (P j) T io hop e₀ he₀ ψ z (fun g hgg => (hW _).1 (hg g hgg)) hz (ht.1 ▸ h)
  have hzI : Integral T io z := P'.int e' he' T io ψ' (inV_of_overLa ho) hg' z hz'
  rw [inV_of_frBor hf y ⟨z, hE.test _ z, hzI⟩ t ht]
  show InV T (evR Xo c f z)
  rw [(hev _).1 _ ψ' _ _ hz']
  refine GlobalTheory.T.integral_of_integral_at_algebraic_points_smooth c.F P'.Ω la P'.gens e' P'.frac (P'.es_mem e' he').1 (P'.es_mem e' he').2 (P'.sm e' he')
    (evR Xo c f (P'.y e' he')) (fun T₁ io₁ n₁ ho₁ hfin ψ₁ hk hg₁ => ?_) T io e ho ψ'.toRingHom ψ'.commutes hg'
  let _ := io₁.toAlgebra
  let φ : P'.R e' →ₐ[c.F] T₁.Fr := ⟨ψ₁, hk⟩
  obtain ⟨z₁, hz₁⟩ := hE.bc _ _ φ (P'.y e' he')
  let y₁ : IntFr Xo c T₁ io₁ := ⟨z₁, hE.test _ z₁, P'.int e' he' T₁ io₁ φ (inV_of_overLa ho₁) hg₁ z₁ hz₁⟩
  have h1 := hb T₁ io₁ n₁ ho₁ y₁ hfin (good_of_extIn Y y₁ (hall T₁ io₁ (inV_of_overLa ho₁) φ z₁ hg₁ hz₁))
  rw [map_one, one_mul] at h1
  have h2 : evI y₁ f = φ (evR Xo c f (P'.y e' he')) := (hev _).1 _ φ _ _ hz₁
  rw [h2] at h1
  exact h1

theorem exists_model (hr : 1 ≤ Dw.p + Dw.q) (Xo : Moduli Dw l) (c : Coeff l) (la : HeightOneSpectrum (𝓞 c.F)) (p : ℕ)
    (hp : p.Prime) (hpl : (p : 𝓞 c.F) ∈ la.asIdeal) (hg : l.GoodAt p) :
    ∃ Y : Model Xo c (la.valuation c.F).valuationSubring.subtype, PushInvertible Y.t.G Y.t.PP.L ∧
      IsOpen (abLocus Y.t.G) ∧ Y.SplitFibres ∧ Y.N3 ∧ Y.N4 := by
  classical
  obtain ⟨hP, hN⟩ := GlobalTheory.Moduli.jointExistence_and_moduliScheme
  let Xf : ∀ l' : Level H, Moduli Dw l' := fun l' =>
    if h : l' = l then h ▸ Xo else Classical.choice (hN E H Dw l' hr)
  have hX : Xf l = Xo := by simp [Xf]
  obtain ⟨Y, hY, -⟩ := hP.2 E H Dw hr Xf
  obtain ⟨W, hWe, hWn⟩ := exists_valuationSubring_comap_eq_nonunits c.F.val.toRingHom
    (la.valuation c.F).valuationSubring
  have hpU : (p : c.F) ∈ (la.valuation c.F).valuationSubring.nonunits := by
    rw [ValuationSubring.mem_nonunits_iff,
      ← (Valuation.isEquiv_valuation_valuationSubring (la.valuation c.F)).lt_one_iff_lt_one]
    have := (la.valuation_lt_one_iff_mem (K := c.F) (p : 𝓞 c.F)).2 hpl
    simpa using this
  have hW : (p : ℂ) ∈ W.nonunits := by simpa using hWn _ hpU
  have h := (hY p W hp hW).1.1 ⟨l, c, hg⟩
  obtain ⟨U, hU, -⟩ := h.2.2.2.1
  have h' : ∃ Y : Model (Xf l) c (c.V W).subtype, PushInvertible Y.t.G Y.t.PP.L ∧
      IsOpen (abLocus Y.t.G) ∧ Y.SplitFibres ∧ Y.N3 ∧ Y.N4 :=
    ⟨_, h.2.2.1, hU ▸ U.isOpen, (hY p W hp hW).2 ⟨l, c, hg⟩⟩
  have he : c.V W = (la.valuation c.F).valuationSubring := hWe
  rw [he, hX] at h'
  exact h'

theorem sp_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : B →+* C) (g : A →+* B) :
    spMap f ≫ spMap g = spMap (f.comp g) := (Spec.map_comp _ _).symm

theorem mem_of_pow_mem {F : Type} [Field F] (V : ValuationSubring F) {x : F} {n : ℕ} (hn : n ≠ 0) (h : x ^ n ∈ V) :
    x ∈ V := by
  rw [← ValuationSubring.valuation_le_one_iff] at h ⊢
  rw [map_pow] at h
  exact (pow_le_one_iff hn).1 h

theorem exists_values (c : Coeff l) (V : ValuationSubring c.F) :
    ∃ r z : V, ((V.subtype r : c.F) : ℂ) = H.rt0 ∧ ((V.subtype z : c.F) : ℂ) = zeta l.A := by
  let inc := (IntermediateField.inclusion c.le).toRingHom
  refine ⟨⟨inc (baseKA l).ρ, mem_of_pow_mem V two_ne_zero ?_⟩,
    ⟨inc (baseKA l).ζ, mem_of_pow_mem V l.A_pos.ne' ?_⟩, rfl, rfl⟩
  · rw [← map_pow, (baseKA l).ρ_sq, map_neg, map_natCast]
    exact neg_mem (natCast_mem V _)
  · rw [← map_pow, (baseKA l).ζ_prim.pow_eq_one, map_one]
    exact one_mem V

theorem coeff_neg_eq_zero {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ r)
    (hU : ∀ σ', Formalism.L2.PjFree.GoodEmb c σ' → Formalism.L2.PjFree.IsUnf (U σ')) (σ : c.F →+* ℂ)
    (hσ : Formalism.L2.PjFree.GoodEmb c σ) {V : ValuationSubring c.F} (Y : Model Xo c V.subtype)
    (a : ArcIn Dw l V.subtype ℂ (σ.comp V.subtype)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : Wit Y a χ)
    (hP : PushInvertible Y.t.G Y.t.PP.L)
    (hover : χ ≫ Y.s = spMap (PowerSeries.C (R := ℂ)) ≫ spMap (σ.comp V.subtype))
    (hgen : ∀ x : Sp (PowerSeries ℂ), PowerSeries.X ∉ x.asIdeal → χ x ∈ Set.range Y.j)
    (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR ℂ)) (th : a.D₀.P.L.Sec) (hth : ThNZ th)
    (htan : ∀ τ k, GtTanR (e τ k)) [Algebra c.F ℂ⸨X⸩]
    (halg : ∀ x : c.F, algebraMap c.F ℂ⸨X⸩ x = HahnSeries.ofPowerSeries ℤ ℂ (PowerSeries.C (R := ℂ) (σ x)))
    (y : FrPt Xo c ℂ⸨X⸩) (hy : IsArcFr W e th (HahnSeries.ofPowerSeries ℤ ℂ) y)
    {a' : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {f : Rul Xo c} (hd : Dom a' n) (hf : f ∈ Formalism.L2.PjFree.cusp Xo c U a' n) :
    ∀ m : ℤ, m < 0 → (evR Xo c f y).coeff m = 0 := by
  let _ : Algebra (FractionRing ℂ) ℂ := FractionRing.liftAlgebra ℂ ℂ
  have : IsScalarTower ℂ (FractionRing ℂ) ℂ := FractionRing.isScalarTower_liftAlgebra ℂ ℂ
  obtain ⟨h1, h2⟩ := GlobalTheory.abelianSchemeLaws_all
  obtain ⟨hE, -⟩ := GlobalTheory.Reg.evLaws_genFr_atlas E H Dw l Xo c
  have hY : Mono Y.j := GlobalTheory.ThetaShiftProofs.mono_j Y (mono_spMap_subtype _)
  obtain ⟨Uw⟩ := nonempty_unfWit_of_isUnf E H Dw l Xo c σ r (U σ) (hU σ hσ)
  have hty := (GlobalTheory.Relab.relab_good E H l c _ hσ).2.2.2 Dw Uw.g Uw.e
  obtain ⟨Ha⟩ := GlobalTheory.arcClause_closed E H Dw l Xo c _ _ Y σ a χ W Uw.g _ Uw.F hσ hty (exists_values c V) hover hgen
  obtain ⟨Θ⟩ := GlobalTheory.ArcTheta.nonempty_thetaDat h1 h2 E H Dw l Xo c σ _ _ Y a χ W _ _ Uw.F Ha hty th hth
  obtain ⟨v₁, -⟩ := GlobalTheory.ExpTan.anVec_bijective h1.globalFns E H Dw l Xo c σ _ _ Y a χ W _ _ Uw.F Ha
  choose z hz using fun τ i => (v₁ (e τ i) (htan τ i)).exists
  have hzt := GlobalTheory.ArcType.main h1 h2 E H Dw l Xo c σ r (U σ) Uw _ _ Y a χ W Ha y e th z hσ halg hY hy hz
  obtain ⟨T₁, hT₁⟩ := GlobalTheory.ArcQ.hasSum_evR_arc h1 h2 E H Dw l Xo c σ _ _ Y a χ W _ _ Uw.F Ha y e th Θ z hE halg hover
    (mono_spMap_subtype _) hP hth hy hz
  obtain ⟨T₂, C, hT₂⟩ := GlobalTheory.T.cuspForm_values_bounded_on_holomorphicArc E H Dw l Xo c r U σ Uw _ _ Y a χ W Ha th Θ z hU hσ hzt a' n f hd hf
  refine GlobalTheory.T.laurent_coeff_neg_eq_zero_of_bounded' _ (max Ha.T (max T₁ T₂)) C fun w hw => ?_
  obtain ⟨yw, hyw, -⟩ := GlobalTheory.ArcQ.AnFrEx.existsUnique_anFr h1 h2 E H Dw l Xo c σ r (U σ) Uw _ _ Y a χ W Ha th Θ z hσ hzt
    w ((le_max_left _ _).trans_lt hw)
  exact ⟨_, hT₁ w (((le_max_left _ _).trans (le_max_right _ _)).trans_lt hw) yw hyw a' n f hf.1,
    hT₂ w (((le_max_right _ _).trans (le_max_right _ _)).trans_lt hw) yw hyw⟩

theorem exists_lift {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β) {S : Type} [CommRing S]
    (w : Sp S ⟶ Y.X) (k : c.F →+* S) (hw : w ≫ Y.s = spMap (k.comp β)) (hr : Set.range w ⊆ abLocus Y.t.G) :
    ∃ z : Sp S ⟶ Xo.XF c, z ≫ Y.j = w ∧ z ≫ pullback.snd _ _ = spMap k := by
  let u : Sp S ⟶ pullback Y.s (spMap β) := pullback.lift w (spMap k) (hw.trans (sp_comp _ _).symm)
  have := Y.jQ_open
  have hu : Set.range u ⊆ Set.range Y.jQ := by
    rw [← Y.ab_gen]
    rintro _ ⟨x, rfl⟩
    refine hr ⟨x, ?_⟩
    rw [← Scheme.Hom.comp_apply, pullback.lift_fst]
  refine ⟨IsOpenImmersion.lift Y.jQ u hu, ?_, ?_⟩
  · rw [Model.j, ← Category.assoc, IsOpenImmersion.lift_fac, pullback.lift_fst]
  · rw [← Y.jQ_over, ← Category.assoc, IsOpenImmersion.lift_fac, pullback.lift_snd]

theorem snd_eq {V : ValuationSubring c.F} (Y : Model Xo c V.subtype) {S : Type} [CommRing S] (z : Sp S ⟶ Xo.XF c)
    (k : c.F →+* S) (h : z ≫ Y.j ≫ Y.s = spMap (k.comp V.subtype)) : z ≫ pullback.snd _ _ = spMap k := by
  have := mono_spMap_subtype V
  rw [← cancel_mono (spMap V.subtype), Category.assoc, ← GlobalTheory.TraitDataIntrinsic.j_s Y, h, sp_comp]

theorem flat_of_injective (T : CDVR) {S : Type} [CommRing S] [IsDomain S] (g : T.V →+* S) (hg : Function.Injective g) :
    g.Flat := by
  let _ := g.toAlgebra
  have : FaithfulSMul T.V S := (faithfulSMul_iff_algebraMap_injective T.V S).2 hg
  show Module.Flat T.V S
  infer_instance

theorem exists_value {V : ValuationSubring c.F} (Y : Model Xo c V.subtype) (T : CDVR) (io : c.F →+* T.Fr)
    (b : V →+* T.V) (a : ArcIn Dw l V.subtype T.V b) (χ : Sp (PowerSeries T.V) ⟶ Y.X) (W : Wit Y a χ) (ϖ : T.V)
    (hϖ : Irreducible ϖ) (hP : PushInvertible Y.t.G Y.t.PP.L) (hb : (algebraMap T.V T.Fr).comp b = io.comp V.subtype)
    (hover : χ ≫ Y.s = spMap (PowerSeries.C (R := T.V)) ≫ spMap b)
    (hab : ∀ x : Sp (PowerSeries T.V), χ x ∈ abLocus Y.t.G ↔ PowerSeries.X ∉ x.asIdeal)
    (ρ : (E →+* ℂ) → (𝓞 E →+* T.V)) (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR T.V))
    (th : a.D₀.P.L.Sec) (he : ArcBasis W ρ e) (hth : ThNZ th)
    (hρ : ∀ τ x, io (embK c τ x) = algebraMap T.V T.Fr (ρ τ x))
    {a' : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {f : Rul Xo c} (hf : f ∈ sec Xo c a' n) :
    ∃ (h : PowerSeries T.V) (N : ℕ), ∀ (L : Type) [CommRing L] [Algebra c.F L] (ω : PowerSeries T.V →+* L)
      (j : T.Fr →+* L), IsUnit (ω (PowerSeries.C ϖ * PowerSeries.X)) →
      (∀ x, j (algebraMap T.V T.Fr x) = ω (PowerSeries.C x)) → (∀ x, algebraMap c.F L x = j (io x)) →
      ∃ y : FrPt Xo c L, IsArcFr W e th ω y ∧ evR Xo c f y * ω ((PowerSeries.C ϖ * PowerSeries.X) ^ N) = ω h := by
  obtain ⟨h1, h2⟩ := GlobalTheory.abelianSchemeLaws_all
  obtain ⟨hE, -⟩ := GlobalTheory.Reg.evLaws_genFr_atlas E H Dw l Xo c
  have hY : Mono Y.j := GlobalTheory.ThetaShiftProofs.mono_j Y (mono_spMap_subtype _)
  let d : PowerSeries T.V := PowerSeries.C ϖ * PowerSeries.X
  have hd : d ≠ 0 := mul_ne_zero (fun h => hϖ.ne_zero (PowerSeries.C_injective (h.trans (map_zero _).symm)))
    PowerSeries.X_ne_zero
  have hle : Submonoid.powers d ≤ nonZeroDivisors _ := powers_le_nonZeroDivisors_of_noZeroDivisors hd
  let S := Localization.Away d
  have : IsDomain S := IsLocalization.isDomain_localization hle
  let ι : PowerSeries T.V →+* S := algebraMap _ _
  have hι : Function.Injective ι := IsLocalization.injective S hle
  have hud : IsUnit (ι d) := IsLocalization.Away.algebraMap_isUnit d
  have huϖ : IsUnit (ι (PowerSeries.C ϖ)) := by
    rw [map_mul] at hud; exact isUnit_of_mul_isUnit_left hud
  have huX : IsUnit (ι PowerSeries.X) := by
    rw [map_mul] at hud; exact isUnit_of_mul_isUnit_right hud
  have hun : ∀ x : nonZeroDivisors T.V, IsUnit ((ι.comp (PowerSeries.C (R := T.V))) x) := fun x => by
    obtain ⟨m, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (nonZeroDivisors.ne_zero x.2) hϖ
    rw [hu, map_mul, map_pow]
    exact (u.isUnit.map _).mul (huϖ.pow m)
  let k : T.Fr →+* S := IsLocalization.lift hun
  have hk : ∀ x, k (algebraMap T.V T.Fr x) = ι (PowerSeries.C x) := IsLocalization.lift_eq hun
  let _ : Algebra c.F S := (k.comp io).toAlgebra
  obtain ⟨z, hz, hz'⟩ := exists_lift Y (spMap ι ≫ χ) (k.comp io) (by
      rw [Category.assoc, hover, sp_comp, sp_comp, RingHom.comp_assoc, ← hb]
      exact congrArg spMap (RingHom.ext fun x => (hk _).symm)) (by
      rintro _ ⟨x, rfl⟩
      rw [Scheme.Hom.comp_apply, hab]
      exact fun hx => x.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ (show ι PowerSeries.X ∈ x.asIdeal from hx) huX))
  have hflat : (ι.comp (PowerSeries.C (R := T.V))).Flat := flat_of_injective T _ (hι.comp PowerSeries.C_injective)
  obtain ⟨yS, -, hyS⟩ := GlobalTheory.ArcQ.exists_isArcFr h1 h2 E H Dw l Xo c _ _ Y T.V b a χ W ρ e th he hth (Or.inr hP) S ι z
    hflat hz (by rw [pullback.condition, ← Category.assoc, hz', sp_comp]; rfl)
    (fun τ x => (congrArg k (hρ τ x)).trans (hk _))
  obtain ⟨⟨h, s, N, rfl⟩, hs⟩ := IsLocalization.surj (Submonoid.powers d) (evR Xo c f yS)
  refine ⟨h, N, fun L _ _ ω j hω hj hc => ?_⟩
  let φ₀ : S →+* L := IsLocalization.Away.lift d hω
  have hφ₀ : ∀ s, φ₀ (ι s) = ω s := IsLocalization.Away.lift_eq d hω
  have hkj : φ₀.comp k = j := IsLocalization.ringHom_ext (nonZeroDivisors T.V)
    (RingHom.ext fun x => ((congrArg φ₀ (hk x)).trans (hφ₀ _)).trans (hj x).symm)
  let φ : S →ₐ[c.F] L := ⟨φ₀, fun x => (RingHom.congr_fun hkj (io x)).trans (hc x).symm⟩
  obtain ⟨y, hy⟩ := hE.bc _ _ φ yS
  have h₀ := (GlobalTheory.ArcQ.isArcFr_unique_baseChange h1 h2 E H Dw l Xo c _ _ Y T.V b a χ W e th hth S ι yS hyS).2 hY
    L φ y hy
  have e₀ : φ.toRingHom.comp ι = ω := RingHom.ext hφ₀
  rw [e₀] at h₀
  refine ⟨y, h₀, ?_⟩
  rw [(GlobalTheory.ArcQ.evR_natural_weight_scaling E H Dw l Xo c hE a' n f hf S).1 L φ yS y hy, ← hφ₀, ← hφ₀]
  exact (map_mul φ₀ _ _).symm.trans (congrArg φ₀ hs)

theorem pow_dvd_of_map {R S : Type} [CommRing R] [CommRing S] [IsDomain S] (ev : R →+* S) {p : R} (hp : ev p ≠ 0)
    (h : ∀ s, ev p ∣ ev s → p ∣ s) : ∀ (N : ℕ) (s : R), ev p ^ N ∣ ev s → p ^ N ∣ s := by
  intro N
  induction N with
  | zero => intro s _; simp
  | succ N ih =>
    intro s hs
    obtain ⟨s', rfl⟩ := h s ((dvd_pow_self _ N.succ_ne_zero).trans hs)
    rw [map_mul, pow_succ', mul_dvd_mul_iff_left hp] at hs
    rw [pow_succ']
    exact mul_dvd_mul_left _ (ih s' hs)

theorem X_pow_dvd {A : Type} [CommRing A] (κ : A →+* ℂ) (hκ : Function.Injective κ) (F : ℂ⸨X⸩)
    (hF : ∀ m : ℤ, m < 0 → F.coeff m = 0) (a : A) (h : PowerSeries A) (N : ℕ)
    (e : F * HahnSeries.ofPowerSeries ℤ ℂ (PowerSeries.map κ ((PowerSeries.C a * PowerSeries.X) ^ N)) =
      HahnSeries.ofPowerSeries ℤ ℂ (PowerSeries.map κ h)) : PowerSeries.X ^ N ∣ h := by
  rw [PowerSeries.X_pow_dvd_iff]
  intro m hm
  apply hκ
  have e1 : HahnSeries.ofPowerSeries ℤ ℂ (PowerSeries.map κ ((PowerSeries.C a * PowerSeries.X) ^ N)) =
      HahnSeries.single (N : ℤ) (κ a ^ N) := by
    rw [map_pow, map_mul, PowerSeries.map_C, PowerSeries.map_X, map_pow, map_mul, HahnSeries.ofPowerSeries_C,
      HahnSeries.ofPowerSeries_X, HahnSeries.C_apply, HahnSeries.single_mul_single, HahnSeries.single_pow]
    simp
  have e2 := congrArg (fun G : ℂ⸨X⸩ => G.coeff (((m : ℤ) - N) + N)) e
  simp only [e1, HahnSeries.coeff_mul_single_add] at e2
  rw [hF _ (by omega), zero_mul, sub_add_cancel, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map] at e2
  rw [← e2, map_zero]

theorem inV_of_arc {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (hU : ∀ σ, GoodEmb c σ → IsUnf (U σ))
    (la : HeightOneSpectrum (𝓞 c.F)) (Y : Model Xo c (la.valuation c.F).valuationSubring.subtype)
    (hP : PushInvertible Y.t.G Y.t.PP.L) (hop : IsOpen (abLocus Y.t.G)) (h4 : Y.N4)
    {a' : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {f : Rul Xo c} (hd : Dom a' n) (hf : f ∈ cusp Xo c U a' n)
    (hbd : BddGood Xo c la 1 f) {T : CDVR} {io : c.F →+* T.Fr} {m : ℕ} (ho : OverLa la T.V io m) (hfin : T.FinRes)
    (b : (la.valuation c.F).valuationSubring →+* T.V)
    (hb : (algebraMap T.V T.Fr).comp b = io.comp (la.valuation c.F).valuationSubring.subtype)
    (ϖ : T.V) (hϖ : Irreducible ϖ) (a : ArcIn Dw l (la.valuation c.F).valuationSubring.subtype T.V b)
    (y' : Sp T.V ⟶ Y.X) (hy' : y' ≫ Y.s = spMap b)
    (hA : Y.HasArcData a (Ideal.span {ϖ}) (RingHom.id T.V) ϖ y') (y : IntFr Xo c T io) (z : Sp T.Fr ⟶ Xo.XF c)
    (hz₁ : letI := io.toAlgebra; z ≫ pullback.fst _ _ = y.1.x) (hz₂ : z ≫ pullback.snd _ _ = spMap io)
    (hz₃ : z ≫ Y.j = spMap (algebraMap T.V T.Fr) ≫ y') : InV T (evI y f) := by
  let _ := io.toAlgebra
  obtain ⟨h1, h2, -, hL4, hL5⟩ := GlobalTheory.firstFiveLaws
  obtain ⟨hE, -⟩ := GlobalTheory.Reg.evLaws_genFr_atlas E H Dw l Xo c
  have hY : Mono Y.j := GlobalTheory.ThetaShiftProofs.mono_j Y (mono_spMap_subtype _)
  have hcpl : IsAdicComplete (Ideal.span {ϖ}) T.V := hϖ.maximalIdeal_eq ▸ T.cpl
  obtain ⟨χ, hχ, hsp⟩ := h4 T.V b ϖ a (Or.inr ⟨inferInstance, hϖ, hcpl⟩)
  obtain ⟨hover, hab, hopen, hW⟩ := (hχ χ).1 rfl
  obtain ⟨W⟩ := (Y.hasArcData_iff a _ _ _ χ).1 hW
  obtain ⟨-, -, ev, hevC, hevX, -⟩ := GlobalTheory.UniformiserEval.dvr_admissibleBase_and_powerSeries_evalUniformiser T.V ϖ hϖ T.cpl
  have hχy : spMap ev ≫ χ = y' := hsp hϖ y' ev hy' (by
    rintro _ ⟨x, rfl⟩
    exact ⟨z x, by rw [← Scheme.Hom.comp_apply, hz₃]⟩) hA hevC hevX
  obtain ⟨ρ, e, th, y₀, t, he, hth, htan, hρ, hy₀, ht⟩ := GlobalTheory.T.exists_constant_integral_arc_frames E H Dw l Xo c _ Y T io b a χ W ev z hP hb hover
    hevC hz₂ (by rw [hz₃, ← hχy, ← Category.assoc, sp_comp]) y.1 hz₁
  obtain ⟨h, N, hval⟩ := exists_value Y T io b a χ W ϖ hϖ hP hb hover hab ρ e th he hth hρ hf.1

  have hX : PowerSeries.X ^ N ∣ h := by
    obtain ⟨κ, hκ⟩ := GlobalTheory.T.exists_complex_embedding_fractionField_cdvr c.F c.F.val.toRingHom T hfin io
    let κ₀ : T.V →+* ℂ := κ.comp (algebraMap T.V T.Fr)
    have hκ₀ : Function.Injective κ₀ := κ.injective.comp (IsFractionRing.injective T.V T.Fr)
    have hb' : c.F.val.toRingHom.comp (la.valuation c.F).valuationSubring.subtype = κ₀.comp b := by
      rw [RingHom.comp_assoc, hb, ← RingHom.comp_assoc, hκ]
    obtain ⟨⟨a₁, p, hp⟩, hbc⟩ := GlobalTheory.ArcQBC.baseChanges h1 h2 hL4.unifBaseChange hL5 E H Dw l Xo c _ _ Y T.V ℂ b a κ₀
      hκ₀ _ hb'
    obtain ⟨hW₁, hlet, htn, hthx, hnz⟩ := hbc a₁ p hp
    obtain ⟨W₁, hW₁⟩ := hW₁ χ W
    choose e₁ he₁ using fun τ k => (hlet (e τ k)).exists
    obtain ⟨th₁, hth₁⟩ := (hthx th).exists
    let cL : ℂ →+* ℂ⸨X⸩ := (HahnSeries.ofPowerSeries ℤ ℂ).comp (PowerSeries.C (R := ℂ))
    let _ : Algebra c.F ℂ⸨X⸩ := (cL.comp c.F.val.toRingHom).toAlgebra
    have hϖ0 : κ₀ ϖ ≠ 0 := fun h0 => hϖ.ne_zero (hκ₀ (h0.trans (map_zero _).symm))
    obtain ⟨yC, hyC, hv⟩ := hval ℂ⸨X⸩ ((HahnSeries.ofPowerSeries ℤ ℂ).comp (PowerSeries.map κ₀)) (cL.comp κ) (by
        rw [isUnit_iff_ne_zero, RingHom.comp_apply, map_ne_zero_iff _ HahnSeries.ofPowerSeries_injective, map_mul,
          PowerSeries.map_C, PowerSeries.map_X]
        exact mul_ne_zero (fun h => hϖ0 (PowerSeries.C_injective (h.trans (map_zero _).symm))) PowerSeries.X_ne_zero)
      (fun x => by simp [cL, κ₀]) (fun x => congrArg cL (RingHom.congr_fun hκ x).symm)
    have hyC₁ := GlobalTheory.ArcQ.isArcFr_witBC h1 h2 E H Dw l Xo c _ _ Y T.V b a χ W ℂ _ a₁ κ₀ p W₁ hY hp hW₁ e e₁ th th₁ he₁
      hth₁ _ _ yC hyC
    refine X_pow_dvd κ₀ hκ₀ _ (coeff_neg_eq_zero (fun σ => Formalism.L2.PjFree.Unf.ofPj (U σ)) hU c.F.val.toRingHom rfl Y a₁ _
      W₁ hP ?_ (fun x hx => ?_) e₁ th₁ (hnz _ _ hth₁ hth) (fun τ k => htn _ _ (he₁ τ k) (htan τ k)) (fun _ => rfl) yC
      hyC₁ hd hf) ϖ h N hv
    · rw [Category.assoc, hover, sp_comp, sp_comp, sp_comp, hb']
      exact congrArg spMap (RingHom.ext fun x => PowerSeries.map_C κ₀ (b x))
    · rw [Scheme.Hom.comp_apply]
      refine hopen _ fun hm => ?_
      have hm' : PowerSeries.map κ₀ (PowerSeries.C ϖ * PowerSeries.X) ∈ x.asIdeal := hm
      rw [map_mul, PowerSeries.map_C, PowerSeries.map_X] at hm'
      exact hx ((Ideal.unit_mul_mem_iff_mem _ ((IsUnit.mk0 _ hϖ0).map _)).1 hm')
  obtain ⟨h₁, rfl⟩ := hX

  have hG : PowerSeries.C ϖ ^ N ∣ h₁ := by
    obtain ⟨T', ω, i, hω, hωX, hωd, hi, hv'⟩ := GlobalTheory.T.exists_gaussPoint' T ϖ hϖ
    have hinj := IsFractionRing.injective T'.V T'.Fr
    have hω0 : ω (PowerSeries.C ϖ) ≠ 0 := fun h0 =>
      hϖ.ne_zero (PowerSeries.C_injective ((hω (h0.trans (map_zero _).symm)).trans (map_zero _).symm))
    let _ := (i.comp io).toAlgebra
    obtain ⟨yG, hyG, hv⟩ := hval T'.Fr ((algebraMap T'.V T'.Fr).comp ω) i (by
        rw [isUnit_iff_ne_zero, RingHom.comp_apply, map_ne_zero_iff _ hinj, map_mul]
        exact mul_ne_zero hω0 hωX.ne_zero) hi (fun _ => rfl)
    have hint := GlobalTheory.ArcQ.integral_of_isArcFr h1 h2 E H Dw l Xo c _ _ Y T.V b a χ W ρ e th he hth hP T' (i.comp io) ω
      (hω.comp PowerSeries.C_injective) (fun τ x => (congrArg i (hρ τ x)).trans (hi _)) yG hyG
    obtain ⟨zG, -, -, -, -, k₁, k₂, -⟩ := id hyG
    have ho' : OverLa la T'.V (i.comp io) (1 * m) := ho.bc i one_pos fun x => by rw [hv', Nat.cast_one, one_mul]
    obtain ⟨x, hx⟩ := inV_of_extIn la Y hP hop hf.1 hbd ho' ⟨yG, hE.test _ yG, hint⟩
      ⟨spMap ω ≫ χ, zG, k₂, snd_eq Y zG _ (by
        rw [← Category.assoc, k₁, Category.assoc, hover, sp_comp, sp_comp, RingHom.comp_assoc _ io, ← hb]
        exact congrArg spMap (RingHom.ext fun x => (hi _).symm)),
       by rw [k₁, ← Category.assoc, sp_comp], by
        rintro _ ⟨x, rfl⟩
        rw [Scheme.Hom.comp_apply, hab]
        exact fun hx => x.isPrime.ne_top
          (Ideal.eq_top_of_isUnit_mem _ (show ω PowerSeries.X ∈ x.asIdeal from hx) hωX)⟩
    have hx' : algebraMap T'.V T'.Fr x = evR Xo c f yG := hx
    rw [← hx', RingHom.comp_apply, RingHom.comp_apply, ← map_mul] at hv
    have hv₁ := hinj hv
    refine pow_dvd_of_map ω hω0 hωd N h₁ ⟨x, mul_left_cancel₀ (pow_ne_zero N hωX.ne_zero) ?_⟩
    simp only [map_mul, map_pow, mul_pow] at hv₁
    rw [← hv₁]; ring
  obtain ⟨h₂, rfl⟩ := hG

  have hinj := IsFractionRing.injective T.V T.Fr
  have hne : (algebraMap T.V T.Fr).comp ev (PowerSeries.C ϖ * PowerSeries.X) ≠ 0 := by
    rw [RingHom.comp_apply, map_ne_zero_iff _ hinj, map_mul, hevC, hevX]
    exact mul_ne_zero hϖ.ne_zero hϖ.ne_zero
  obtain ⟨y₁, hy₁, hv⟩ := hval T.Fr ((algebraMap T.V T.Fr).comp ev) (RingHom.id _) (isUnit_iff_ne_zero.2 hne)
    (fun x => by rw [RingHom.comp_apply, hevC]; rfl) (fun _ => rfl)
  obtain rfl : y₁ = y₀ := (GlobalTheory.ArcQ.isArcFr_unique_baseChange h1 h2 E H Dw l Xo c _ _ Y T.V b a χ W e th hth _ _ y₀
    hy₀).1 hY y₁ hy₁
  have hint := GlobalTheory.ArcQ.integral_of_isArcFr h1 h2 E H Dw l Xo c _ _ Y T.V b a χ W ρ e th he hth hP T io ev
    (fun x x' hx => (hevC x).symm.trans (hx.trans (hevC x'))) (fun τ x => by rw [hevC]; exact hρ τ x) y₁ hy₁
  rw [← inV_of_frBor hf.1 ⟨y₁, hE.test _ y₁, hint⟩ y t ht]
  refine ⟨ev h₂, mul_right_cancel₀ (pow_ne_zero N hne) ?_⟩
  rw [← map_pow]
  refine Eq.trans ?_ hv.symm
  simp only [RingHom.comp_apply, map_mul, map_pow, mul_pow]
  ring

theorem bddAll_one {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (hU : ∀ σ, GoodEmb c σ → IsUnf (U σ))
    (la : HeightOneSpectrum (𝓞 c.F)) (p : ℕ) (hp : p.Prime) (hpl : (p : 𝓞 c.F) ∈ la.asIdeal) (hg : l.GoodAt p)
    {a' : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {f : Rul Xo c} (hd : Dom a' n) (hf : f ∈ cusp Xo c U a' n)
    (hbd : BddGood Xo c la 1 f) : BddAll Xo c la 1 f := by
  intro T io m ho y hy
  by_cases hq : Dw.q = 0
  · exact hbd T io m ho y hy (GlobalTheory.T.integral_framed_point_good_reduction_definite_signature E H Dw l Xo c hq T io y)
  obtain ⟨Y, hP, hop, hS, h3, h4⟩ := exists_model (by omega) Xo c la p hp hpl hg
  let _ := io.toAlgebra
  obtain ⟨b, hb⟩ := exists_factor T (io.comp (la.valuation c.F).valuationSubring.subtype) (inV_of_overLa ho)
  let z : Sp T.Fr ⟶ Xo.XF c := pullback.lift y.1.x (spMap io) (y.1.x_over.trans (sp_comp _ _).symm)
  have hz₁ : z ≫ pullback.fst _ _ = y.1.x := pullback.lift_fst _ _ _
  have hz₂ : z ≫ pullback.snd _ _ = spMap io := pullback.lift_snd _ _ _
  obtain ⟨⟨y', ⟨hy', hz₃⟩, -⟩, -⟩ := GlobalTheory.ValuativeExtension.valuation_extension E H Dw l Xo c _ _ Y T.V T.Fr b io z hb hz₂
  by_cases hr : Set.range y' ⊆ abLocus Y.t.G
  · exact hbd T io m ho y hy (good_of_extIn Y y ⟨y', z, hz₁, hz₂, hz₃.symm, hr⟩)
  obtain ⟨T', g, ϖ, a, hg₁, hg₂, hϖ, hA⟩ := GlobalTheory.T.exists_arcData_of_badReduction_finiteExtension E H Dw l Xo c _ Y h3 hS T io b y' z hb hy' hz₂ hz₃.symm hr
  obtain ⟨i, ρ, hρ, hi, hv, -⟩ := GlobalTheory.EtaVal.finite_extension_ramification_embedding T T' g hg₁ hg₂
  have hfin : T'.FinRes := by
    let _ := g.toAlgebra
    have : Module.Finite T.V T'.V := hg₂
    exact (GlobalTheory.dvr_finite_over_complete_dvr T.V T'.V).2.2.2.2 hy
  obtain ⟨y₁, φ, hφ, hy₁⟩ := GlobalTheory.IntFrBaseChange.exists_intFr_baseChange E H Dw l Xo c T T' io y i ρ hρ
    (fun x _ => hv x)
  let _ := (i.comp io).toAlgebra
  have e₁ : (algebraMap T'.V T'.Fr).comp g = i.comp (algebraMap T.V T.Fr) := RingHom.ext fun x => (hi x).symm
  have key := inV_of_arc U hU la Y hP hop h4 hd hf hbd (ho.bc i hρ hv) hfin (g.comp b)
    (by rw [← RingHom.comp_assoc, e₁, RingHom.comp_assoc, hb]; rfl) ϖ hϖ a (spMap g ≫ y')
    (by rw [Category.assoc, hy', sp_comp]) hA y₁ (spMap i ≫ z)
    (by rw [Category.assoc, hz₁, hy₁.1, hφ]) (by rw [Category.assoc, hz₂, sp_comp])
    (by rw [Category.assoc, ← hz₃, ← Category.assoc, ← Category.assoc, sp_comp, sp_comp, e₁])
  obtain ⟨hE, -⟩ := GlobalTheory.Reg.evLaws_genFr_atlas E H Dw l Xo c
  have e₂ : evI y₁ f = φ (evI y f) :=
    (GlobalTheory.ArcQ.evR_natural_weight_scaling E H Dw l Xo c hE a' n f hf.1 T.Fr).1 _ φ _ _ hy₁
  have e₃ : φ (evI y f) = i (evI y f) := RingHom.congr_fun hφ _
  rw [e₂, e₃, inV_iff, hv] at key
  rw [map_one, one_mul, inV_iff]
  exact nonneg_of_mul_nonneg_right key (by exact_mod_cast hρ)

theorem bddAll_of_bddGood : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r), (∀ σ, GoodEmb c σ → IsUnf (U σ)) → ∀ (la : HeightOneSpectrum (𝓞 c.F)) (p : ℕ), p.Prime → (p : 𝓞 c.F) ∈ la.asIdeal → l.GoodAt p → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Rul Xo c) (κ : c.F), Dom a n → f ∈ cusp Xo c U a n → BddGood Xo c la κ f → BddAll Xo c la κ f := by
  intro E _ _ _ H Dw l Xo c r U hU la p hp hpl hg a n f κ hd hf hb T io m ho y hy
  have h := bddAll_one U hU la p hp hpl hg hd (Submodule.smul_mem _ κ hf)
    (fun T io m ho y hy hgood => by rw [map_one, one_mul, evI_smul]; exact hb T io m ho y hy hgood) T io m ho y hy
  rwa [map_one, one_mul, evI_smul] at h

end GlobalTheory.GoodTransfer
