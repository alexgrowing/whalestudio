import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormPeriodSq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockVectorIsThetaFunctionDefinitePairStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepRealFixesFockMaximalMinorsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealPointsMixMaximalMinorFockVectorsUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemL2OfContinuousAutomorphicStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralDefiniteUnitaryQuotientEqClassSumStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompAtMtOfMemGfC
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaEqZeroOfReal
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DefiniteThetaPairTermsNormsIndependentRepresenta
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.VacuumUnderAdelicPairModulusOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdealPeriodLatticeOfCurveDatum
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CmBaseFieldIntegersAndCurveIdealFacts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHermitianFormScaledCoordinateEq
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OmPureTensorOOfFinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStandardPositiveDefiniteHermitianSpaceRankStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAdelicEmbeddingStandardUnitaryGroupStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenCompactLevelOfStandardCongruenceLevelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsVolumeOneMeasureDefiniteOpenCompactStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelMeasureEqRelIndexSmulStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormScaleCurveIdealStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeckeCharacterOfThetaModelCharacterStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasInfinityExponentOfFinitePartPowerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdelicThetaReadsCurveThetaFunctionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockVacuumOfReadsGaussianEntireStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergFinitePointReadsClassicalTranslationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockVectorMinorProductOriginEqPeriodsJetStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MovedThetaFunctionsReadOfMovedVacuumReadsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDatumFinitePartMovesVacuumAsThetaModelStatement

open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsDefiniteSpace IsOpenCompactLevel)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.NormExact

theorem finsum_const_mul {α : Type*} (c : ℂ) (f : α → ℂ) : ∑ᶠ a, c * f a = c * ∑ᶠ a, f a := (mul_finsum f c).symm

theorem ofReal_finsum {α : Type*} (f : α → ℝ) : ((∑ᶠ a, f a : ℝ) : ℂ) = ∑ᶠ a, (f a : ℂ) := by
  by_cases hs : (Function.support f).Finite
  · rw [finsum_eq_sum _ hs, finsum_eq_sum_of_support_subset (s := hs.toFinset) _ (by
      intro a ha; simpa using ha)]
    push_cast; rfl
  · have hs' : ¬ (Function.support fun a => (f a : ℂ)).Finite := by
      have : (Function.support fun a => (f a : ℂ)) = Function.support f := by ext a; simp
      rwa [this]
    rw [finsum_of_infinite_support hs, finsum_of_infinite_support hs', Complex.ofReal_zero]

open Matrix in

theorem sum_norm_sq_unitary {ι : Type*} [Fintype ι] [DecidableEq ι] (U : Matrix ι ι ℂ)
    (hU : U ∈ Matrix.unitaryGroup ι ℂ) (v : ι → ℂ) :
    ∑ i, ‖∑ j, U i j * v j‖ ^ 2 = ∑ i, ‖v i‖ ^ 2 := by
  have key : star (U *ᵥ v) ⬝ᵥ (U *ᵥ v) = star v ⬝ᵥ v := by
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, ← Matrix.star_eq_conjTranspose,
      (Matrix.mem_unitaryGroup_iff').1 hU, Matrix.one_mulVec]
  apply Complex.ofReal_injective
  push_cast
  have e : ∀ w : ι → ℂ, ∑ i, ((‖w i‖ : ℂ)) ^ 2 = star w ⬝ᵥ w := fun w => by
    simp only [dotProduct, Pi.star_apply, RCLike.star_def, Complex.conj_mul']
  have e2 := e (U *ᵥ v)
  simp only [Matrix.mulVec, dotProduct] at e2
  rw [e2, e v]
  simpa [Matrix.mulVec, dotProduct] using key

end GlobalTheory.NormExact

namespace GlobalTheory.NormExact

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ t0 : ℂ} {Q : ℕ} {P : Pair D cc δ t0 Q} {X : Data P}

def IsDictWt (P : Pair D cc δ t0 Q) (X : Data P) : Prop :=
  IsDict P X ∧ ∀ τ, HasInfExp D X.χB τ (-((P.n τ : ℚ) + (P.d : ℚ) / 2))

theorem om_apply_mul (X : Data P) (g g' : GA D X.A) (h h' : GA D X.B) (f : WO X.A X.B → ℂ) :
    X.om (g * g', h * h') f = X.om (g, h) (X.om (g', h') f) := by
  have : ((g * g', h * h') : GA D X.A × GA D X.B) = (g, h) * (g', h') := rfl
  rw [this, map_mul]; rfl

theorem ker_rat (hX : IsDictWt P X) {γ : GA D X.A} (hγ : γ ∈ GQ X.A) {γ' : GA D X.B} (hγ' : γ' ∈ GQ X.B)
    (g : GA D X.A) (h : GA D X.B) (T : Tup D P.a P.d P.n) :
    thetaKO X.om (γ * g) (γ' * h) (X.fock T) = thetaKO X.om g h (X.fock T) := by
  unfold thetaKO
  rw [om_apply_mul]
  exact hX.1.2.weil.om_aut γ hγ γ' hγ' _ (hX.1.2.weil.om_pres _ _ (GlobalTheory.T.fock_vector_isThetaFunction_definite_pair P X hX.1 T))

theorem classFun_A (hX : IsDictWt P X) (h : GA D X.B) (T : Tup D P.a P.d P.n) :
    GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.IsClassFun X.A X.KA (fun g => thetaKO X.om g h (X.fock T) * (1 : GA D X.A → ℂ) g) := by
  refine ⟨fun γ hγ g => ?_, fun k hk g => ?_, fun k hk g => ?_⟩
  · simp only [Pi.one_apply, mul_one]
    have := ker_rat hX hγ (one_mem (GQ X.B)) g h T
    rwa [one_mul] at this
  · simp only [Pi.one_apply, mul_one]
    unfold thetaKO
    rw [show h = h * 1 from (mul_one h).symm, om_apply_mul, GlobalTheory.T.weilRep_real_fixes_fock_maximal_minors P X hX.1 hX.2 k hk T, mul_one]
  · simp only [Pi.one_apply, mul_one]
    obtain ⟨hk1, hk2⟩ := hk
    rw [← hX.1.1.rangeA] at hk1
    obtain ⟨k', rfl⟩ := hk1
    have hk' : k' ∈ intG D P.a := (hX.1.1.levA_iff k').1 hk2
    unfold thetaKO
    rw [show h = h * 1 from (mul_one h).symm, om_apply_mul, hX.1.2.fixA k' hk' T, mul_one]

theorem lift_classSum (hX : IsDictWt P X) (h : GA D X.B) (T : Tup D P.a P.d P.n) :
    Integrable (GlobalTheory.AutomorphicL2Unitary.descend (GQ X.A) (fun g => thetaKO X.om g h (X.fock T) * (1 : GA D X.A → ℂ) g))
      (GlobalTheory.AutomorphicL2Unitary.autMeasure X.A X.m) ∧
    X.lift T h = ∑ᶠ x : Cls D P.a (intG D P.a), ((gam D (intG D P.a) x.out : ℂ))⁻¹ *
      thetaKO X.om (X.ιA x.out) h (X.fock T) := by
  obtain ⟨𝓕, h𝓕⟩ := hX.1.1.measA
  have := GlobalTheory.T.integral_definiteUnitaryQuotient_eq_classSum X.A P.a X.ιA (intG D P.a) X.KA X.m 𝓕 hX.1.1.defA hX.1.1.injA hX.1.1.rangeA hX.1.1.ratA hX.1.1.levA
    hX.1.1.levA_iff h𝓕 _ (classFun_A hX h T)
  refine ⟨this.2.1, ?_⟩
  unfold Data.lift GlobalTheory.Core.Rk.IP.up
  rw [this.2.2]
  simp

theorem finite_cls_A (hX : IsDictWt P X) (T : Tup D P.a P.d P.n) : Finite (Cls D P.a (intG D P.a)) := by
  obtain ⟨𝓕, h𝓕⟩ := hX.1.1.measA
  exact (GlobalTheory.T.integral_definiteUnitaryQuotient_eq_classSum X.A P.a X.ιA (intG D P.a) X.KA X.m 𝓕 hX.1.1.defA hX.1.1.injA hX.1.1.rangeA hX.1.1.ratA hX.1.1.levA
    hX.1.1.levA_iff h𝓕 _ (classFun_A hX 1 T)).1

theorem continuous_lift (hX : IsDictWt P X) (T : Tup D P.a P.d P.n) : Continuous (X.lift T) := by
  haveI := finite_cls_A hX T
  haveI := Fintype.ofFinite (Cls D P.a (intG D P.a))
  have e : X.lift T = fun h => ∑ x : Cls D P.a (intG D P.a), ((gam D (intG D P.a) x.out : ℂ))⁻¹ *
      thetaKO X.om (X.ιA x.out) h (X.fock T) := by
    funext h
    rw [(lift_classSum hX h T).2, finsum_eq_sum_of_fintype]
  rw [e]
  refine continuous_finsetSum _ fun x _ => continuous_const.mul ?_
  exact (hX.1.2.weil.om_cont _ (GlobalTheory.T.fock_vector_isThetaFunction_definite_pair P X hX.1 T) 0).comp (Continuous.prodMk continuous_const continuous_id)

theorem lift_eq (hX : IsDictWt P X) (h : Formalism.MainNotions.StandardLatticesGL3.GA D P.d) (T : Tup D P.a P.d P.n) :
    X.lift T (X.ιB h) = X.c₁ * P.coord h T := by
  rw [(lift_classSum hX (X.ιB h) T).2, Pair.coord]
  simp_rw [hX.1.2.ker, ← finsum_const_mul X.c₁]
  congr 1; funext x; ring

end GlobalTheory.NormExact

namespace GlobalTheory.NormExact

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ t0 : ℂ} {Q : ℕ} {P : Pair D cc δ t0 Q} {X : Data P}

theorem lift_mul_apply (X : Data P) (T : Tup D P.a P.d P.n) (h k : GA D X.B) :
    X.lift T (h * k) = GlobalTheory.Core.Rk.IP.up X.om X.m (X.om (1, k) (X.fock T)) 1 h := by
  unfold Data.lift GlobalTheory.Core.Rk.IP.up
  congr 1; funext q
  simp only [GlobalTheory.AutomorphicL2Unitary.descend, thetaKO]
  rw [show Quotient.out q = Quotient.out q * 1 from (mul_one _).symm, om_apply_mul, mul_one]

theorem norm_lift_mul_level (hX : IsDictWt P X) {k : GA D X.B} (hk : k ∈ Lev.levA X.B X.KB) (h : GA D X.B)
    (T : Tup D P.a P.d P.n) : ‖X.lift T (h * k)‖ = ‖X.lift T h‖ := by
  obtain ⟨hk1, hk2⟩ := hk
  rw [← hX.1.1.rangeB] at hk1
  obtain ⟨j, rfl⟩ := hk1
  obtain ⟨c, hc, hcT⟩ := hX.1.2.eigB j ((hX.1.1.levB_iff j).1 hk2)
  rw [lift_mul_apply, hcT T]
  have : GlobalTheory.Core.Rk.IP.up X.om X.m (c • X.fock T) 1 h = c * X.lift T h := by
    unfold Data.lift GlobalTheory.Core.Rk.IP.up
    rw [← integral_const_mul]
    congr 1; funext q
    simp only [GlobalTheory.AutomorphicL2Unitary.descend, thetaKO, map_smul, Pi.smul_apply, smul_eq_mul]
    ring
  rw [this, norm_mul, hc, one_mul]

theorem sum_lift_mul_real (hX : IsDictWt P X) {k : GA D X.B} (hk : k ∈ GinfC X.B) (h : GA D X.B) :
    ∑ T, ‖X.lift T (h * k)‖ ^ 2 = ∑ T, ‖X.lift T h‖ ^ 2 := by
  obtain ⟨U, hU, hUT⟩ := GlobalTheory.T.realPoints_mix_maximalMinorFockVectors_unitary P X hX.1 k hk
  have e : ∀ T, X.lift T (h * k) = ∑ T', U T T' * X.lift T' h := by
    intro T
    rw [lift_mul_apply, hUT T]
    unfold Data.lift GlobalTheory.Core.Rk.IP.up
    have hi : ∀ T', Integrable (GlobalTheory.AutomorphicL2Unitary.descend (GQ X.A)
        (fun g => thetaKO X.om g h (X.fock T') * (1 : GA D X.A → ℂ) g)) (GlobalTheory.AutomorphicL2Unitary.autMeasure X.A X.m) :=
      fun T' => (lift_classSum hX h T').1
    rw [show (∑ T', U T T' * ∫ q, GlobalTheory.AutomorphicL2Unitary.descend (GQ X.A)
          (fun g => thetaKO X.om g h (X.fock T') * (1 : GA D X.A → ℂ) g) q ∂GlobalTheory.AutomorphicL2Unitary.autMeasure X.A X.m) =
        ∑ T', ∫ q, U T T' * GlobalTheory.AutomorphicL2Unitary.descend (GQ X.A)
          (fun g => thetaKO X.om g h (X.fock T') * (1 : GA D X.A → ℂ) g) q ∂GlobalTheory.AutomorphicL2Unitary.autMeasure X.A X.m from
        Finset.sum_congr rfl (fun T' _ => (integral_const_mul _ _).symm)]
    rw [← integral_finsetSum _ (fun T' _ => (hi T').const_mul (U T T'))]
    congr 1; funext q
    simp only [GlobalTheory.AutomorphicL2Unitary.descend, thetaKO, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Pi.one_apply, mul_one]
  simp_rw [e]
  exact sum_norm_sq_unitary U hU _

theorem lift_rat (hX : IsDictWt P X) {γ : GA D X.B} (hγ : γ ∈ GQ X.B) (h : GA D X.B) (T : Tup D P.a P.d P.n) :
    X.lift T (γ * h) = X.lift T h := by
  unfold Data.lift GlobalTheory.Core.Rk.IP.up
  congr 1; funext q
  simp only [GlobalTheory.AutomorphicL2Unitary.descend]
  have := ker_rat hX (one_mem (GQ X.A)) hγ (Quotient.out q) h T
  rw [one_mul] at this
  rw [this]

theorem classFun_B (hX : IsDictWt P X) :
    GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.IsClassFun X.B X.KB (fun h => ((∑ T, ‖X.lift T h‖ ^ 2 : ℝ) : ℂ)) := by
  refine ⟨fun γ hγ h => ?_, fun k hk h => ?_, fun k hk h => ?_⟩
  · simp only [lift_rat hX hγ]
  · rw [sum_lift_mul_real hX hk]
  · simp only [norm_lift_mul_level hX hk]

theorem norm_mul_eq (hX : IsDictWt P X) :
    (P.norm : ℂ) * ((‖X.c₁‖ ^ 2 : ℝ) : ℂ) =
      ∑ T, GlobalTheory.Cusp.petersson X.B X.mH (X.lift T) (X.lift T) := by
  obtain ⟨𝓕, h𝓕⟩ := hX.1.1.measB
  have hc := GlobalTheory.T.integral_definiteUnitaryQuotient_eq_classSum X.B P.d X.ιB P.J X.KB X.mH 𝓕 hX.1.1.defB hX.1.1.injB hX.1.1.rangeB hX.1.1.ratB hX.1.1.levB
    hX.1.1.levB_iff h𝓕 _ (classFun_B hX)
  have hint : ∀ T, Integrable (fun q => GlobalTheory.AutomorphicL2Unitary.descend (GQ X.B) (X.lift T) q *
      (starRingEnd ℂ) (GlobalTheory.AutomorphicL2Unitary.descend (GQ X.B) (X.lift T) q)) (GlobalTheory.AutomorphicL2Unitary.autMeasure X.B X.mH) := by
    intro T
    obtain ⟨𝓕, h𝓕⟩ := hX.1.1.measB
    have hm := (GlobalTheory.T.memL2_of_continuous_automorphic X.B X.KB X.mH 𝓕 hX.1.1.defB hX.1.1.levB h𝓕 (X.lift T) (continuous_lift hX T)
      (fun γ hγ h => lift_rat hX hγ h T)).2
    have h2 := hm.integrable_norm_pow (p := 2) (by norm_num)
    have h3 : Integrable (fun q => ((‖GlobalTheory.AutomorphicL2Unitary.descend (GQ X.B) (X.lift T) q‖ ^ 2 : ℝ) : ℂ))
        (GlobalTheory.AutomorphicL2Unitary.autMeasure X.B X.mH) := by
      have := h2.ofReal (𝕜 := ℂ)
      simpa using this
    refine h3.congr (Filter.Eventually.of_forall fun q => ?_)
    simp [Complex.mul_conj']
  have e1 : ∑ T, GlobalTheory.Cusp.petersson X.B X.mH (X.lift T) (X.lift T) =
      ∫ q, GlobalTheory.AutomorphicL2Unitary.descend (GQ X.B) (fun h => ((∑ T, ‖X.lift T h‖ ^ 2 : ℝ) : ℂ)) q
        ∂GlobalTheory.AutomorphicL2Unitary.autMeasure X.B X.mH := by
    simp only [GlobalTheory.Cusp.petersson, GlobalTheory.AutomorphicL2Unitary.pet]
    rw [← integral_finsetSum _ (fun T _ => hint T)]
    congr 1; funext q
    simp only [GlobalTheory.AutomorphicL2Unitary.descend, Complex.mul_conj']
    push_cast; rfl
  have hs : ∀ y, ∑ T, ‖X.lift T (X.ιB y)‖ ^ 2 = ‖X.c₁‖ ^ 2 * P.sq y := by
    intro y
    simp only [lift_eq hX, norm_mul, mul_pow, Pair.sq, Finset.mul_sum]
  rw [e1, hc.2.2, Pair.norm, ofReal_finsum, mul_comm, ← finsum_const_mul]
  congr 1; funext x
  rw [hs]
  push_cast; ring

end GlobalTheory.NormExact

namespace GlobalTheory.NormExact

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ t0 : ℂ} {Q : ℕ} {P : Pair D cc δ t0 Q} {X : Data P} {r : D.host.E}

theorem test_TT (P : Pair D cc δ t0 Q) : P.F ∈ TT D (tor0 D cc δ) P.a P.d :=
  GlobalTheory.NormSum.RepInv.test_mem (GlobalTheory.InducedType.induced_type D).1 P.crv P P.level_pos

theorem IsExact.reads_om (hI : GlobalTheory.NormSum.Inp D) (h : IsExact P X r) (x : Formalism.MainNotions.StandardLatticesGL3.GA D P.a) (y : Formalism.MainNotions.StandardLatticesGL3.GA D P.d)
    {G : VC D P.a P.d → ℂ} (hG : G ∈ TT D (tor0 D cc δ) P.a P.d) {f : WO X.A X.B → ℂ}
    (hf : Reads X.ψ X.θ X.rkA X.rkB cc δ r G f) :
    Reads X.ψ X.θ X.rkA X.rkB cc δ r (P.W.Om x y G) (X.om (X.ιA x, X.ιB y) f) := by
  obtain ⟨f₀, hf₀⟩ := GlobalTheory.T.exists_adelicTheta_reads_curveThetaFunction X.ψ X.θ X.A X.B X.rkA X.rkB cc δ r h.setup P.e0
    (GlobalTheory.NormSum.VacMove.vac_TT (GlobalTheory.InducedType.induced_type D).1 P.crv P.vac.1)
  have h1 := GlobalTheory.T.weil_datum_finite_part_moves_vacuum_as_theta_model X.ψ X.θ X.A X.B X.rkA X.rkB cc δ r h.setup P.e0 P.W X.χA X.χB X.om h.weil hI t0 P.pt0 P.even_mul
    P.vac h.chA h.chB x y _ _ (h.std.ptA x) (h.std.ptB y) f₀ hf₀
  have h2 := GlobalTheory.T.movedThetaFunctions_read_of_movedVacuum_reads X.ψ X.θ X.A X.B X.rkA X.rkB cc δ r h.setup P.e0 P.W X.χA X.χB X.om h.weil P.vac.1 x y _ _
    (h.std.ptA x) (h.std.ptB y) 1 f₀ hf₀ (by rwa [one_smul]) G hG f hf
  rwa [one_smul] at h2

theorem IsExact.om_fock (h : IsExact P X r) (x : Formalism.MainNotions.StandardLatticesGL3.GA D P.a) (y : Formalism.MainNotions.StandardLatticesGL3.GA D P.d) (T : Tup D P.a P.d P.n) :
    X.om (X.ιA x, X.ιB y) (X.fock T) =
      pureTensorO X.ψ X.θ X.A X.B (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 1) (X.om (X.ιA x, X.ιB y) X.vac)
        (MvPolynomial.rename X.var (minorPol D T)) :=
  GlobalTheory.OrientedHeis.om_fin_pureTensorO X.ψ X.A X.B X.χA X.χB X.om h.weil X.θ h.inf _ (h.std.ptA x).1 _ (h.std.ptB y).1
    _ _ _ _ _ _ h.read.1

theorem IsExact.norm_const (h : IsExact P X r) : ‖X.c₁‖ ^ 2 * normConst D cc δ P.a P.n = 1 := by
  have hA := area_pos P.crv
  have hp := Real.pi_pos
  rw [h.const, norm_prod, ← Finset.prod_pow, normConst, ← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one fun τ _ => ?_
  rw [norm_pow, ← pow_mul, mul_comm _ 2, pow_mul, norm_period_sq P.crv.1.1 h.scale, ← mul_pow]
  have : area (lamOf D cc δ) / Real.pi * (Real.pi / area (lamOf D cc δ)) = 1 := by field_simp
  rw [this, one_pow]

theorem normConst_pos (hc : Formalism.MainNotions.StandardLatticesGL3.Crv D cc δ) (a : ℕ) (n : D.what₂.Tau → ℕ) : 0 < normConst D cc δ a n :=
  Finset.prod_pos fun _ _ => pow_pos (div_pos Real.pi_pos (area_pos hc)) _

theorem IsExact.isDictWt (hI : GlobalTheory.NormSum.Inp D) (h : IsExact P X r) : IsDictWt P X := by
  have hF := test_TT P
  have hb : ∀ τ, HasInfExp D X.χB τ (-((P.n τ : ℚ) + (P.d : ℚ) / 2)) := fun τ => by
    have h1 := GlobalTheory.T.hasInfinityExponent_of_finitePartPower P.W.chV' (-P.W.ep') X.χB h.weil.hecT h.chB τ
    have h2 : ((2 * (P.n τ : ℤ) : ℤ) : ℚ) = ((P.W.ep' * P.W.chV'.n τ - (P.d : ℤ) : ℤ) : ℚ) := by rw [P.wt τ]
    push_cast at h1 h2
    convert h1 using 1
    linarith
  refine ⟨⟨h.std.frame, h.inf, h.weil, h.read.1,
    GlobalTheory.T.isFockVacuum_of_readsGaussianEntire X.ψ X.θ X.A X.B X.rkA X.rkB cc δ r h.setup _ _ hF.1 h.read, fun h0 => ?_, fun x y T => ?_,
    fun k hk T => ?_, fun j hj => ?_, hb⟩, hb⟩
  · have := h.norm_const
    rw [h0] at this
    simp at this
  · rw [thetaKO, h.om_fock, h.const]
    exact GlobalTheory.T.fockVector_minorProduct_origin_eq_periods_jet X.ψ X.θ X.A X.B X.rkA X.rkB cc δ r h.setup _ _ (P.W.maps x y _ hF).1 (h.reads_om hI x y hF h.read) P.n T
  · have h1 := h.reads_om hI k 1 hF h.read
    rw [P.fix k hk] at h1
    have h2 := h.om_fock k 1 T
    rw [h1.unique h.read, map_one] at h2
    exact h2
  · obtain ⟨c, hc, hcF⟩ := P.eig j hj
    refine ⟨c, hc, fun T => ?_⟩
    have h1 := h.reads_om hI 1 j hF h.read
    rw [hcF] at h1
    have h2 := h.om_fock 1 j T
    rw [h1.unique (h.read.smul c), map_one, GlobalTheory.FiniteFock.pureTensorO_smul] at h2
    exact h2

theorem IsExact.upConv (hI : GlobalTheory.NormSum.Inp D) (h : IsExact P X r) {K₀ : Subgroup (GL (Fin X.B.rank) (Lev.EAf D))}
    {μ₀ : Measure (GA D X.B)} (hm : IsMaxLevel X.toFrame K₀ μ₀) (T : Tup D P.a P.d P.n) :
    GlobalTheory.Core.Rk.IP.UpConv X.om X.m μ₀ (X.fock T) 1 := by
  have hX := h.isDictWt hI
  obtain ⟨𝓕, h𝓕⟩ := hm.meas
  exact ⟨fun y => (lift_classSum hX y T).1, GlobalTheory.T.memL2_of_continuous_automorphic X.B K₀ μ₀ 𝓕 hX.1.1.defB hm.lev h𝓕 (X.lift T) (continuous_lift hX T)
    fun γ hγ y => lift_rat hX hγ y T⟩

theorem IsExact.norm_eq (hI : GlobalTheory.NormSum.Inp D) (h : IsExact P X r) {K₀ : Subgroup (GL (Fin X.B.rank) (Lev.EAf D))}
    {μ₀ : Measure (GA D X.B)} (hm : IsMaxLevel X.toFrame K₀ μ₀) :
    (P.norm : ℂ) = (normConst D cc δ P.a P.n : ℂ) * (P.J.relIndex (intG D P.d) : ℂ) *
      ∑ T, GlobalTheory.Cusp.petersson X.B μ₀ (X.lift T) (X.lift T) := by
  have hX := h.isDictWt hI
  obtain ⟨𝓕, h𝓕⟩ := hX.1.1.measB
  obtain ⟨𝓕₀, h𝓕₀⟩ := hm.meas
  have e := GlobalTheory.T.levelMeasure_eq_relIndex_smul X.B P.d X.ιB P.J (intG D P.d) X.KB K₀ X.mH μ₀ hX.1.1.rangeB P.J_le P.idx_ne hX.1.1.levB hm.lev
    hX.1.1.levB_iff hm.mem_iff h𝓕.1 h𝓕₀.1
  have e2 : ∀ T, GlobalTheory.Cusp.petersson X.B X.mH (X.lift T) (X.lift T) =
      (P.J.relIndex (intG D P.d) : ℂ) * GlobalTheory.Cusp.petersson X.B μ₀ (X.lift T) (X.lift T) := fun T => by
    simp only [GlobalTheory.Cusp.petersson, GlobalTheory.AutomorphicL2Unitary.pet]
    rw [e, GlobalTheory.AutomorphicL2Unitary.quotMeasure_smul, integral_smul_measure]
    simp
  have e3 := norm_mul_eq hX
  have e4 : ((‖X.c₁‖ ^ 2 * normConst D cc δ P.a P.n : ℝ) : ℂ) = 1 := by rw [h.norm_const]; rfl
  simp only [e2, ← Finset.mul_sum] at e3
  push_cast at e3 e4
  linear_combination (normConst D cc δ P.a P.n : ℂ) * e3 - (P.norm : ℂ) * e4

theorem exists_stdFrame (P : Pair D cc δ t0 Q) (hJ : IsCongLevel P.J) :
    ∃ (Y : Frame P) (K₀ : Subgroup (GL (Fin Y.B.rank) (Lev.EAf D))) (μ₀ : Measure (GA D Y.B)),
      IsStdFrame P Y ∧ IsMaxLevel Y K₀ μ₀ := by
  obtain ⟨A, rA, gA, dA⟩ := GlobalTheory.T.exists_standardPositiveDefinite_hermitianSpace_rank D P.a
  obtain ⟨B, rB, gB, dB⟩ := GlobalTheory.T.exists_standardPositiveDefinite_hermitianSpace_rank D P.d
  obtain ⟨ιA, pA, iA, sA, qA⟩ := GlobalTheory.T.exists_finiteAdelicEmbedding_standardUnitaryGroup A P.a gA rA
  obtain ⟨ιB, pB, iB, sB, qB⟩ := GlobalTheory.T.exists_finiteAdelicEmbedding_standardUnitaryGroup B P.d gB rB
  obtain ⟨KA, lA, mA⟩ := GlobalTheory.T.exists_openCompactLevel_of_standardCongruenceLevel A P.a ιA _ gA pA iA sA le_rfl (isCongLevel_intG _)
  obtain ⟨KB, lB, mB⟩ := GlobalTheory.T.exists_openCompactLevel_of_standardCongruenceLevel B P.d ιB _ gB pB iB sB P.J_le hJ
  obtain ⟨K₀, l₀, m₀⟩ := GlobalTheory.T.exists_openCompactLevel_of_standardCongruenceLevel B P.d ιB _ gB pB iB sB le_rfl (isCongLevel_intG _)
  obtain ⟨μA, 𝓕A, hA⟩ := GlobalTheory.T.exists_volumeOne_measure_definite_openCompact A KA dA lA
  obtain ⟨μB, 𝓕B, hB⟩ := GlobalTheory.T.exists_volumeOne_measure_definite_openCompact B KB dB lB
  obtain ⟨μ₀, 𝓕₀, h₀⟩ := GlobalTheory.T.exists_volumeOne_measure_definite_openCompact B K₀ dB l₀
  exact ⟨⟨A, B, rA, rB, ιA, ιB, KA, KB, μA, μB⟩, K₀, μ₀,
    ⟨⟨gA, gB, dA, dB, iA, iB, sA, sB, qA, qB, lA, lB, mA, mB, hA.1.1, hB.1.1, ⟨_, hA⟩, ⟨_, hB⟩⟩, pA, pB⟩, l₀, m₀, ⟨_, h₀⟩⟩

theorem exists_isExact (P : Pair D cc δ t0 Q) (hJ : IsCongLevel P.J) :
    ∃ (X : Data P) (r : D.host.E) (K₀ : Subgroup (GL (Fin X.B.rank) (Lev.EAf D))) (μ₀ : Measure (GA D X.B)),
      IsExact P X r ∧ IsMaxLevel X.toFrame K₀ μ₀ := by
  obtain ⟨Y, K₀, μ₀, hY, hm⟩ := exists_stdFrame P hJ
  obtain ⟨ψ, hψ⟩ := GlobalTheory.StdAdelicChar.exists_isStdChar D
  obtain ⟨θ, hθ⟩ := GlobalTheory.AdelicU.exists_isInfFam D
  obtain ⟨r, hr⟩ := GlobalTheory.T.exists_normScale_curveIdeal D cc P.crv.1
  obtain ⟨χA, a1, a2, a3⟩ := GlobalTheory.T.exists_heckeCharacter_of_thetaModelCharacter P.W.chV P.W.ep P.W.ep_pm.1
  obtain ⟨χB, b1, b2, b3⟩ := GlobalTheory.T.exists_heckeCharacter_of_thetaModelCharacter P.W.chV' (-P.W.ep') (by rcases P.W.ep_pm.2 with h | h <;> simp [h])
  obtain ⟨om, hom⟩ := GlobalTheory.Unf.Inhab.exists_weil hψ Y.A Y.B a1 b1 (Y.rkA.symm ▸ a2) (Y.rkB.symm ▸ b2)
  obtain ⟨f, hf⟩ := GlobalTheory.T.exists_adelicTheta_reads_curveThetaFunction ψ θ Y.A Y.B Y.rkA Y.rkB cc δ r ⟨hψ, hθ, hY.frame.gramA, hY.frame.gramB, P.crv, hr⟩ P.F (test_TT P)
  exact ⟨⟨Y, ψ, θ, χA, χB, om, f, ∏ τ, period D δ r τ ^ (P.a * P.n τ)⟩, r, K₀, μ₀, ⟨hY, hθ, hom, a3, b3, hr, hf, rfl⟩, hm⟩

theorem isCongLevel_of_isBlockLevel {δ t0 : ℂ} {Q : ℕ} {P : Pair D ⊤ δ t0 Q} {𝔪 : Ideal (𝓞 D.host.E)} (h𝔪 : 𝔪 ≠ ⊥) {a : ℕ}
    (h : GlobalTheory.FunObj.SqNum.IsBlockLevel P 𝔪 a) : IsCongLevel P.J := by
  refine ⟨Ideal.absNorm 𝔪, Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.2 h𝔪), fun k hk hc => (h k).2 ⟨hk, fun i j hj hi => ?_⟩⟩
  obtain ⟨s, hs, e⟩ := hc i j
  have hij : i ≠ j := fun e' => by subst e'; omega
  rw [Matrix.sub_apply, Matrix.one_apply_ne hij, sub_zero] at e
  refine AddSubgroup.subset_closure ⟨(Ideal.absNorm 𝔪 : 𝓞 D.host.E), Ideal.absNorm_mem _, s, hs, ?_⟩
  rw [e]
  simp

theorem exact_dictionary (P : Pair D cc δ t0 Q) (hI : GlobalTheory.NormSum.Inp D) (hJ : IsCongLevel P.J) :
    0 < normConst D cc δ P.a P.n ∧
    (∃ (X : Data P) (r : D.host.E) (K₀ : Subgroup (GL (Fin X.B.rank) (Lev.EAf D))) (μ₀ : Measure (GA D X.B)),
      IsExact P X r ∧ IsMaxLevel X.toFrame K₀ μ₀) ∧
    ∀ (X : Data P) (r : D.host.E) (K₀ : Subgroup (GL (Fin X.B.rank) (Lev.EAf D))) (μ₀ : Measure (GA D X.B)),
      IsExact P X r → IsMaxLevel X.toFrame K₀ μ₀ →
      IsDictWt P X ∧ (∀ T, GlobalTheory.Core.Rk.IP.UpConv X.om X.m μ₀ (X.fock T) 1) ∧
      (∀ h T, X.lift T (X.ιB h) = X.c₁ * P.coord h T) ∧ ‖X.c₁‖ ^ 2 * normConst D cc δ P.a P.n = 1 ∧
      (P.norm : ℂ) = (normConst D cc δ P.a P.n : ℂ) * (P.J.relIndex (intG D P.d) : ℂ) *
        ∑ T, GlobalTheory.Cusp.petersson X.B μ₀ (X.lift T) (X.lift T) :=
  ⟨normConst_pos P.crv _ _, exists_isExact P hJ, fun _ _ _ _ h hm =>
    ⟨h.isDictWt hI, h.upConv hI hm, lift_eq (h.isDictWt hI), h.norm_const, h.norm_eq hI hm⟩⟩

end GlobalTheory.NormExact
