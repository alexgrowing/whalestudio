import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatIntegrableAaVacOfConductor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemValuationEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteCoefficientBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearCombinationLogBoundRealInequality
import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.RamBasic
import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
import Formalism.LocalToGlobal.ProjectiveLattices.HostInt
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicUnitaryLatticeSelfDualTraceForm
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ModelLatIn

noncomputable section

namespace GlobalTheory.ScalAA

open IsDedekindDomain NumberField
open Formalism.DivisionValues (vw lw)

section Abstract

variable {K : Type} [Field K] [NumberField K]

theorem vw_mul' (w : HeightOneSpectrum (𝓞 K)) {a b : K} (ha : a ≠ 0) (hb : b ≠ 0) :
    vw w (a * b) = vw w a + vw w b := by
  unfold vw
  rw [← FractionalIdeal.spanSingleton_mul_spanSingleton, FractionalIdeal.count_mul K w
    (FractionalIdeal.spanSingleton_ne_zero_iff.2 ha) (FractionalIdeal.spanSingleton_ne_zero_iff.2 hb)]

theorem vw_inv' (w : HeightOneSpectrum (𝓞 K)) (a : K) : vw w a⁻¹ = - vw w a := by
  unfold vw
  rw [← FractionalIdeal.spanSingleton_inv, FractionalIdeal.count_inv]

theorem vw_pow' (w : HeightOneSpectrum (𝓞 K)) {a : K} (ha : a ≠ 0) : ∀ k : ℕ, vw w (a ^ k) = k * vw w a
  | 0 => by simp [vw, FractionalIdeal.spanSingleton_one, FractionalIdeal.count_one]
  | k + 1 => by
    rw [pow_succ, vw_mul' w (pow_ne_zero _ ha) ha, vw_pow' w ha k]; push_cast; ring

theorem vw_zpow' (w : HeightOneSpectrum (𝓞 K)) {a : K} (ha : a ≠ 0) (n : ℤ) : vw w (a ^ n) = n * vw w a := by
  rcases Int.eq_nat_or_neg n with ⟨k, rfl | rfl⟩
  · rw [zpow_natCast, vw_pow' w ha]
  · rw [zpow_neg, zpow_natCast, vw_inv', vw_pow' w ha]; ring

theorem vw_prod' (w : HeightOneSpectrum (𝓞 K)) {ι : Type} (P : Finset ι) (f : ι → K) (hf : ∀ i ∈ P, f i ≠ 0) :
    vw w (∏ i ∈ P, f i) = ∑ i ∈ P, vw w (f i) := by
  classical
  induction P using Finset.induction_on with
  | empty => simp [vw, FractionalIdeal.spanSingleton_one, FractionalIdeal.count_one]
  | insert j P hj ih =>
    rw [Finset.prod_insert hj, Finset.sum_insert hj,
      vw_mul' w (hf j (Finset.mem_insert_self _ _)) (Finset.prod_ne_zero_iff.2 fun i hi => hf i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => hf i (Finset.mem_insert_of_mem hi)]

theorem vw_natCast_nonneg' (w : HeightOneSpectrum (𝓞 K)) (q : ℕ) : 0 ≤ vw w (q : K) := by
  have e : (q : K) = algebraMap (𝓞 K) K (q : 𝓞 K) := by simp
  unfold vw
  rw [e, ← FractionalIdeal.coeIdeal_span_singleton]
  exact FractionalIdeal.count_coe_nonneg K w _

theorem loss_sqrt_prod {ι : Type} (P : Finset ι) (q : ι → ℕ) (hq : ∀ i ∈ P, q i ≠ 0) (s : ι → K)
    (hs : ∀ i ∈ P, s i ^ 2 = (q i : K)) (n : ι → ℤ) :
    ∃ dl : HeightOneSpectrum (𝓞 K) → ℝ, (∀ w, 0 ≤ dl w) ∧ {w | dl w ≠ 0}.Finite ∧
      (∀ T : Finset (HeightOneSpectrum (𝓞 K)), ∑ w ∈ T, lw w * dl w ≤ ∑ i ∈ P, |(n i : ℝ)| * (Real.log (q i) / 2)) ∧
      ∀ w, -(dl w) ≤ (vw w (∏ i ∈ P, s i ^ n i) : ℝ) := by
  classical
  have hs0 : ∀ i ∈ P, s i ≠ 0 := fun i hi h => by
    have := hs i hi
    rw [h, zero_pow two_ne_zero] at this
    exact hq i hi (by exact_mod_cast this.symm)
  have hv2 : ∀ w, ∀ i ∈ P, 2 * vw w (s i) = vw w (q i : K) := fun w i hi => by
    rw [← hs i hi, sq, vw_mul' w (hs0 i hi) (hs0 i hi)]; ring
  have hv0 : ∀ w, ∀ i ∈ P, (0 : ℝ) ≤ vw w (s i) := fun w i hi => by
    have h1 := vw_natCast_nonneg' w (q i) (K := K)
    have h2 := hv2 w i hi
    have : 0 ≤ vw w (s i) := by omega
    exact_mod_cast this
  refine ⟨fun w => ∑ i ∈ P, |(n i : ℝ)| * vw w (s i), fun w => Finset.sum_nonneg fun i hi => mul_nonneg (abs_nonneg _) (hv0 w i hi),
    ?_, fun T => ?_, fun w => ?_⟩
  · refine (P.finite_toSet.biUnion fun i _ => Filter.eventually_cofinite.1
      (FractionalIdeal.finite_factors (K := K) (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (s i)))).subset
      fun w hw => ?_
    by_contra h
    refine hw (Finset.sum_eq_zero fun i hi => ?_)
    have : vw w (s i) = 0 := by
      by_contra h'
      exact h (Set.mem_biUnion hi h')
    simp [this]
  · have e : ∑ w ∈ T, lw w * ∑ i ∈ P, |(n i : ℝ)| * vw w (s i) =
        ∑ i ∈ P, |(n i : ℝ)| * ((∑ w ∈ T, lw w * (vw w ((q i : ℕ) : K) : ℝ)) / 2) := by
      simp only [Finset.mul_sum, Finset.sum_div]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun w _ => ?_
      have : (vw w ((q i : ℕ) : K) : ℝ) = 2 * vw w (s i) := by rw [← hv2 w i hi]; push_cast; ring
      rw [this]; ring
    rw [e]
    refine Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    have := @Formalism.EigenvalueLevelCeiling.sum_lw_vw_natCast_le K _ _ starRingOfComm T (q i) (hq i hi)
    linarith
  · rw [vw_prod' w P _ fun i hi => zpow_ne_zero _ (hs0 i hi)]
    push_cast
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum fun i hi => ?_
    rw [vw_zpow' w (hs0 i hi)]
    push_cast
    have h1 := hv0 w i hi
    have h2 : -|(n i : ℝ)| ≤ (n i : ℝ) := neg_abs_le _
    nlinarith

theorem norm_sqrt_prod {ι : Type} (P : Finset ι) (q : ι → ℕ) (hq : ∀ i ∈ P, q i ≠ 0) (s : ι → K)
    (hs : ∀ i ∈ P, s i ^ 2 = (q i : K)) (n : ι → ℤ) (σ : K →+* ℂ) :
    ‖σ (∏ i ∈ P, s i ^ n i)‖ ≤ Real.exp (∑ i ∈ P, |(n i : ℝ)| * (Real.log (q i) / 2)) := by
  have hn : ∀ i ∈ P, ‖σ (s i)‖ = Real.sqrt (q i) := fun i hi => by
    have h1 : ‖σ (s i)‖ ^ 2 = (q i : ℝ) := by
      rw [← norm_pow, ← map_pow, hs i hi, map_natCast, Complex.norm_natCast]
    rw [← h1, Real.sqrt_sq (norm_nonneg _)]
  rw [map_prod, norm_prod, Real.exp_sum]
  refine Finset.prod_le_prod (fun i _ => norm_nonneg _) fun i hi => ?_
  have hq1 : (1 : ℝ) ≤ q i := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (hq i hi)
  have hpos : 0 < Real.sqrt (q i) := Real.sqrt_pos.2 (by linarith)
  rw [map_zpow₀, norm_zpow, hn i hi]
  have e : Real.sqrt (q i) ^ n i = Real.exp ((n i : ℝ) * (Real.log (q i) / 2)) := by
    rw [← Real.rpow_intCast, Real.rpow_def_of_pos hpos, Real.log_sqrt (by linarith)]
    ring_nf
  rw [e, Real.exp_le_exp]
  have hl : 0 ≤ Real.log (q i) / 2 := by have := Real.log_nonneg hq1; linarith
  exact mul_le_mul_of_nonneg_right (le_abs_self _) hl

end Abstract

end GlobalTheory.ScalAA

noncomputable section

namespace GlobalTheory.ScalAA

open IsDedekindDomain NumberField Formalism.BasicNotions
open Formalism.DivisionValues (vw lw)
open scoped nonZeroDivisors Pointwise

section IdealSum

variable {E : Type} [Field E] [NumberField E]

theorem vw_int_nonneg' (w : HeightOneSpectrum (𝓞 E)) (z : 𝓞 E) : 0 ≤ vw w (z : E) := by
  unfold vw
  rw [show (z : E) = algebraMap (𝓞 E) E z from rfl, ← FractionalIdeal.coeIdeal_span_singleton]
  exact FractionalIdeal.count_coe_nonneg E w _

theorem sum_count_log_le (I : Ideal (𝓞 E)) (hI : I ≠ 0) (S : Finset (HeightOneSpectrum (𝓞 E))) :
    ∑ w ∈ S, (FractionalIdeal.count E w (I : FractionalIdeal (𝓞 E)⁰ E) : ℝ) * Real.log (Ideal.absNorm w.asIdeal) ≤
      Real.log (Ideal.absNorm I) := by
  classical
  set c : HeightOneSpectrum (𝓞 E) → ℕ := fun w => (Associates.mk w.asIdeal).count (Associates.mk I).factors with hcdef
  have hc : ∀ w, FractionalIdeal.count E w (I : FractionalIdeal (𝓞 E)⁰ E) = c w := fun w => FractionalIdeal.count_coe E w hI
  set f : HeightOneSpectrum (𝓞 E) → ℕ := fun w => Ideal.absNorm w.asIdeal ^ c w with hf
  have hprod : ∏ᶠ w, f w = Ideal.absNorm I := by
    have := map_finprod (Ideal.absNorm (S := 𝓞 E)).toMonoidHom (Ideal.hasFiniteMulSupport hI)
    rw [Ideal.finprod_heightOneSpectrum_factorization hI] at this
    simpa [HeightOneSpectrum.maxPowDividing, hf, hcdef] using this.symm
  have hfin : (Function.mulSupport f).Finite := by
    refine (Filter.eventually_cofinite.1 (FractionalIdeal.finite_factors (K := E) (I : FractionalIdeal (𝓞 E)⁰ E))).subset
      fun w hw => ?_
    intro h0
    apply hw
    have : c w = 0 := by have := hc w; rw [h0] at this; exact_mod_cast this.symm
    simp [hf, this]
  have hN : ∀ w : HeightOneSpectrum (𝓞 E), 0 < Ideal.absNorm w.asIdeal := fun w =>
    Nat.pos_of_ne_zero fun h => w.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  have hI0 : 0 < Ideal.absNorm I := Nat.pos_of_ne_zero fun h => hI (Ideal.absNorm_eq_zero_iff.1 h)
  have hsub : Function.mulSupport f ⊆ ((S ∪ hfin.toFinset : Finset _) : Set _) := fun w hw => by
    simp only [Finset.coe_union, Set.Finite.coe_toFinset, Set.mem_union]
    exact Or.inr hw
  have hdvd : ∏ w ∈ S, f w ∣ Ideal.absNorm I := by
    rw [← hprod, finprod_eq_prod_of_mulSupport_subset f hsub]
    exact Finset.prod_dvd_prod_of_subset _ _ _ Finset.subset_union_left
  have hle : ((∏ w ∈ S, f w : ℕ) : ℝ) ≤ (Ideal.absNorm I : ℝ) := by exact_mod_cast Nat.le_of_dvd hI0 hdvd
  have hpos : (0 : ℝ) < ((∏ w ∈ S, f w : ℕ) : ℝ) := by
    exact_mod_cast Finset.prod_pos fun w _ => pow_pos (hN w) _
  have e : Real.log ((∏ w ∈ S, f w : ℕ) : ℝ) =
      ∑ w ∈ S, (FractionalIdeal.count E w (I : FractionalIdeal (𝓞 E)⁰ E) : ℝ) * Real.log (Ideal.absNorm w.asIdeal) := by
    push_cast
    rw [Real.log_prod fun w _ => by
      show ((f w : ℕ) : ℝ) ≠ 0
      simp only [hf]
      exact_mod_cast (pow_pos (hN w) (c w)).ne']
    refine Finset.sum_congr rfl fun w _ => ?_
    simp only [hf]
    push_cast
    rw [Real.log_pow, hc w]; push_cast; ring
  rw [← e]
  exact Real.log_le_log hpos hle

end IdealSum

section Host

variable (D : D7)

theorem sum_abs_count_AA_le (hcc : D.host.ccK = ⊤) (S : Finset (HeightOneSpectrum (𝓞 D.host.E))) :
    ∑ w ∈ S, ((|FractionalIdeal.count D.host.E w D.host.AA| + |FractionalIdeal.count D.host.E w D.host.AAbar| : ℤ) : ℝ) *
      Real.log (Ideal.absNorm w.asIdeal) ≤ Real.log |(discr D.host.E : ℝ)| := by
  classical
  have hP := Formalism.IndefR.Fin.factPrincipalDatum D.R D.host
  have hξ := Formalism.L2.Pj.cmHost_imaginaryGenerator_ne_zero Formalism.IndefR.Fin.factPrincipalDatum D
  have hA := Formalism.L2.Pj.AA_ne_zero Formalism.IndefR.Fin.factPrincipalDatum D
  have hB := GlobalTheory.Member.LatSelfDual.AAbar_ne_zero D
  have hdI : (D.host.ddE : Ideal (𝓞 D.host.E)) ≠ 0 := by
    intro h
    have := NumberField.absNorm_differentIdeal D.host.E (𝓞 D.host.E)
    rw [show differentIdeal ℤ (𝓞 D.host.E) = D.host.ddE from rfl, h, map_zero] at this
    exact discr_ne_zero D.host.E (Int.natAbs_eq_zero.1 this.symm)
  have hd : ((D.host.ddE : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ≠ 0 := by
    rwa [ne_eq, FractionalIdeal.coeIdeal_eq_zero]
  have hs : FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ D.host.xi0 ≠ 0 := FractionalIdeal.spanSingleton_ne_zero_iff.2 hξ
  have key : ∀ w : HeightOneSpectrum (𝓞 D.host.E),
      vw w D.host.xi0 + FractionalIdeal.count D.host.E w D.host.AA + FractionalIdeal.count D.host.E w D.host.AAbar +
        FractionalIdeal.count D.host.E w (D.host.ddE : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) = 0 := fun w => by
    have := congrArg (FractionalIdeal.count D.host.E w) hP
    rwa [FractionalIdeal.count_mul _ _ (mul_ne_zero (mul_ne_zero hs hA) hB) hd,
      FractionalIdeal.count_mul _ _ (mul_ne_zero hs hA) hB, FractionalIdeal.count_mul _ _ hs hA,
      FractionalIdeal.count_one] at this
  have hxi : ∀ w, vw w D.host.xi0 ≤ 0 := fun w => by
    have e : D.host.xi0⁻¹ = -((Ideal.absNorm D.host.ccK : D.host.E) * D.host.sqrtMinusD) := by
      simp [Formalism.BasicNotions.Host.xi0, neg_div, one_div]
    have hi : IsIntegral ℤ D.host.xi0⁻¹ := by
      rw [e]; exact ((isIntegral_natCast _).mul (Formalism.L2.Pj.sqrtMinusD_isIntegral D)).neg
    have h1 := vw_int_nonneg' w ⟨_, hi⟩
    have h2 := vw_inv' w D.host.xi0⁻¹
    rw [inv_inv] at h2
    change 0 ≤ vw w D.host.xi0⁻¹ at h1
    omega
  have hAle : ∀ w, FractionalIdeal.count D.host.E w D.host.AA ≤ 0 := fun w => by
    simp only [Formalism.BasicNotions.Host.AA, Formalism.BasicNotions.Host.AA0, Formalism.BasicNotions.Host.ccE, hcc, Ideal.map_top, FractionalIdeal.coeIdeal_top,
      one_mul, FractionalIdeal.count_inv, neg_nonpos]
    exact FractionalIdeal.count_coe_nonneg _ _ _
  have hBle : ∀ w, FractionalIdeal.count D.host.E w D.host.AAbar ≤ 0 := fun w => by
    have ht : (D.host.conj • D.host.ccE : Ideal (𝓞 D.host.E)) = ⊤ := by
      rw [Formalism.BasicNotions.Host.ccE, hcc, Ideal.map_top]
      first | rw [Ideal.pointwise_smul_def, Ideal.map_top] | simp [Ideal.pointwise_smul_def] | rfl
    simp only [Formalism.BasicNotions.Host.AAbar, ht, FractionalIdeal.coeIdeal_top, one_mul, FractionalIdeal.count_inv, neg_nonpos]
    exact FractionalIdeal.count_coe_nonneg _ _ _
  have hterm : ∀ w ∈ S, ((|FractionalIdeal.count D.host.E w D.host.AA| + |FractionalIdeal.count D.host.E w D.host.AAbar| : ℤ) : ℝ) *
      Real.log (Ideal.absNorm w.asIdeal) ≤
      (FractionalIdeal.count D.host.E w ((D.host.ddE : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) : ℝ) *
        Real.log (Ideal.absNorm w.asIdeal) := fun w _ => by
    refine mul_le_mul_of_nonneg_right ?_ (Real.log_natCast_nonneg _)
    have h1 := key w
    have h2 := hxi w
    rw [abs_of_nonpos (hAle w), abs_of_nonpos (hBle w)]
    exact_mod_cast (by omega)
  refine (Finset.sum_le_sum hterm).trans ((sum_count_log_le _ hdI S).trans (le_of_eq ?_))
  rw [show D.host.ddE = differentIdeal ℤ (𝓞 D.host.E) from rfl, NumberField.absNorm_differentIdeal D.host.E (𝓞 D.host.E),
    Nat.cast_natAbs, Int.cast_abs]

end Host

end GlobalTheory.ScalAA

noncomputable section

namespace GlobalTheory.ScalAA

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.RowTest
open Formalism.DivisionValues (vw lw)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw
  GlobalTheory.FunObj.borelSpaceKw

section Scalar

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) {U : Set T}

theorem sAA_eq_prod (S : GridChoice W U) (s : Pl D.host.E → D.what₂.LL)
    (hs : ∀ w ∈ S.PA, D.what₂.embLL (s w) = ((Real.sqrt (Ideal.absNorm w.asIdeal) : ℝ) : ℂ)) :
    ∃ n : Pl D.host.E → ℤ, (∀ w, |n w| ≤ 16 * ((D.R.m : ℤ) ^ 3 * (bigN D : ℤ) ^ 2 *
      (|FractionalIdeal.count D.host.E w D.host.AA| + |FractionalIdeal.count D.host.E w D.host.AAbar|))) ∧
      D.what₂.embLL (∏ w ∈ S.PA, s w ^ n w) = S.sAA := by
  classical
  have h := fun w => aaScalar_eq_pow W w (hasConductor_psiAt_AA W w)
  choose n hn hb using h
  refine ⟨n, hb, ?_⟩
  rw [map_prod, GridChoice.sAA]
  refine Finset.prod_congr rfl fun w hw => ?_
  rw [map_zpow₀, hs w hw, hn w, ResidueCardinalityNilpotence.GlobalTheory.CompanionTheory.ResCardPlace.resCard_Kw]
  have hq : (0 : ℝ) ≤ (Ideal.absNorm w.asIdeal : ℝ) := Nat.cast_nonneg _
  rw [← Complex.ofReal_zpow, Real.sqrt_eq_rpow, ← Real.rpow_intCast, ← Real.rpow_mul hq, Complex.ofReal_cpow hq]
  push_cast
  ring_nf

end Scalar

end GlobalTheory.ScalAA

noncomputable section

namespace GlobalTheory.ScalAA

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.RowTest
open Formalism.DivisionValues (vw lw)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw
  GlobalTheory.FunObj.borelSpaceKw

section Core

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

theorem log_discr_le {large₂ : SizeData₂ D} {F : Face D A} (s : HidaSetting large₂ R F) :
    Real.log |(discr D.host.E : ℝ)| ≤ D.R.f * large₂.sc.L / 50 := by
  obtain ⟨-, -, h4f, h44, -, -, -, -, -, hrd, hcond, -, -, -⟩ := s.size
  have hd : (0 : ℝ) < |(discr D.host.E : ℝ)| := abs_pos.2 (by exact_mod_cast discr_ne_zero D.host.E)
  have hfr := ReciprocityTheory.ChartRestriction.G.PullbackSections.MLI.finrank_E D
  have hf : (1 : ℝ) ≤ D.R.f := by
    have : 1 ≤ D.R.f := le_trans (Nat.one_le_pow _ _ (by omega)) h4f
    exact_mod_cast this
  have e : Real.log D.host.rdE = Real.log |(discr D.host.E : ℝ)| / (2 * D.R.f) := by
    rw [Formalism.BasicNotions.Host.rdE, Real.log_rpow hd, hfr]; push_cast; ring
  have h1 := hrd.trans hcond
  rw [e, div_le_iff₀ (by positivity)] at h1
  nlinarith

set_option maxHeartbeats 1000000 in

theorem core {large₂ : SizeData₂ D} {F : Face D A} (s : HidaSetting large₂ R F) (ch : Choice R) (hF : ch.FieldOK) {C : ℝ} (hC : 2 ≤ C) :
    FinScalAt ch C large₂.sc.b ∧ InfScalAt ch C large₂.sc.b := by
  classical
  have hdisc := log_discr_le s
  obtain ⟨-, -, h4f, h44, -, hbig, -, -, -, -, -, -, -, hcc⟩ := s.size
  have hroot : ∀ w ∈ ch.S.PA, ∃ y : D.what₂.LL, D.what₂.embLL y = ((Real.sqrt (Ideal.absNorm w.asIdeal) : ℝ) : ℂ) :=
    fun w hw => hF.sqrt w (Or.inl hw)
  choose! r hr using hroot
  obtain ⟨n, hnb, hy⟩ := sAA_eq_prod ch.W ch.S.toGridChoice r hr
  have hq : ∀ w ∈ ch.S.PA, Ideal.absNorm w.asIdeal ≠ 0 := fun w _ h => w.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  have hr2 : ∀ w ∈ ch.S.PA, r w ^ 2 = ((Ideal.absNorm w.asIdeal : ℕ) : D.what₂.LL) := fun w hw =>
    D.what₂.embLL.injective (by
      rw [map_pow, hr w hw, map_natCast, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
      push_cast; rfl)
  set X : ℝ := ∑ w ∈ ch.S.PA, |(n w : ℝ)| * (Real.log (Ideal.absNorm w.asIdeal : ℕ) / 2) with hX
  have hL0 : 0 ≤ large₂.sc.L := Real.rpow_nonneg (by linarith [large₂.sc.one_lt_alt]) _
  have hlogb : Real.log large₂.sc.b = large₂.sc.L := Real.log_exp _

  set M : ℝ := (D.R.m : ℝ) ^ 3 * (bigN D : ℝ) ^ 2 with hM
  have hM0 : 0 ≤ M := by positivity
  have hZ := sum_abs_count_AA_le D hcc ch.S.PA
  push_cast at hZ
  have hXle : X ≤ 8 * M * (D.R.f * large₂.sc.L / 50) := by
    have h1 : X ≤ ∑ w ∈ ch.S.PA, 8 * M * ((|(FractionalIdeal.count D.host.E w D.host.AA : ℝ)| +
        |(FractionalIdeal.count D.host.E w D.host.AAbar : ℝ)|) * Real.log (Ideal.absNorm w.asIdeal : ℕ)) := by
      refine Finset.sum_le_sum fun w _ => ?_
      have hl : 0 ≤ Real.log (Ideal.absNorm w.asIdeal : ℕ) / 2 := by
        have := Real.log_natCast_nonneg (Ideal.absNorm w.asIdeal); linarith
      have hn' := (Int.cast_le (R := ℝ)).2 (hnb w)
      push_cast at hn'
      calc |(n w : ℝ)| * (Real.log (Ideal.absNorm w.asIdeal : ℕ) / 2)
          ≤ 16 * ((D.R.m : ℝ) ^ 3 * (bigN D : ℝ) ^ 2 * (|(FractionalIdeal.count D.host.E w D.host.AA : ℝ)| +
            |(FractionalIdeal.count D.host.E w D.host.AAbar : ℝ)|)) * (Real.log (Ideal.absNorm w.asIdeal : ℕ) / 2) :=
            mul_le_mul_of_nonneg_right hn' hl
        _ = _ := by rw [hM]; ring
    rw [← Finset.mul_sum] at h1
    exact h1.trans (mul_le_mul_of_nonneg_left (hZ.trans hdisc) (by positivity))

  have hm44 : (44 : ℝ) ≤ D.R.m := by exact_mod_cast h44
  have hmf : (D.R.m : ℝ) ≤ D.R.f := by
    have : D.R.m ≤ D.R.f := le_trans (Nat.le_self_pow (by norm_num) _) h4f
    exact_mod_cast this
  have hd1 : (1 : ℝ) ≤ D.host.d := by exact_mod_cast (D.host.hyp.2.1 : Nat.Prime D.host.d).one_lt.le
  have hNle : (bigN D : ℝ) ≤ 8 * (D.R.N D.R.m : ℝ) ^ 2 := by exact_mod_cast GlobalTheory.DenSumPf.bigN_le D
  have hmN : (D.R.m : ℝ) ≤ bigN D := by exact_mod_cast ResidueCardinalityNilpotence.GlobalTheory.CompanionTheory.VolVal.m_le_bigN (D := D)
  have hNR : (1 : ℝ) ≤ (D.R.N D.R.m : ℝ) ^ 2 := by
    have h0 : (0 : ℝ) ≤ (D.R.N D.R.m : ℝ) := Nat.cast_nonneg _
    have h1 : (1 : ℝ) ≤ (D.R.N D.R.m : ℝ) := by
      by_contra h
      have : (D.R.N D.R.m : ℝ) < 1 := not_le.1 h
      have : (D.R.N D.R.m : ℕ) = 0 := by
        have : (D.R.N D.R.m : ℕ) < 1 := by exact_mod_cast this
        omega
      rw [this] at hNle
      push_cast at hNle
      linarith
    nlinarith
  have hf0 : (0 : ℝ) ≤ D.R.f := by linarith
  have hmb : (D.R.m : ℝ) ≤ large₂.sc.b := by
    have h1 : (D.R.m : ℝ) ≤ D.R.m * D.R.f := le_mul_of_one_le_right (by linarith) (by linarith)
    have h2 : (D.R.m : ℝ) * D.R.f ≤ D.R.m * D.R.f * (D.R.N D.R.m : ℝ) ^ 2 := le_mul_of_one_le_right (by positivity) hNR
    have h3 : (D.R.m : ℝ) * D.R.f * (D.R.N D.R.m : ℝ) ^ 2 ≤ D.R.m * D.R.f * (D.R.N D.R.m : ℝ) ^ 2 * D.host.d :=
      le_mul_of_one_le_right (by positivity) hd1
    linarith
  have hm2N : (D.R.m : ℝ) ^ 2 * bigN D ≤ 8 * large₂.sc.b := by
    have h1 : (D.R.m : ℝ) ^ 2 * bigN D ≤ (D.R.m : ℝ) ^ 2 * (8 * (D.R.N D.R.m : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left hNle (by positivity)
    have h2 : (D.R.m : ℝ) ^ 2 * (8 * (D.R.N D.R.m : ℝ) ^ 2) ≤ 8 * ((D.R.m : ℝ) * D.R.f * (D.R.N D.R.m : ℝ) ^ 2) := by
      have := mul_le_mul_of_nonneg_right hmf (by positivity : (0 : ℝ) ≤ 8 * (D.R.m : ℝ) * (D.R.N D.R.m : ℝ) ^ 2)
      nlinarith
    have h3 : (D.R.m : ℝ) * D.R.f * (D.R.N D.R.m : ℝ) ^ 2 ≤ D.R.m * D.R.f * (D.R.N D.R.m : ℝ) ^ 2 * D.host.d :=
      le_mul_of_one_le_right (by positivity) hd1
    linarith
  have hsig := ResidueCardinalityNilpotence.GlobalTheory.CompanionTheory.VolVal.sig_nonneg ch.G
  have hb0 : 0 ≤ large₂.sc.b := by linarith
  refine ⟨?_, ?_⟩
  ·
    obtain ⟨dl, h0, hfin, hsum, hv⟩ := loss_sqrt_prod ch.S.PA (fun w => Ideal.absNorm w.asIdeal) hq r hr2 n
    refine ⟨dl, ⟨h0, hfin, fun T => (hsum T).trans (hXle.trans ?_)⟩, fun w => ⟨_, hy, Or.inr (hv w)⟩⟩
    rw [bOne, hlogb]
    set P : ℝ := (D.R.m : ℝ) ^ 2 * (bigN D : ℝ) ^ 2 * D.R.f * large₂.sc.L with hP
    have hP0 : 0 ≤ P := by positivity
    have h1 : 8 * M * (D.R.f * large₂.sc.L / 50) = (4 / 25 * D.R.m) * P := by rw [hM, hP]; ring
    have h2 : (4 / 25 * (D.R.m : ℝ)) * P ≤ (C * large₂.sc.b) * P := mul_le_mul_of_nonneg_right (by nlinarith) hP0
    have h3 : (C * large₂.sc.b) * P ≤ D.R.m * (C * D.R.f * D.R.m * (bigN D : ℝ) ^ 2 * (large₂.sc.L + sig ch.G) * large₂.sc.b) := by
      have : (C * large₂.sc.b) * P = D.R.m * (C * D.R.f * D.R.m * (bigN D : ℝ) ^ 2 * large₂.sc.L * large₂.sc.b) := by rw [hP]; ring
      rw [this]
      have hc0 : 0 ≤ (D.R.m : ℝ) * (C * D.R.f * D.R.m * (bigN D : ℝ) ^ 2) * large₂.sc.b := by
        have : (0 : ℝ) ≤ C := by linarith
        positivity
      nlinarith
    linarith
  ·
    intro σ
    refine ⟨_, hy, (norm_sqrt_prod ch.S.PA (fun w => Ideal.absNorm w.asIdeal) hq r hr2 n σ).trans
      (Real.exp_le_exp.2 (hXle.trans ?_))⟩
    rw [aOne, hlogb]
    set Q : ℝ := (D.R.m : ℝ) * bigN D * D.R.f * large₂.sc.L with hQ
    have hQ0 : 0 ≤ Q := by positivity
    have h1 : 8 * M * (D.R.f * large₂.sc.L / 50) = (4 / 25 * ((D.R.m : ℝ) ^ 2 * bigN D)) * Q := by rw [hM, hQ]; ring
    have h2 : (4 / 25 * ((D.R.m : ℝ) ^ 2 * bigN D)) * Q ≤ (C * large₂.sc.b) * Q := mul_le_mul_of_nonneg_right (by nlinarith) hQ0
    have h3 : (C * large₂.sc.b) * Q ≤ D.R.m * (C * D.R.f * bigN D * large₂.sc.b * large₂.sc.L + C * D.R.m * (bigN D : ℝ) ^ 2 * sig ch.G) := by
      have : (C * large₂.sc.b) * Q = D.R.m * (C * D.R.f * bigN D * large₂.sc.b * large₂.sc.L) := by rw [hQ]; ring
      rw [this]
      have : 0 ≤ (D.R.m : ℝ) * (C * D.R.m * (bigN D : ℝ) ^ 2 * sig ch.G) := by
        have : (0 : ℝ) ≤ C := by linarith
        positivity
      rw [mul_add]
      linarith
    linarith

end Core

theorem finScal_infScal : GlobalTheory.FunPr.Hypotheses₂ → FinScalK ∧ InfScalK := by
  intro _
  refine ⟨⟨0, fun CF _ => ⟨2, fun ε C hC => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F s ch _ _ hF => ?_⟩⟩⟩,
    ⟨0, fun CF _ => ⟨2, fun ε C hC => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F s ch _ _ hF => ?_⟩⟩⟩⟩
  · exact (core s ch hF hC).1
  · exact (core s ch hF hC).2

end GlobalTheory.ScalAA
