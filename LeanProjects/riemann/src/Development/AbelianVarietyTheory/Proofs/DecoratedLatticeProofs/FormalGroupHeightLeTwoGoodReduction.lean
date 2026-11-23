import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EndOmega
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.TranslateProduct
import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.StatementC
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.StatementK
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.Taylor
import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.AnalyticTransOfAdd
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.BinomialSeriesCoefficients.CurveIntegerMultiplicationSeries
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.BinomialSeriesCoefficients.USideB
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MultiplicationSeriesUnitCoeffNormLeStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeierstrassPOddMulSubTwoTorsionProductStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeierstrassPIntegralOfMulIntegralGoodReductionStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormWeierstrassPSubEqOneOfGood

open PowerSeries GlobalTheory.Honda Formalism.L2.Th1.CM

noncomputable section

namespace GlobalTheory.HeightTwo

open Formalism.L2.Th1.F Formalism.L2.Th1.F.Taylor Formalism.L2.Th1.C Formalism.L2.Th1.C.USideB Formalism.L2.Th1.C.WeierstrassCurveSeries

def shiftFn (L : PeriodPair) (c z : ℂ) : ℂ := 1 + z * z * (L.weierstrassPExcept 0 z + -c)

theorem analyticAt_shiftFn (L : PeriodPair) (c : ℂ) : AnalyticAt ℂ (shiftFn L c) 0 := by
  have h := L.analyticAt_weierstrassPExcept 0
  unfold shiftFn
  fun_prop

theorem taylor0_shiftFn (L : PeriodPair) (c : ℂ) : taylor0 (shiftFn L c) = wpShift (pSeries L) c := by
  have h := L.analyticAt_weierstrassPExcept 0
  unfold shiftFn
  rw [taylor0_add (by fun_prop) (by fun_prop), taylor0_mul (by fun_prop) (by fun_prop),
    taylor0_mul (by fun_prop) (by fun_prop), taylor0_add h (by fun_prop), taylor0_const, taylor0_const, taylor0_id]
  unfold wpShift pSeries
  simp only [map_one, map_neg]
  ring

theorem shiftFn_eq (L : PeriodPair) (c z : ℂ) (hz : z ≠ 0) :
    shiftFn L c z = z ^ 2 * (L.weierstrassP z - c) := by
  have h := L.weierstrassPExcept_add 0 z
  simp only [ZeroMemClass.coe_zero, sub_zero] at h
  unfold shiftFn
  rw [← h]
  field_simp
  ring

theorem taylor0_prod_shiftFn (L : PeriodPair) (S : Finset ℂ) (a : ℂ → ℂ) :
    AnalyticAt ℂ (fun z => ∏ P ∈ S, shiftFn L (a P) z) 0 ∧
      taylor0 (fun z => ∏ P ∈ S, shiftFn L (a P) z) = ∏ P ∈ S, wpShift (pSeries L) (a P) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp only [Finset.prod_empty]; exact ⟨analyticAt_const, by rw [taylor0_const, map_one]⟩
  | insert P S hP ih =>
    simp only [Finset.prod_insert hP]
    exact ⟨(analyticAt_shiftFn L _).mul ih.1,
      by rw [taylor0_mul (analyticAt_shiftFn L _) ih.1, ih.2, taylor0_shiftFn]⟩

theorem weierstrassP_nat_mul_product_series_identity (L : PeriodPair) (n e : ℂ) (hn : n ≠ 0) (S : Finset ℂ) (a b : ℂ → ℂ)
    (h : ∀ z, n * z ∉ L.lattice →
      n ^ 2 * (L.weierstrassP (n * z) - e) * ∏ P ∈ S, (L.weierstrassP z - a P) =
        (L.weierstrassP z - e) * ∏ P ∈ S, (L.weierstrassP z - b P)) :
    rescale n (wpShift (pSeries L) e) * ∏ P ∈ S, wpShift (pSeries L) (a P) =
      wpShift (pSeries L) e * ∏ P ∈ S, wpShift (pSeries L) (b P) := by
  have hc : Filter.Tendsto (fun z : ℂ => n * z) (nhds 0) (nhds 0) := by
    have : Continuous fun z : ℂ => n * z := by fun_prop
    simpa using this.tendsto 0
  have ha : AnalyticAt ℂ (fun z => shiftFn L e (n * z)) 0 :=
    AnalyticAt.comp_of_eq (g := shiftFn L e) (f := fun z : ℂ => n * z) (analyticAt_shiftFn L e) (by fun_prop) (by simp)
  rw [← (taylor0_prod_shiftFn L S a).2, ← (taylor0_prod_shiftFn L S b).2, ← taylor0_shiftFn,
    ← taylor0_rescale n (analyticAt_shiftFn L e), ← taylor0_mul ha (taylor0_prod_shiftFn L S a).1,
    ← taylor0_mul (analyticAt_shiftFn L e) (taylor0_prod_shiftFn L S b).1]
  apply taylor0_congr
  filter_upwards [hc.eventually (L.compl_lattice_sdiff_singleton_mem_nhds 0)] with z hz
  by_cases h0 : z = 0
  · simp [h0, shiftFn]
  have hnz : n * z ≠ 0 := mul_ne_zero hn h0
  have h1 : n * z ∉ L.lattice := fun hm => hz ⟨hm, hnz⟩
  simp only [shiftFn_eq L _ _ h0, shiftFn_eq L _ _ hnz, Finset.prod_mul_distrib]
  linear_combination (z ^ 2 * ∏ P ∈ S, z ^ 2) * h z h1

section Formal

variable {K : Type} [Field K]

theorem map_wpShift {K' : Type} [Field K'] (φ : K →+* K') (p : K⟦X⟧) (c : K) :
    PowerSeries.map φ (wpShift p c) = wpShift (PowerSeries.map φ p) (φ c) := by
  simp [wpShift]

theorem map_rescale' {K' : Type} [Field K'] (φ : K →+* K') (p : K⟦X⟧) (c : K) :
    PowerSeries.map φ (rescale c p) = rescale (φ c) (PowerSeries.map φ p) := by
  ext n
  simp [coeff_rescale]

theorem series_u {σ : Type} {p l linv A : K⟦X⟧} (hL : IsLogPair l linv) (hX : XIsWp p l A 0) (n e : K)
    (S : Finset σ) (a b : σ → K)
    (h : rescale n (wpShift p e) * ∏ P ∈ S, wpShift p (a P) = wpShift p e * ∏ P ∈ S, wpShift p (b P)) :
    (A.subst (mulBy l linv n) - C e * mulBy l linv n ^ 2) * (C (n ^ 2) * ∏ P ∈ S, (A - C (a P) * X ^ 2)) * X ^ 2 =
      mulBy l linv n ^ 2 * ((A - C e * X ^ 2) * ∏ P ∈ S, (A - C (b P) * X ^ 2)) := by
  set v := mulBy l linv n with hv
  have hsl := hs_of hL.1
  have hsv : HasSubst v := hs_of (cc_mulBy hL n)
  have h1 : ∀ x : K, X ^ 2 * subst l (wpShift p x) = (A - C x * X ^ 2) * l ^ 2 := fun x => by
    simpa using subst_wpShift hL.1 hX x
  have h2 := congrArg (substAlgHom hsl) h
  simp only [map_mul, map_prod, coe_substAlgHom] at h2
  rw [subst_rescale hL, ← hv] at h2
  have h3 : v ^ 2 * subst v (subst l (wpShift p e)) = (A.subst v - C e * v ^ 2) * (C n * l) ^ 2 := by
    have := congrArg (subst v) (h1 e)
    have hC : subst v (C e : K⟦X⟧) = (C e : K⟦X⟧) := subst_C _
    rwa [subst_mul hsv, subst_mul hsv, subst_sub hsv, subst_mul hsv, subst_pow hsv, subst_pow hsv, subst_X hsv,
      hC, hv, subst_mulBy_l hL, ← hv] at this
  have h4 : ∀ c : σ → K, (∏ _P ∈ S, (X : K⟦X⟧) ^ 2) * ∏ P ∈ S, subst l (wpShift p (c P)) =
      (∏ P ∈ S, (A - C (c P) * X ^ 2)) * ∏ _P ∈ S, l ^ 2 := fun c => by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun P _ => h1 _
  have hl0 : l ^ 2 * ∏ _P ∈ S, l ^ 2 ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (l_ne_zero hL)) (Finset.prod_ne_zero_iff.2 fun _ _ => pow_ne_zero _ (l_ne_zero hL))
  apply mul_right_cancel₀ hl0
  have ha := h4 a
  have hb := h4 b
  have he := h1 e
  rw [map_pow]
  set T := ∏ _P ∈ S, (X : K⟦X⟧) ^ 2
  set Sa := ∏ P ∈ S, subst l (wpShift p (a P))
  set Sb := ∏ P ∈ S, subst l (wpShift p (b P))
  linear_combination (v ^ 2 * X ^ 2 * T) * h2 - X ^ 2 * T * Sa * h3
    - X ^ 2 * ((A.subst v - C e * v ^ 2) * (C n * l) ^ 2) * ha + v ^ 2 * T * Sb * he
    + v ^ 2 * ((A - C e * X ^ 2) * l ^ 2) * hb

theorem homog_field {F : Type} [Field F] (φ : K →+* F) (q : Polynomial K) (m : ℕ) (hq : q.natDegree ≤ m) (a y : F)
    (hy : y ≠ 0) :
    ∑ i ∈ Finset.range (m + 1), φ (q.coeff i) * a ^ i * y ^ (m - i) = y ^ m * q.eval₂ φ (a / y) := by
  rw [Polynomial.eval₂_eq_sum_range' φ (Nat.lt_succ_of_le hq), Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  rw [pow_sub₀ _ hy hi', div_pow]
  field_simp

theorem homog_prod {σ : Type} (S : Finset σ) (d : K) (c : σ → K) (A : K⟦X⟧) (m : ℕ) (hm : S.card = m) :
    ∑ i ∈ Finset.range (m + 1),
        C ((Polynomial.C d * ∏ P ∈ S, (Polynomial.X - Polynomial.C (c P))).coeff i) * A ^ i * X ^ (2 * (m - i)) =
      C d * ∏ P ∈ S, (A - C (c P) * X ^ 2) := by
  let ψ := algebraMap K⟦X⟧ (FractionRing K⟦X⟧)
  have hψ : Function.Injective ψ := IsFractionRing.injective _ _
  have hy : ψ (X ^ 2) ≠ 0 := (map_ne_zero_iff ψ hψ).2 (pow_ne_zero _ X_ne_zero)
  have hd : (Polynomial.C d * ∏ P ∈ S, (Polynomial.X - Polynomial.C (c P))).natDegree ≤ m := by
    refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
    rw [Polynomial.natDegree_finsetProd_X_sub_C_eq_card, hm]
  have := homog_field (ψ.comp C) _ m hd (ψ A) _ hy
  apply hψ
  simp only [map_sum, map_mul, map_pow, map_prod, map_sub, pow_mul]
  simp only [RingHom.comp_apply, map_pow] at this
  rw [this, Polynomial.eval₂_mul, Polynomial.eval₂_finsetProd, Polynomial.eval₂_C, ← hm, ← Finset.prod_const,
    mul_left_comm, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun P _ => ?_
  rw [map_pow] at hy
  simp only [Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_C, RingHom.comp_apply]
  rw [mul_sub, mul_div_cancel₀ _ hy, mul_comm]

end Formal

theorem coeff_prod_le {K : Type} [NormedField K] [IsUltrametricDist K] {σ : Type} (S : Finset σ) (c : σ → K)
    (hc : ∀ P ∈ S, ‖c P‖ ≤ 1) (i : ℕ) : ‖(∏ P ∈ S, (Polynomial.X - Polynomial.C (c P))).coeff i‖ ≤ 1 := by
  classical
  change _ ∈ Formalism.G.unitBall K
  induction S using Finset.induction_on generalizing i with
  | empty =>
    rw [Finset.prod_empty, Polynomial.coeff_one]
    split_ifs
    exacts [one_mem _, zero_mem _]
  | insert P S hP ih =>
    rw [Finset.prod_insert hP, Polynomial.coeff_mul]
    refine Subring.sum_mem _ fun x _ => mul_mem ?_ (ih (fun Q hQ => hc Q (Finset.mem_insert_of_mem hQ)) _)
    have h : c P ∈ Formalism.G.unitBall K := hc P (Finset.mem_insert_self _ _)
    rw [Polynomial.coeff_sub, Polynomial.coeff_X, Polynomial.coeff_C]
    refine sub_mem ?_ ?_ <;> split_ifs
    exacts [one_mem _, zero_mem _, h, zero_mem _]

theorem norm_two (l : ℕ) [Fact l.Prime] (hl : 5 ≤ l) : ‖(2 : ℂ_[l])‖ = 1 := by
  have h1 : ‖((2 : ℕ) : ℚ_[l])‖ = 1 := by
    rw [Padic.norm_natCast_eq_one_iff, Nat.coprime_primes Fact.out Nat.prime_two]
    omega
  have h2 : (2 : ℂ_[l]) = algebraMap ℚ_[l] ℂ_[l] ((2 : ℕ) : ℚ_[l]) := by simp [map_ofNat]
  rw [h2, norm_algebraMap', h1]

theorem mulBy_eq_zSer {K : Type} [Field K] [CharZero K] (W : WeierstrassCurve K) (n : ℕ) :
    mulBy (Formalism.L2.Th1.A.logSer W) (Formalism.L2.Th1.A.expSer W) (n : K) = Formalism.L2.Th1.A.zSer W (n : ℤ) := by
  have hL := logPair W
  have h0 := ((Formalism.L2.Th1.A.zSerSpec K W).1 (n : ℤ)).1
  have h1 := Formalism.L2.Th1.A.zSerLog K W (n : ℤ)
  rw [Int.cast_natCast] at h1
  unfold mulBy
  rw [← h1, ← subst_comp_subst_apply (hs_of hL.1) (hs_of h0), hL.2.2.2.1, subst_X (hs_of h0)]

theorem odd_mul_sub_mem (L : PeriodPair) {k : ℕ} (hk : Odd k) {s P : ℂ} (hs : 2 * s ∈ L.lattice)
    (hP : (k : ℂ) * P ∈ L.lattice) : (k : ℂ) * (s + P) - s ∈ L.lattice := by
  obtain ⟨j, rfl⟩ := hk
  have : ((2 * j + 1 : ℕ) : ℂ) * (s + P) - s = (j : ℤ) • (2 * s) + ((2 * j + 1 : ℕ) : ℂ) * P := by
    simp only [zsmul_eq_mul]; push_cast; ring
  rw [this]
  exact add_mem (Submodule.smul_mem _ _ hs) hP

theorem wp_congr (L : PeriodPair) {z w : ℂ} (h : z - w ∈ L.lattice) : L.weierstrassP z = L.weierstrassP w := by
  have := L.weierstrassP_add_coe w ⟨z - w, h⟩
  simpa using this

theorem nat_mul_mem (L : PeriodPair) (k : ℕ) {z : ℂ} (h : z ∈ L.lattice) : (k : ℂ) * z ∈ L.lattice := by
  simpa [zsmul_eq_mul] using L.lattice.smul_mem (k : ℤ) h

theorem height_le_two (L : PeriodPair) (l : ℕ) [Fact l.Prime] (hl : 5 ≤ l) (ι : ℂ ≃+* ℂ_[l])
    (h2 : ‖ι L.g₂‖ ≤ 1) (h3 : ‖ι L.g₃‖ ≤ 1) (hΔ : ‖ι L.g₂ ^ 3 - 27 * ι L.g₃ ^ 2‖ = 1) :
    ∃ n, n ≤ l ^ 2 ∧ ‖coeff n (Formalism.L2.Th1.C.mulBy (Formalism.L2.Th1.A.logSer (Formalism.L2.Th1.A.shortW (ι L.g₂) (ι L.g₃)))
      (Formalism.L2.Th1.A.expSer (Formalism.L2.Th1.A.shortW (ι L.g₂) (ι L.g₃))) (l : ℂ_[l]))‖ = 1 := by
  classical
  set W := Formalism.L2.Th1.A.shortW (ι L.g₂) (ι L.g₃) with hW
  have hodd : Odd l := (Fact.out : l.Prime).odd_of_ne_two (by omega)
  have hl0 : (l : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have h4 : ‖(4 : ℂ_[l])‖ = 1 := by
    rw [show (4 : ℂ_[l]) = 2 * 2 by norm_num, norm_mul, norm_two l hl, mul_one]
  have ha4 : ‖W.a₄‖ ≤ 1 := by
    change ‖-ι L.g₂ / 4‖ ≤ 1
    rwa [norm_div, norm_neg, h4, div_one]
  have ha6 : ‖W.a₆‖ ≤ 1 := by
    change ‖-ι L.g₃ / 4‖ ≤ 1
    rwa [norm_div, norm_neg, h4, div_one]
  have hz : ‖(0 : ℂ_[l])‖ ≤ 1 := by simp
  obtain ⟨hb2, -, -, hD⟩ := Formalism.L2.Th1.A.shortInv ℂ_[l] (ι L.g₂) (ι L.g₃)
  have hInt : Formalism.L2.Th1.E.IntCurve (Formalism.L2.Th1.E.curveL l L ι) :=
    ⟨hz, hz, hz, ha4, ha6, by rw [← hΔ, ← hD]; rfl⟩
  obtain ⟨-, hx, -, -, -, -, -, hzs, -⟩ := Formalism.L2.Th1.A.coeffMem ℂ_[l] W (Formalism.G.unitBall ℂ_[l]) hz hz hz ha4 ha6

  have key : ∀ s P : ℂ, s ∉ L.lattice → 2 * s ∈ L.lattice → (l : ℂ) * P ∈ L.lattice →
      s + P ∉ L.lattice ∧ ‖ι (L.weierstrassP (s + P))‖ ≤ 1 := by
    intro s P hs h2s hP
    have hm := odd_mul_sub_mem L hodd h2s hP
    have hn : (l : ℂ) * (s + P) ∉ L.lattice := fun h => hs (by simpa using sub_mem h hm)
    refine ⟨fun h => hn (nat_mul_mem L l h), GlobalTheory.T.weierstrassP_integral_of_mul_integral_good_reduction L l hl ι h2 h3 hΔ _ l hn ?_⟩
    rw [wp_congr L hm, ← Formalism.L2.Th1.E.AnaSys.px_ptOf l L ι s hs]
    exact (Formalism.L2.Th1.E.ptOfInt l L ι hInt s 2 two_pos (fun h => by have := Nat.le_of_dvd two_pos h; omega)
      (by simpa using h2s) hs).1
  set t := L.ω₁ / 2 with ht
  set t' := L.ω₂ / 2 with ht'
  have ht0 : t ∉ L.lattice := L.ω₁_div_two_notMem_lattice
  have ht0' : t' ∉ L.lattice := L.ω₂_div_two_notMem_lattice
  have ht2 : 2 * t ∈ L.lattice := by rw [ht, mul_div_cancel₀ _ two_ne_zero]; exact L.ω₁_mem_lattice
  have ht2' : 2 * t' ∈ L.lattice := by rw [ht', mul_div_cancel₀ _ two_ne_zero]; exact L.ω₂_mem_lattice
  have hp0 : t' + t ∉ L.lattice := fun h => by
    have := (PeriodPair.mul_ω₁_add_mul_ω₂_mem_lattice (L := L) (α := 1 / 2) (β := 1 / 2)).1
      (by convert h using 1; rw [ht, ht']; push_cast; ring)
    norm_num at this
  have hm0 : t' - t ∉ L.lattice := fun h => hp0 (by convert add_mem h ht2 using 1; ring)
  have hp2 : 2 * (t' + t) ∈ L.lattice := by rw [mul_add]; exact add_mem ht2' ht2
  have hm2 : 2 * (t' - t) ∈ L.lattice := by rw [mul_sub]; exact sub_mem ht2' ht2
  have hk0 : (l : ℂ) * 0 ∈ L.lattice := by simp
  have unit : ∀ P : ℂ, (l : ℂ) * P ∈ L.lattice → ‖ι (L.weierstrassP t') - ι (L.weierstrassP (t + P))‖ = 1 := by
    intro P hP
    have k1 := key t' 0 ht0' ht2' hk0
    have k2 := key t P ht0 ht2 hP
    have k3 := key _ P hp0 hp2 hP
    have k4 := key _ (-P) hm0 hm2 (by simpa using hP)
    rw [add_zero] at k1
    rw [add_assoc] at k3
    rw [show t' - t + -P = t' - (t + P) by ring] at k4
    exact GlobalTheory.Honda.norm_weierstrassP_sub_eq_one_of_good L l hl ι h2 h3 hΔ _ _ k1.1 k2.1 k3.1 k4.1 k1.2 k2.2 k3.2 k4.2
  have hst : MulStable L l := fun ω h => nat_mul_mem L l h
  obtain ⟨S, hS⟩ := kerRepsExist L l hl0 hst
  have hcard : S.card + 1 = l ^ 2 := by
    have := kerRepsCard L l S hl0 hst hS
    rw [Complex.normSq_natCast, ← sq] at this
    exact_mod_cast this
  have h0S : (0 : ℂ) ∉ S := fun h => (hS.1 0 h).2 (zero_mem _)
  have hprod := GlobalTheory.T.weierstrassP_odd_mul_sub_twoTorsion_product L l S t hodd hS ht0 ht2
  have hins : ∀ P ∈ insert (0 : ℂ) S, (l : ℂ) * P ∈ L.lattice := by
    intro P hP
    rcases Finset.mem_insert.1 hP with rfl | hP
    exacts [hk0, (hS.1 P hP).1]

  have hzser := congrArg (PowerSeries.map (ι : ℂ →+* ℂ_[l])) (weierstrassP_nat_mul_product_series_identity L l _ hl0 S _ _ hprod)
  have hbr : Formalism.L2.Th1.A.wpReg W = PowerSeries.map (ι : ℂ →+* ℂ_[l]) (pSeries L) := Formalism.L2.Th1.E.wpBridge l L ι
  simp only [map_mul, map_prod, map_rescale', map_wpShift, ← hbr, map_natCast] at hzser
  have hX : XIsWp (Formalism.L2.Th1.A.wpReg W) (Formalism.L2.Th1.A.logSer W) (Formalism.L2.Th1.A.xS W) 0 := by
    have := xIsWp W
    rwa [hb2, zero_div] at this
  have hu := series_u (logPair W) hX _ _ S _ _ hzser
  rw [← hcard]
  refine GlobalTheory.T.multiplication_series_unit_coeff_norm_le ℂ_[l] (Formalism.L2.Th1.A.xS W) _ (ι (L.weierstrassP t)) (ι (L.weierstrassP t')) S.card
    (Polynomial.C ((l : ℂ_[l]) ^ 2) * ∏ P ∈ S, (Polynomial.X - Polynomial.C (ι (L.weierstrassP P))))
    (Polynomial.C 1 * ∏ P ∈ insert 0 S, (Polynomial.X - Polynomial.C (ι (L.weierstrassP (t + P)))))
    hx (Formalism.L2.Th1.A.wSerFactor ℂ_[l] W).2.2.2.1 ?_ (cc_mulBy (logPair W) _) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [mulBy_eq_zSer]; exact hzs l
  · simpa using (key t 0 ht0 ht2 hk0).2
  · simpa using (key t' 0 ht0' ht2' hk0).2
  · rw [map_one, one_mul]; exact Polynomial.monic_prod_of_monic _ _ fun _ _ => Polynomial.monic_X_sub_C _
  · rw [map_one, one_mul, Polynomial.natDegree_finsetProd_X_sub_C_eq_card, Finset.card_insert_of_notMem h0S]
  · rw [map_one, one_mul]
    exact coeff_prod_le _ _ fun P hP => (key t P ht0 ht2 (hins P hP)).2
  · refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
    rw [Polynomial.natDegree_finsetProd_X_sub_C_eq_card]
  · have hm := odd_mul_sub_mem L hodd ht2' hk0
    rw [add_zero] at hm
    have h := congrArg ι (hprod t' fun h => ht0' (by simpa using sub_mem h hm))
    rw [wp_congr L hm] at h
    simp only [map_mul, map_sub, map_prod, map_pow, map_natCast] at h
    have hu0 := unit 0 hk0
    rw [add_zero] at hu0
    have hne : ι (L.weierstrassP t') - ι (L.weierstrassP t) ≠ 0 := fun h => by simp [h] at hu0
    rw [mul_right_comm, mul_comm] at h
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X]
    rw [mul_left_cancel₀ hne h, norm_prod]
    exact Finset.prod_eq_one fun P hP => unit P (hS.1 P hP).1
  · rw [homog_prod S _ _ _ _ rfl, homog_prod (insert 0 S) _ _ _ (S.card + 1) (Finset.card_insert_of_notMem h0S),
      Finset.prod_insert h0S, add_zero, map_one, one_mul]
    exact hu

end GlobalTheory.HeightTwo
