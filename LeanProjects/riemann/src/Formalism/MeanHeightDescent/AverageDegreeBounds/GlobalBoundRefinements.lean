import Mathlib
import Formalism.MeanHeightDescent.CovolumeEstimateAnchoredWeights
import Formalism.MeanHeightDescent.AverageDegreeBounds.CovolumeAssemblyHolds
import Formalism.MeanHeightDescent.AverageDegreeBounds.CovolumeFullAssemblyHolds
import Formalism.MeanHeightDescent.AverageDegreeBounds.CovolumeIntoDivisionHolds
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.TheoremDivIneq
import Formalism.MeanHeightDescent.AverageDegreeBounds.SpanMuMin
import Formalism.MeanHeightDescent.AverageDegreeBounds.TwistLower
import Formalism.MeanHeightDescent.AverageDegreeBounds.MuMaxMinkowski

namespace Formalism.ExtensionFiltration

section Numbers
open Finset Module NumberField

theorem weight_shift_constant : WShiftConst := by
  intro Pl _ w w0 lcvD pq logOm C3 B0 llx La f m k Δ b xe CO h1 hw hΔ hpq hCO hlog hLa hf hm hk hkΔ hB0 hllx
  subst hB0
  have hL0 : 0 ≤ CO * La := le_trans (abs_nonneg _) hlog
  have hLa0 : 0 ≤ La := by nlinarith
  have hpqa : |pq| ≤ k + m := by
    have h := abs_sub_abs_le_abs_sub pq k
    rw [abs_of_pos (by linarith : (0:ℝ) < k)] at h
    linarith
  have hkm : 0 ≤ k + m := by linarith
  have hX0 : 0 ≤ (k + m) * Δ := mul_nonneg hkm hΔ
  have hterm : ∀ ρ, pq * w ρ * logOm ≤ pq * w0 ρ * logOm + (k + m) * Δ * (CO * La) := by
    intro ρ
    have habs : |pq * (w ρ - w0 ρ) * logOm| ≤ (k + m) * Δ * (CO * La) := by
      rw [abs_mul, abs_mul]
      exact mul_le_mul (mul_le_mul hpqa (hw ρ) (abs_nonneg _) hkm) hlog (abs_nonneg _) hX0
    have e : pq * w ρ * logOm = pq * w0 ρ * logOm + pq * (w ρ - w0 ρ) * logOm := by ring
    rw [e]
    linarith [le_abs_self (pq * (w ρ - w0 ρ) * logOm)]
  have hsum : ∑ ρ, pq * w ρ * logOm ≤
      ∑ ρ, pq * w0 ρ * logOm + (Fintype.card Pl : ℝ) * ((k + m) * Δ * (CO * La)) := by
    calc ∑ ρ, pq * w ρ * logOm ≤ ∑ ρ, (pq * w0 ρ * logOm + (k + m) * Δ * (CO * La)) :=
          Finset.sum_le_sum fun ρ _ => hterm ρ
      _ = ∑ ρ, pq * w0 ρ * logOm + (Fintype.card Pl : ℝ) * ((k + m) * Δ * (CO * La)) := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hf0 : 0 ≤ f := le_trans (Nat.cast_nonneg _) hf
  have hm0 : 0 ≤ m := by linarith
  have hb0 : 0 ≤ b := by linarith [mul_nonneg (by linarith : (0:ℝ) ≤ k) hΔ]
  have hxe0 : 0 ≤ xe := by linarith
  have hXY : (k + m) * Δ ≤ 4 * m * b := by
    linarith [mul_nonneg hm0 (by linarith : (0:ℝ) ≤ 2 * b - k * Δ),
      mul_nonneg (mul_nonneg hm0 hΔ) (by linarith : (0:ℝ) ≤ k - 1),
      mul_nonneg hb0 (by linarith : (0:ℝ) ≤ m - 1)]
  have hY0 : 0 ≤ 4 * m * b := mul_nonneg (mul_nonneg (by norm_num) hm0) hb0
  have hB0nn : 0 ≤ f * m * b * xe := mul_nonneg (mul_nonneg (mul_nonneg hf0 hm0) hb0) hxe0
  have hc1 : (Fintype.card Pl : ℝ) * ((k + m) * Δ * (CO * La)) ≤ f * ((k + m) * Δ * (CO * La)) :=
    mul_le_mul_of_nonneg_right hf (mul_nonneg hX0 hL0)
  have hc2 : f * ((k + m) * Δ * (CO * La)) ≤ f * (4 * m * b * (CO * (3 * xe))) :=
    mul_le_mul_of_nonneg_left
      (mul_le_mul hXY (mul_le_mul_of_nonneg_left hLa (by linarith)) hL0 hY0) hf0
  have hc3 : 0 ≤ CO * (f * m * b * xe) * (llx - 1) :=
    mul_nonneg (mul_nonneg (by linarith) hB0nn) (by linarith)
  linarith

theorem la_le_three (x eps L b a rd La : ℝ) (hx : 1 ≤ x) (hL : L = x ^ eps) (hb : b = Real.exp L)
    (ha : a = x * b) (hrd : 1 ≤ rd) (hrdL : Real.log rd ≤ L) (hlx : Real.log x ≤ L)
    (hLa : La = Real.log (a * rd)) : La ≤ 3 * x ^ eps := by
  have hx0 : 0 < x := lt_of_lt_of_le one_pos hx
  have hrd0 : 0 < rd := lt_of_lt_of_le one_pos hrd
  have hb0 : 0 < b := by rw [hb]; exact Real.exp_pos L
  have hlb : Real.log b = L := by rw [hb, Real.log_exp]
  rw [hLa, ha, Real.log_mul (mul_pos hx0 hb0).ne' hrd0.ne', Real.log_mul hx0.ne' hb0.ne', hlb, ← hL]
  linarith

theorem covolume_assembly_weighted_holds : CovolumeEstimateAnchoredWeights := by
  intro K _ _ _ _ d D hD hdD XW hXW M hM Pl _ w w0 c1 ua muU muA muN muG mmax dA dB dN dg db
    C1 Cf Cc cfl ε δ Q P Λ G P9 pq q' logOm x eps L b rd Lchi llx LL0 B0 f m k S η a La R CO
    h41 hcfl hfl hdA hAB hBε hε hP hdesc hcQ hΛ hεQ hd hsum hdb hdb3 hδ hδ12 hcut hmuN hmm hG h9 hsmall
    hc1 hua hU1 hw hkS hkη hcard hm hf hq0 hqm hx heps hL hb hrd hrdL hchi0 hchiL hlx hll hLL0 hB0
    hC1 hCf hCc hww hS hR hkR hk hpq ha hLa hCO hOm
  have h := covolume_assembly_holds K d D hD hdD XW hXW M hM Pl w c1 ua muU muA muN muG mmax dA dB dN dg db
    C1 Cf Cc cfl ε δ Q P Λ G P9 pq q' logOm x eps L b rd Lchi llx LL0 B0 f m k S η
    h41 hcfl hfl hdA hAB hBε hε hP hdesc hcQ hΛ hεQ hd hsum hdb hdb3 hδ hδ12 hcut hmuN hmm hG h9 hsmall
    hc1 hua hU1 hw hkS hkη hcard hm hf hq0 hqm hx heps hL hb hrd hrdL hchi0 hchiL hlx hll hLL0 hB0
    hC1 hCf hCc
  have h3 := la_le_three x eps L b a rd La hx hL hb ha hrd hrdL hlx hLa
  exact weight_shift_constant Pl w w0 _ pq logOm _ B0 llx La f m k (S + R) b (x ^ eps) CO h hww (by linarith) hpq hCO
    hOm h3 hcard hm hk (by linarith) hB0 hll

theorem covolume_full_assembly_weighted_holds : CovolumeEstimateOfAverageDegreeWeighted := by
  intro K _ _ _ _ d D hD hdD XW hXW M hM Pl _ w w0 c1 ua ι _ _ T DY A cs X cc z ρ R1 R2 Bn δ' h sl δc dc degc
    Ca Cb PPf e1 e2 muU muA muN muG mmax dA dB dN dg db Cf Cc cfl ε δ Q P Λ G P9
    pq q' logOm x eps L b rd Lchi llx LL0 B0 f m k S η a La R CO
    a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24
    hcfl hfl hdA hAB hBε hε hP hdesc hcQ hΛ hεQ hd hsum hdb hdb3 hδ hδ12 hcut hmuN hmm hG h9 hsmall
    hc1 hua hU1 hw hkS hkη hcard hm hf hq0 hqm hx heps hL hb hrd hrdL hchi0 hchiL hlx hll hLL0 hB0
    hCa hCb hCf hCc hww hS hR hkR hk hpq ha hLa hCO hOm
  have h0 := covolume_full_assembly_holds K d D hD hdD XW hXW M hM Pl w c1 ua ι T DY A cs X cc z ρ R1 R2 Bn δ' h sl δc dc degc
    Ca Cb PPf e1 e2 muU muA muN muG mmax dA dB dN dg db Cf Cc cfl ε δ Q P Λ G P9
    pq q' logOm x eps L b rd Lchi llx LL0 B0 f m k S η
    a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24
    hcfl hfl hdA hAB hBε hε hP hdesc hcQ hΛ hεQ hd hsum hdb hdb3 hδ hδ12 hcut hmuN hmm hG h9 hsmall
    hc1 hua hU1 hw hkS hkη hcard hm hf hq0 hqm hx heps hL hb hrd hrdL hchi0 hchiL hlx hll hLL0 hB0
    hCa hCb hCf hCc
  have h3 := la_le_three x eps L b a rd La hx hL hb ha hrd hrdL hlx hLa
  exact weight_shift_constant Pl w w0 _ pq logOm _ B0 llx La f m k (S + R) b (x ^ eps) CO h0 hww (by linarith) hpq hCO
    hOm h3 hcard hm hk (by linarith) hB0 hll

theorem period_bound' : PeriodBound := by
  intro logOm v rd Lc L x b a hlog hv hrd hLc hx hb ha
  have hrd0 : 0 < rd := by linarith
  have hv' : v = rd / 2 := by linarith
  have hpv : Real.pi / v = 2 * Real.pi / rd := by rw [hv', div_div_eq_mul_div]; ring
  have hl2pi : Real.log (2 * Real.pi / rd) = Real.log (2 * Real.pi) - Real.log rd :=
    Real.log_div (by positivity) hrd0.ne'
  have hlrd : 2 * Real.log 2 ≤ Real.log rd := by
    have h4 : Real.log 4 ≤ Real.log rd := Real.log_le_log (by norm_num) hrd
    have e : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      first | norm_num | skip
    linarith
  have hl2 := Real.log_two_gt_d9
  have hpi8 : Real.log (2 * Real.pi) ≤ 3 * Real.log 2 := by
    have h8 : Real.log (2 * Real.pi) ≤ Real.log 8 :=
      Real.log_le_log (by positivity) (by linarith [Real.pi_le_four])
    have e : Real.log 8 = 3 * Real.log 2 := by
      rw [show (8:ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
      first | norm_num | skip
    linarith
  have hpi0 : 0 ≤ Real.log (2 * Real.pi) := Real.log_nonneg (by linarith [Real.pi_gt_three])
  have hg1 := Real.eulerMascheroniConstant_lt_two_thirds
  have hg0 := Real.one_half_lt_eulerMascheroniConstant
  have hlx : 0 ≤ Real.log x := Real.log_nonneg hx
  have hx0 : 0 < x := by linarith
  have hb0 : 0 < b := by rw [hb]; exact Real.exp_pos L
  have hlar : Real.log (a * rd) = Real.log x + L + Real.log rd := by
    rw [ha, Real.log_mul (mul_pos hx0 hb0).ne' hrd0.ne', Real.log_mul hx0.ne' hb0.ne', hb, Real.log_exp]
  rw [hlar, hlog, hpv, hl2pi]
  obtain ⟨hL1, hL2⟩ := abs_le.1 hLc
  rw [abs_le]
  constructor <;> linarith

end Numbers

noncomputable section Short
open Module NumberField
open Formalism.HN

section Core
open NumberField.mixedEmbedding NumberField.InfinitePlace MeasureTheory
open scoped ENNReal NNReal nonZeroDivisors

theorem mk_lt (K : Type) [Field K] [NumberField K] [IsTotallyComplex K]
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (g : InfinitePlace K → ℝ) (hg : ∀ w, 0 < g w)
    (h : (FractionalIdeal.absNorm I.1 : ℝ) * (2:ℝ) ^ nrComplexPlaces K * Real.sqrt |(discr K : ℝ)| <
      Real.pi ^ nrComplexPlaces K * ∏ w, g w ^ 2) :
    ∃ a ∈ (I : FractionalIdeal (𝓞 K)⁰ K), a ≠ 0 ∧ ∀ w : InfinitePlace K, w a < g w := by
  classical
  let f : InfinitePlace K → NNReal := fun w => (g w).toNNReal
  have hmx : ∀ i, max (g i) 0 = g i := fun i => max_eq_left (hg i).le
  have hr : nrRealPlaces K = 0 := by
    unfold nrRealPlaces
    rw [Fintype.card_eq_zero_iff, isEmpty_subtype]
    exact fun w => not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex w)
  have hm : ∀ w : InfinitePlace K, mult w = 2 := fun w => by
    unfold mult
    rw [if_neg (not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex w))]
  have hd : Module.finrank ℝ (mixedSpace K) = 2 * nrComplexPlaces K := by
    rw [mixedEmbedding.finrank, ← card_add_two_mul_card_eq_rank, hr, zero_add]
  have hL : minkowskiBound K I ≠ ⊤ := by
    first
    | exact (minkowskiBound_lt_top K I).ne
    | exact (minkowskiBound_lt_top (K := K) (I := I)).ne
  have hR : volume (convexBodyLT K f) ≠ ⊤ := by
    rw [convexBodyLT_volume]
    simp
    exact ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.coe_ne_top)
      (ENNReal.prod_ne_top fun w _ => ENNReal.pow_ne_top ENNReal.coe_ne_top)
  have key : minkowskiBound K I < volume (convexBodyLT K f) := by
    rw [← ENNReal.toReal_lt_toReal hL hR, convexBodyLT_volume]
    unfold minkowskiBound
    rw [volume_fundamentalDomain_fractionalIdealLatticeBasis, volume_fundamentalDomain_latticeBasis, hd]
    simp [hm, hr, convexBodyLTFactor, f, hmx]
    rw [ENNReal.toReal_ofReal (by first | exact_mod_cast FractionalIdeal.absNorm_nonneg _ | positivity),
      Int.norm_eq_abs]
    have e : ∀ N s : ℝ, N * (((2:ℝ) ^ nrComplexPlaces K)⁻¹ * s) * (2:ℝ) ^ (2 * nrComplexPlaces K) =
        N * 2 ^ nrComplexPlaces K * s := by
      intro N s
      have h2 : (2:ℝ) ^ nrComplexPlaces K ≠ 0 := by positivity
      rw [two_mul, pow_add]
      calc N * (((2:ℝ) ^ nrComplexPlaces K)⁻¹ * s) * ((2:ℝ) ^ nrComplexPlaces K * (2:ℝ) ^ nrComplexPlaces K)
          = N * (2:ℝ) ^ nrComplexPlaces K * s *
              (((2:ℝ) ^ nrComplexPlaces K)⁻¹ * (2:ℝ) ^ nrComplexPlaces K) := by ring
        _ = N * 2 ^ nrComplexPlaces K * s := by rw [inv_mul_cancel₀ h2, mul_one]
    rw [e]
    first | exact h | linarith [h]
  obtain ⟨a, ha, ha0, hlt⟩ := exists_ne_zero_mem_ideal_lt K I key
  exact ⟨a, ha, ha0, fun w => lt_of_lt_of_eq (hlt w) (Real.coe_toNNReal _ (hg w).le)⟩

end Core

section Line

variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] [AddCommGroup V]
  [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι]

theorem muDef_line_eq (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) (x : V) (hx : x ≠ 0) :
    muDef b X (Submodule.span (𝓞 K) ({x} : Set V)) =
      -((1 / (nPl K : ℝ)) * ∑ v, 2 * Real.log (Formalism.HermitianLatticesTheory.normAt b X v x)) := by
  set L : Submodule (𝓞 K) V := Submodule.span (𝓞 K) ({x} : Set V) with hL
  have hLfg : L.FG := Submodule.fg_span (Set.finite_singleton x)
  have hL0 : L ≠ ⊥ := by
    intro h
    exact hx ((Submodule.span_singleton_eq_bot).1 h)
  have hrk : rkK (K := K) L = 1 := rkK_span_singleton x hx
  have hf : 0 < nPl K := Fintype.card_pos
  have hfR : (0 : ℝ) < (nPl K : ℝ) := by exact_mod_cast hf
  obtain ⟨-, hmu, -⟩ := size_maximal_slope K V ι b X hX L hLfg hL0
  have hpos : 0 < ht b X L := (place_lattice_structure K V ι b X hX L hLfg).2.2
  have hli : LinearIndependent K (fun _ : Fin 1 => x) :=
    LinearIndependent.of_subsingleton (0 : Fin 1) hx
  have hrange : Set.range (fun _ : Fin 1 => x) = {x} := Set.range_const
  have hg := (height_gram_determinant K V ι b X hX 1 (fun _ : Fin 1 => x) hli).1
  rw [hrange] at hg
  have hht : ht b X L = ∏ v, Formalism.HermitianLatticesTheory.normAt b X v x ^ 2 := by
    rw [hL, hg]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [Matrix.det_fin_one]
    simp only [gramPl, Matrix.of_apply]
    rw [majAt_self_re]
  have hlog : Real.log (ht b X L) = ∑ v, 2 * Real.log (Formalism.HermitianLatticesTheory.normAt b X v x) := by
    rw [hht, Real.log_prod (s := Finset.univ) (f := fun v => Formalism.HermitianLatticesTheory.normAt b X v x ^ 2)
      (fun v _ => pow_ne_zero 2 (mink_normAt_pos b X hX v x hx).ne')]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [Real.log_pow]; norm_num
  rw [hmu]
  unfold size
  rw [Real.log_rpow hpos, hrk, hlog, Nat.cast_one]
  field_simp

end Line

end Short

noncomputable section Primes
open Finset

end Primes

end Formalism.ExtensionFiltration
