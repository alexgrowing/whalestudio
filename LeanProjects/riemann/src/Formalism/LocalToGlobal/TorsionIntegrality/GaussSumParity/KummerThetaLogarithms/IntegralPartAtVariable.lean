import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.BiextensionHypothesesOfLevelOne
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.CoboundaryCommutesHomomorphism
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.StatementC
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FinalS

noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.D

open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq DivAB d1 swap2 UnrOK IsLawOfLog BetaHyp frobVar)
open MvPowerSeries

namespace SubstitutionCoefficientLemmas

open Pair InverseCommuting

section Alg

variable {K : Type} [Field K]

theorem coeff_subst_fin {ι τ : Type} {a : ι → MvPowerSeries τ K} (ha : HasSubst a) (e : τ →₀ ℕ) :
    ∃ T : Finset (ι →₀ ℕ), ∀ g : MvPowerSeries ι K,
      coeff e (subst a g) = ∑ d ∈ T, coeff d g * coeff e (d.prod fun s k => a s ^ k) := by
  let u : MvPowerSeries ι K := fun _ => 1
  have hu : ∀ d, coeff d u = 1 := fun d => coeff_apply u d
  have hfin : (Function.support
      fun d => coeff d u • coeff e (d.prod fun s k => a s ^ k)).Finite :=
    coeff_subst_finite ha u e
  refine ⟨hfin.toFinset, fun g => ?_⟩
  rw [coeff_subst ha, finsum_eq_sum_of_support_subset]
  · rfl
  · intro d hd
    rw [Finset.mem_coe, Set.Finite.mem_toFinset, Function.mem_support]
    rw [Function.mem_support] at hd
    intro h0
    apply hd
    rw [hu, one_smul] at h0
    rw [h0, smul_zero]

theorem subst_scale {τ : Type} {G H : MvPowerSeries τ K} (hG : constantCoeff G = 0)
    (hH : constantCoeff H = 0) (a b : K) (B : MvPowerSeries (Fin 2) K) :
    subst ![C a * G, C b * H] B = subst ![G, H] (rescale ![a, b] B) := by
  have hs := hs2 hG hH
  rw [rescale_eq_subst, subst_comp_subst_apply (HasSubst.smul_X _) hs]
  congr 1
  funext i
  rw [Pi.smul_apply', subst_smul hs, subst_X hs, smul_eq_C_mul]
  fin_cases i <;> rfl

theorem coeff_scale (a b : K) (B : MvPowerSeries (Fin 2) K) (d : Fin 2 →₀ ℕ) :
    coeff d (rescale ![a, b] B) = a ^ d 0 * b ^ d 1 * coeff d B := by
  rw [coeff_rescale, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_two]
  rfl

theorem left_eq {l : ℕ} (hl : 2 ≤ l) {α : K} {e : PowerSeries K} (he : IsMul l α e)
    (be0 : MvPowerSeries (Fin 2) K) :
    subst ![C α * at1 (0 : Fin 2) (lgF K l), at1 (1 : Fin 2) (lgF K l)] (addC l be0) =
      subst ![at1 (0 : Fin 2) e, X 1] be0 := by
  have h := addC_log expSpec hl (a := at1 (0 : Fin 2) e) (b := X 1) (constantCoeff_inVar_eq_zero _ he.1)
    (constantCoeff_X 1) be0
  have h1 : PowerSeries.subst (at1 (0 : Fin 2) e) (lgF K l) = C α * at1 (0 : Fin 2) (lgF K l) :=
    log_mul he (constantCoeff_X 0)
  rw [h1] at h
  exact h

theorem right_eq {l : ℕ} (hl : 2 ≤ l) {β : K} {e : PowerSeries K} (he : IsMul l β e)
    (be0 : MvPowerSeries (Fin 2) K) :
    subst ![at1 (0 : Fin 2) (lgF K l), C β * at1 (1 : Fin 2) (lgF K l)] (addC l be0) =
      subst ![X 0, at1 (1 : Fin 2) e] be0 := by
  have h := addC_log expSpec hl (a := X 0) (b := at1 (1 : Fin 2) e) (constantCoeff_X 0)
    (constantCoeff_inVar_eq_zero _ he.1) be0
  have h1 : PowerSeries.subst (at1 (1 : Fin 2) e) (lgF K l) = C β * at1 (1 : Fin 2) (lgF K l) :=
    log_mul he (constantCoeff_X 1)
  rw [h1] at h
  exact h

end Alg

section Normed

variable {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K]

def InS (l : ℕ) (σ : K →+* K) (be0 : MvPowerSeries (Fin 2) K) (α : K) : Prop :=
  ‖α‖ ≤ 1 ∧ σ (σ α) = α ∧
    Simeq (subst ![C α * at1 (0 : Fin 2) (lgF K l), at1 (1 : Fin 2) (lgF K l)] (addC l be0))
      (subst ![at1 (0 : Fin 2) (lgF K l), C (σ α) * at1 (1 : Fin 2) (lgF K l)] (addC l be0))

theorem integral_part_at_variable {l : ℕ} (hp : l.Prime) (σ : K →+* K) (x : Fin 2) : IP l σ (at1 x (lgF K l)) :=
  ⟨constantCoeff_inVar_eq_zero _ (cc_lgF hp.two_le), by
    rw [TranslateJetMomentLawAnyIdempotentLevel.artin_hasse_log_frobenius_shift hp]
    exact KernelCokernelKilling.integral_X' _⟩

variable {l : ℕ} {σ : K →+* K} {F be0 : MvPowerSeries (Fin 2) K}

theorem inS_root (hU : UnrOK K l σ) (hB : BetaHyp l F be0) {ζ : K} (hζ : ζ ^ (l ^ 2 - 1) = 1) :
    InS l σ be0 ζ := by
  have hl : 2 ≤ l := hU.1.two_le
  have hN0 : l ^ 2 - 1 ≠ 0 := by
    have : 2 ^ 2 ≤ l ^ 2 := Nat.pow_le_pow_left hl 2
    omega
  have hσ : σ ζ = ζ ^ l := teichSigma K l 2 σ hU (by norm_num) ζ hζ
  have hζl : (ζ ^ l) ^ (l ^ 2 - 1) = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, hζ, one_pow]
  refine ⟨(FormalExponential.norm_eq_one_of_pow hN0 hζ).le, ?_, ?_⟩
  · rw [hσ, map_pow, hσ, ← pow_mul, ← sq]
    have : l ^ 2 = (l ^ 2 - 1) + 1 := by omega
    rw [this, pow_succ, hζ, one_mul]
  · rw [hσ, left_eq hl (FormalExponential.isMul_root hl hζ), right_eq hl (FormalExponential.isMul_root hl hζl),
      FormalExponential.at_variable_C_mul_X, FormalExponential.at_variable_C_mul_X]
    exact hB.2.2.2 ζ hζ

theorem inS_add (hU : UnrOK K l σ) (hF : IsLawOfLog l F) (hF1 : F1 F be0) {α β : K}
    (hα : InS l σ be0 α) (hβ : InS l σ be0 β) : InS l σ be0 (α + β) := by
  obtain ⟨hadd1, hadd2, -⟩ := pairRules K l σ hU F hF be0 hF1 (Fin 2)
  obtain ⟨-, -, hmul⟩ := ipClosure K l σ (Fin 2)
  have hσ1 := (frobSq K l σ hU).2
  have hG := integral_part_at_variable hU.1 σ (0 : Fin 2)
  have hH := integral_part_at_variable hU.1 σ (1 : Fin 2)
  refine ⟨(IsUltrametricDist.norm_add_le_max _ _).trans (max_le hα.1 hβ.1), ?_, ?_⟩
  · rw [map_add, map_add, hα.2.1, hβ.2.1]
  · rw [map_add σ, map_add C, map_add C, add_mul, add_mul]
    refine sim_trans (hadd1 _ _ _ (hmul α _ hα.1 hα.2.1 hG) (hmul β _ hβ.1 hβ.2.1 hG) hH) ?_
    refine sim_trans (sim_add hα.2.2 hβ.2.2) (sim_symm ?_)
    exact hadd2 _ _ _ hG (hmul (σ α) _ (hσ1 α hα.1) (by rw [hα.2.1]) hH)
      (hmul (σ β) _ (hσ1 β hβ.1) (by rw [hβ.2.1]) hH)

theorem inS_zero (hU : UnrOK K l σ) (hF : IsLawOfLog l F) (hB : BetaHyp l F be0) :
    InS l σ be0 0 := by
  have hodd : Odd l := hU.1.odd_of_ne_two hU.2.1.ne'
  have hev : Even (l ^ 2 - 1) := Nat.Odd.sub_odd hodd.pow odd_one
  have h := inS_add hU hF ⟨hB.1, hB.2.1, hB.2.2.1⟩ (inS_root hU hB (one_pow _))
    (inS_root hU hB hev.neg_one_pow)
  rwa [add_neg_cancel] at h

theorem inS_nat (hU : UnrOK K l σ) (hF : IsLawOfLog l F) (hB : BetaHyp l F be0) {α : K}
    (hα : InS l σ be0 α) (n : ℕ) : InS l σ be0 ((n : K) * α) := by
  induction n with
  | zero =>
    rw [Nat.cast_zero, zero_mul]
    exact inS_zero hU hF hB
  | succ n ih =>
    rw [Nat.cast_succ, add_mul, one_mul]
    exact inS_add hU hF ⟨hB.1, hB.2.1, hB.2.2.1⟩ ih hα

theorem approx_one (hU : UnrOK K l σ) (hF : IsLawOfLog l F) (hB : BetaHyp l F be0) {ζ0 : K}
    (hζ0 : IsPrimitiveRoot ζ0 (l ^ 2 - 1)) {α : K} (hα : ‖α‖ ≤ 1) (hfix : σ (σ α) = α) :
    ∃ z, InS l σ be0 z ∧ ‖α - z‖ ≤ (l : ℝ)⁻¹ := by
  have hp := hU.1
  have hl : 2 ≤ l := hp.two_le
  have hpn := hU.2.2.1
  have hval := hU.2.2.2.1
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hp.one_lt
  have hinv : ((l : ℝ))⁻¹ < 1 := inv_lt_one_of_one_lt₀ hl1
  have hN : 0 < l ^ 2 - 1 := by
    have : 2 ^ 2 ≤ l ^ 2 := Nat.pow_le_pow_left hl 2
    omega
  have h1 : ‖α ^ (l ^ 2) - α‖ ≤ (l : ℝ)⁻¹ := by
    have h := (frobSq K l σ hU).1.2.2.2 α hα
    rwa [RingHom.comp_apply, hfix, norm_sub_rev, hpn] at h
  have e : α ^ (l ^ 2) - α = α * ∏ z ∈ Polynomial.nthRootsFinset (l ^ 2 - 1) (1 : K), (α - z) := by
    have h := hζ0.pow_sub_pow_eq_prod_sub_mul α 1 hN
    simp only [one_pow, mul_one] at h
    rw [← h, mul_sub, mul_one, ← pow_succ']
    congr 2
    omega
  by_contra hc
  push Not at hc
  have h0 : (1 : ℝ) ≤ ‖α‖ := by
    by_contra hlt
    have h := hc 0 (inS_zero hU hF hB)
    rw [sub_zero] at h
    exact absurd (TraceNormBounds.norm_le_inv_of_lt_one hp.one_lt hval (not_le.1 hlt)) (not_le.2 h)
  have h4 : ∀ z ∈ Polynomial.nthRootsFinset (l ^ 2 - 1) (1 : K), (1 : ℝ) ≤ ‖α - z‖ := by
    intro z hz
    by_contra hlt
    exact absurd (TraceNormBounds.norm_le_inv_of_lt_one hp.one_lt hval (not_le.1 hlt))
      (not_le.2 (hc z (inS_root hU hB ((Polynomial.mem_nthRootsFinset hN 1).1 hz))))
  have h5 : (1 : ℝ) ≤ ‖∏ z ∈ Polynomial.nthRootsFinset (l ^ 2 - 1) (1 : K), (α - z)‖ := by
    rw [norm_prod]
    have := Finset.prod_le_prod (s := Polynomial.nthRootsFinset (l ^ 2 - 1) (1 : K))
      (f := fun _ => (1 : ℝ)) (g := fun z : K => ‖α - z‖) (fun _ _ => zero_le_one) h4
    simpa using this
  rw [e, norm_mul] at h1
  have h6 : (1 : ℝ) ≤ ‖α‖ * ‖∏ z ∈ Polynomial.nthRootsFinset (l ^ 2 - 1) (1 : K), (α - z)‖ :=
    one_le_mul_of_one_le_of_one_le h0 h5
  linarith

theorem approx (hU : UnrOK K l σ) (hF : IsLawOfLog l F) (hB : BetaHyp l F be0) {ζ0 : K}
    (hζ0 : IsPrimitiveRoot ζ0 (l ^ 2 - 1)) (k : ℕ) : ∀ α : K, ‖α‖ ≤ 1 → σ (σ α) = α →
    ∃ z, InS l σ be0 z ∧ ‖α - z‖ ≤ ((l : ℝ) ^ k)⁻¹ := by
  have hp := hU.1
  have hpn := hU.2.2.1
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hp.one_lt
  have hl0 : (l : ℝ) ≠ 0 := by positivity
  have hlK : (l : K) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  induction k with
  | zero =>
    intro α hα _
    exact ⟨0, inS_zero hU hF hB, by simpa using hα⟩
  | succ k ih =>
    intro α hα hfix
    obtain ⟨z0, hz0, hn0⟩ := approx_one hU hF hB hζ0 hα hfix
    have hy : ‖(α - z0) / (l : K)‖ ≤ 1 := by
      rw [norm_div, hpn, div_inv_eq_mul]
      calc ‖α - z0‖ * l ≤ (l : ℝ)⁻¹ * l := by gcongr
        _ = 1 := inv_mul_cancel₀ hl0
    have hyf : σ (σ ((α - z0) / (l : K))) = (α - z0) / (l : K) := by
      rw [map_div₀, map_div₀, map_sub, map_sub, map_natCast, map_natCast, hfix, hz0.2.1]
    obtain ⟨m, hm, hnm⟩ := ih _ hy hyf
    refine ⟨z0 + (l : K) * m, inS_add hU hF ⟨hB.1, hB.2.1, hB.2.2.1⟩ hz0 (inS_nat hU hF hB hm l), ?_⟩
    have e : α - (z0 + (l : K) * m) = (l : K) * ((α - z0) / (l : K) - m) := by
      field_simp
      ring
    rw [e, norm_mul, hpn, pow_succ, mul_inv, mul_comm]
    gcongr

theorem coeff_diff {τ : Type} {G H : MvPowerSeries τ K} (hG : constantCoeff G = 0)
    (hH : constantCoeff H = 0) (B : MvPowerSeries (Fin 2) K) (n : τ →₀ ℕ) :
    ∃ (T : Finset (Fin 2 →₀ ℕ)) (c : (Fin 2 →₀ ℕ) → K), ∀ x y : K,
      coeff n (subst ![C x * G, H] B - subst ![G, C y * H] B) =
        ∑ d ∈ T, x ^ d 0 * c d - ∑ d ∈ T, y ^ d 1 * c d := by
  obtain ⟨T, hT⟩ := coeff_subst_fin (hs2 hG hH) n
  refine ⟨T, fun d => coeff d B * coeff n (d.prod fun s k => ![G, H] s ^ k), fun x y => ?_⟩
  have e1 : subst ![C x * G, H] B = subst ![C x * G, C 1 * H] B := by rw [map_one, one_mul]
  have e2 : subst ![G, C y * H] B = subst ![C 1 * G, C y * H] B := by rw [map_one, one_mul]
  rw [map_sub, e1, e2, subst_scale hG hH, subst_scale hG hH, hT, hT]
  simp only [coeff_scale, one_pow, mul_one, one_mul, mul_assoc]

end Normed

end SubstitutionCoefficientLemmas

open SubstitutionCoefficientLemmas Pair

theorem f_of_beta_hypotheses : FOfBetaHyp := by
  intro K _ _ _ l σ hU hζ F hF be0 hB
  obtain ⟨ζ0, hζ0⟩ := hζ
  refine ⟨⟨hB.1, hB.2.1, hB.2.2.1⟩, ?_⟩
  intro α hα hfix e e' he he'
  have hp := hU.1
  have hl : 2 ≤ l := hp.two_le
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hp.one_lt
  have hiso := sigma_isometry K l σ hU
  have hcont : Continuous σ := (AddMonoidHomClass.isometry_of_norm σ hiso).continuous
  choose a haS han using fun k => approx hU hF hB hζ0 k α hα hfix
  have hlim : Filter.Tendsto a Filter.atTop (nhds α) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun _ => norm_nonneg _) (fun k => ?_)
      (tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt hl1))
    rw [norm_sub_rev]
    exact han k
  have hlimσ : Filter.Tendsto (fun k => σ (a k)) Filter.atTop (nhds (σ α)) :=
    (hcont.tendsto α).comp hlim
  have hG0 : constantCoeff (at1 (0 : Fin 2) (lgF K l)) = 0 := constantCoeff_inVar_eq_zero _ (cc_lgF hl)
  have hH0 : constantCoeff (at1 (1 : Fin 2) (lgF K l)) = 0 := constantCoeff_inVar_eq_zero _ (cc_lgF hl)
  have key := simeq_closed K l σ hU (Fin 2)
    (fun k => subst ![C (a k) * at1 (0 : Fin 2) (lgF K l), at1 (1 : Fin 2) (lgF K l)] (addC l be0) -
      subst ![at1 (0 : Fin 2) (lgF K l), C (σ (a k)) * at1 (1 : Fin 2) (lgF K l)] (addC l be0))
    (subst ![C α * at1 (0 : Fin 2) (lgF K l), at1 (1 : Fin 2) (lgF K l)] (addC l be0) -
      subst ![at1 (0 : Fin 2) (lgF K l), C (σ α) * at1 (1 : Fin 2) (lgF K l)] (addC l be0))
    (by
      intro n
      obtain ⟨T, c, hT⟩ := coeff_diff hG0 hH0 (addC l be0) n
      simp only [hT]
      refine Filter.Tendsto.sub ?_ ?_
      · exact tendsto_finsetSum _ fun d _ => (hlim.pow _).mul_const _
      · exact tendsto_finsetSum _ fun d _ => (hlimσ.pow _).mul_const _)
    (fun k => B4.simeq_sub_zero (haS k).2.2)
  rw [← left_eq hl he, ← right_eq hl he']
  unfold Simeq at key ⊢
  rwa [sub_zero] at key

end Formalism.L2.Th1.D
