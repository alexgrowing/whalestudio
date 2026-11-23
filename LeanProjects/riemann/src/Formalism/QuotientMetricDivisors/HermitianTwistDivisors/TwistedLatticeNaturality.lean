import Mathlib
import Formalism.QuotientMetricDivisors.DivIntoDualShift
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.IdxChange
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ImageLcv
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.LcvBasis
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.LocBasis
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ValBasic
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ProdFormula
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.SizeMu
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.DiscreteSpanOfLinIndep
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.DivIntoDual

open Module NumberField IsDedekindDomain
open scoped Matrix nonZeroDivisors

noncomputable section

namespace Formalism.DivisionValues

section Smul

variable {K : Type} [Field K] [NumberField K] [StarRing K] {d : ℕ}

def shiftEquiv (d : ℕ) (a : K) (ha : a ≠ 0) : (Fin d → K) ≃ₗ[𝓞 K] (Fin d → K) :=
  (LinearEquiv.smulOfNeZero K (Fin d → K) a ha).restrictScalars (𝓞 K)

theorem shift_smulLat_eq_map (a : K) (ha : a ≠ 0) (N : Submodule (𝓞 K) (Fin d → K)) :
    smulLat a N = N.map ((shiftEquiv d a ha : (Fin d → K) ≃ₗ[𝓞 K] (Fin d → K)) :
      (Fin d → K) →ₗ[𝓞 K] (Fin d → K)) := rfl

theorem shift_mem_smulLat (a : K) (N : Submodule (𝓞 K) (Fin d → K)) (x : Fin d → K) :
    x ∈ smulLat a N ↔ ∃ y ∈ N, a • y = x := by
  simp [smulLat, Submodule.mem_map]

theorem localizationAt_smul (w : HeightOneSpectrum (𝓞 K)) (a : K) (ha : a ≠ 0)
    (N : Submodule (𝓞 K) (Fin d → K)) :
    Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (smulLat a N) = smulLat a (Formalism.HermitianLatticesTheory.localization₂ w.asIdeal N) := by
  ext x
  rw [imageLcv_mem_locP, shift_mem_smulLat]
  constructor
  · rintro ⟨s, hs, hsx⟩
    rw [shift_mem_smulLat] at hsx
    obtain ⟨y, hy, hyx⟩ := hsx
    refine ⟨a⁻¹ • x, ?_, by rw [smul_smul, mul_inv_cancel₀ ha, one_smul]⟩
    rw [imageLcv_mem_locP]
    refine ⟨s, hs, ?_⟩
    rw [smul_comm, ← hyx, smul_smul, inv_mul_cancel₀ ha, one_smul]
    exact hy
  · rintro ⟨y, hy, rfl⟩
    rw [imageLcv_mem_locP] at hy
    obtain ⟨s, hs, hsy⟩ := hy
    refine ⟨s, hs, ?_⟩
    rw [shift_mem_smulLat]
    exact ⟨s • y, hsy, smul_comm a s y⟩

theorem shift_smulLat_span (a : K) (f : Fin d → Fin d → K) :
    smulLat a (Submodule.span (𝓞 K) (Set.range f)) =
      Submodule.span (𝓞 K) (Set.range fun k => a • f k) := by
  rw [smulLat, Submodule.map_span, ← Set.range_comp]
  rfl

theorem shift_vw_pow (w : HeightOneSpectrum (𝓞 K)) (a : K) (ha : a ≠ 0) (n : ℕ) :
    vw w (a ^ n) = (n : ℤ) * vw w a := by
  simp only [vw]
  rw [← FractionalIdeal.spanSingleton_pow, FractionalIdeal.count_pow]

theorem shift_idx_smulLat (w : HeightOneSpectrum (𝓞 K)) (N : Submodule (𝓞 K) (Fin d → K))
    (hN : Submodule.IsLattice K N) (a : K) (ha : a ≠ 0) :
    idx w N (smulLat a N) = (d : ℤ) * vw w a := by
  obtain ⟨f, hf, hl⟩ := semilocal_basis_exists K d N hN w
  have h1 : Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (Submodule.span (𝓞 K) (Set.range f)) =
      Formalism.HermitianLatticesTheory.localization₂ w.asIdeal N := by
    unfold Formalism.HermitianLatticesTheory.loc at hl
    unfold Formalism.HermitianLatticesTheory.localization₂
    exact idxChange_locS_of_le (Formalism.HermitianLatticesTheory.locBasic_hcompl_le (K := K) w.asIdeal) hl
  have hdet : (Matrix.diagonal fun _ : Fin d => a).det = a ^ d := by
    simp [Matrix.det_diagonal]
  have h2 : Formalism.HermitianLatticesTheory.localization₂ w.asIdeal
      (Submodule.span (𝓞 K) (Set.range (idxChangeAct f (Matrix.diagonal fun _ : Fin d => a)))) =
      Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (smulLat a N) := by
    rw [idxChange_act_diagonal, ← shift_smulLat_span, localizationAt_smul w a ha, h1,
      ← localizationAt_smul w a ha]
  have h3 := idxChange_at w (smulLat a N) f hf (Matrix.diagonal fun _ : Fin d => a)
    (by rw [hdet]; exact pow_ne_zero d ha) h2
  rw [hdet, shift_vw_pow w a ha] at h3
  rw [← h3]
  unfold idx
  exact idxChange_lidx_congr w.asIdeal h1.symm rfl

theorem shift_index_formula : ShiftIndex := by
  intro K _ _ _ d N N' hN w s hsh
  obtain ⟨a, ha, hva, hloc⟩ := hsh
  have e : idx w N N' = idx w N (smulLat a N) := by
    unfold idx
    exact Formalism.DivisionValues.StepBAux.lidx_congr w.asIdeal N N N' (smulLat a N) rfl hloc
  rw [e, shift_idx_smulLat w N hN a ha, hva]
  ring

end Smul

theorem mu_log_conductor : MuLcv := by
  intro K _ _ _ _ d hd X hX N hN
  have hfg : N.FG := Submodule.IsLattice.fg (self := hN)
  have hspan : Submodule.span K (N : Set (Fin d → K)) = ⊤ :=
    Submodule.IsLattice.span_eq_top (self := hN)
  have hne : N ≠ ⊥ := by
    intro h
    have h2 : Submodule.span K (((⊥ : Submodule (𝓞 K) (Fin d → K))) : Set (Fin d → K)) = ⊥ := by
      simp
    rw [h, h2] at hspan
    have h3 := congrArg (fun U : Submodule K (Fin d → K) => finrank K U) hspan
    simp only [finrank_bot, finrank_top, finrank_fin_fun] at h3
    omega
  obtain ⟨-, hmu, -⟩ := Formalism.HN.size_maximal_slope K (Fin d → K) (Fin d)
    (Pi.basisFun K (Fin d)) X hX N hfg hne
  have hht : 0 < Formalism.HN.ht (Pi.basisFun K (Fin d)) X N :=
    (Formalism.HN.place_lattice_structure K (Fin d → K) (Fin d) (Pi.basisFun K (Fin d)) X hX N hfg).2.2
  have hrk : Formalism.HN.rkK N = d := by
    unfold Formalism.HN.rkK
    rw [hspan]
    simp
  have hn : (finrank ℚ K : ℝ) = 2 * (Formalism.HN.nPl K : ℝ) := by
    exact_mod_cast Formalism.HN.sizeMu_finrank_eq K
  have hf : (0 : ℝ) < Formalism.HN.nPl K := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (InfinitePlace K))
  have hDr : (0 : ℝ) < d := by exact_mod_cast hd
  rw [hmu, Formalism.HN.size, Real.log_rpow hht, hrk, lcv, hn]
  field_simp

theorem shift_lw_pos {K : Type} [Field K] [NumberField K] [StarRing K]
    (w : HeightOneSpectrum (𝓞 K)) : 0 < lw w := by
  unfold lw
  apply div_pos
  · apply Real.log_pos
    have h1 : Ideal.absNorm w.asIdeal ≠ 1 := by
      rw [Ne, Ideal.absNorm_eq_one_iff]
      exact w.isPrime.ne_top
    have h0 : Ideal.absNorm w.asIdeal ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff]
      exact w.ne_bot
    have h2 : 1 < Ideal.absNorm w.asIdeal := by omega
    exact_mod_cast h2
  · exact_mod_cast Module.finrank_pos

theorem shift_slope_mu : ShiftMu := by
  intro K _ _ _ _ d X hX N N' hN hN' σ hσ
  obtain ⟨hfin, hlcv⟩ := idxLcv_of covolume_via_basis K d X hX N N' hN hN'
  have key : ∀ w, lw w * (idx w N N' : ℝ) = -(d : ℝ) * (lw w * (σ w : ℝ)) := fun w => by
    rw [shift_index_formula K d N N' hN w (σ w) (hσ w)]
    push_cast
    ring
  have hsum : ∑ᶠ w : HeightOneSpectrum (𝓞 K), lw w * (idx w N N' : ℝ) =
      -(d : ℝ) * ∑ᶠ w : HeightOneSpectrum (𝓞 K), lw w * (σ w : ℝ) := by
    simp_rw [key]
    rcases Nat.eq_zero_or_pos d with hd | hd
    · subst hd
      simp
    · have hd' : (-(d : ℝ)) ≠ 0 := by
        have : (0 : ℝ) < d := by exact_mod_cast hd
        linarith
      have hfs : (Function.support fun w : HeightOneSpectrum (𝓞 K) => lw w * (σ w : ℝ)).Finite := by
        refine hfin.subset (fun w hw => ?_)
        simp only [Function.mem_support] at hw ⊢
        rw [key]
        exact mul_ne_zero hd' hw
      exact (mul_finsum _ _).symm
  have hL : lcv X N' = lcv X N - 2 * (d : ℝ) * ∑ᶠ w : HeightOneSpectrum (𝓞 K), lw w * (σ w : ℝ) := by
    rw [hlcv, hsum]
    ring
  refine ⟨hL, fun hd => ⟨?_, ?_⟩⟩
  · have hd' : (-(d : ℝ)) ≠ 0 := by
      have : (0 : ℝ) < d := by exact_mod_cast hd
      linarith
    refine hfin.subset (fun w hw => ?_)
    simp only [Function.mem_support] at hw ⊢
    rw [key]
    refine mul_ne_zero hd' (mul_ne_zero (shift_lw_pos w).ne' ?_)
    exact_mod_cast hw
  · rw [mu_log_conductor K d hd X hX N' hN', mu_log_conductor K d hd X hX N hN, hL]
    have : (0 : ℝ) < d := by exact_mod_cast hd
    field_simp
    ring

section Prime

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem shift_above_iff (p : ℕ) (hp : p.Prime) (w : HeightOneSpectrum (𝓞 K)) :
    Above p w ↔ 0 < vw w (p : K) := by
  have hp0 : (p : 𝓞 K) ≠ 0 := by
    first
    | exact Nat.cast_ne_zero.mpr hp.ne_zero
    | intro h
      have h' : ((p : 𝓞 K) : K) = 0 := by rw [h]; simp
      have h'' : (p : K) = 0 := by simpa using h'
      exact hp.ne_zero (by exact_mod_cast h'')
  have hI : Ideal.span {(p : 𝓞 K)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact hp0
  have hv : vw w (p : K) =
      ((Associates.mk w.asIdeal).count (Associates.mk (Ideal.span {(p : 𝓞 K)})).factors : ℤ) := by
    rw [← FractionalIdeal.count_coe K w hI, FractionalIdeal.coeIdeal_span_singleton]
    simp [vw]
  show (p : 𝓞 K) ∈ w.asIdeal ↔ _
  rw [hv, ← Ideal.dvd_span_singleton, ← Associates.count_ne_zero_iff_dvd hI w.irreducible]
  omega

theorem shift_vw_nat_nonneg (p : ℕ) (w : HeightOneSpectrum (𝓞 K)) : 0 ≤ vw w (p : K) := by
  have h := (valuation_basic_properties K w).2.2.2.2.2.2 (p : 𝓞 K)
  simpa using h

variable [IsTotallyComplex K]

theorem shift_sum_e (p : ℕ) (hp : p.Prime) :
    (Function.support fun w : HeightOneSpectrum (𝓞 K) => lw w * (vw w (p : K) : ℝ)).Finite ∧
    ∑ᶠ w : HeightOneSpectrum (𝓞 K), lw w * (vw w (p : K) : ℝ) = Real.log p := by
  have hpK : (p : K) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  obtain ⟨hfin, hsum⟩ := prod_formula' K (p : K) hpK
  refine ⟨hfin, ?_⟩
  rw [← hsum]
  have hnorm : ∀ v : InfinitePlace K, Real.log ‖v.embedding (p : K)‖ = Real.log p := by
    intro v
    simp
  simp only [hnorm, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have h2 := Formalism.HN.sizeMu_finrank_eq K
  unfold Formalism.HN.nPl at h2
  have hc : (Fintype.card (InfinitePlace K) : ℝ) ≠ 0 := by
    have h1 : 0 < Module.finrank ℚ K := Module.finrank_pos
    have h3 : Fintype.card (InfinitePlace K) ≠ 0 := by omega
    exact_mod_cast h3
  have hn' : (Module.finrank ℚ K : ℝ) = 2 * Fintype.card (InfinitePlace K) := by
    exact_mod_cast h2
  rw [hn']
  field_simp

theorem shift_above_finite (p : ℕ) (hp : p.Prime) :
    {w : HeightOneSpectrum (𝓞 K) | Above p w}.Finite := by
  have hp0 : (p : 𝓞 K) ≠ 0 := by
    first
    | exact Nat.cast_ne_zero.mpr hp.ne_zero
    | intro h
      have h' : ((p : 𝓞 K) : K) = 0 := by rw [h]; simp
      have h'' : (p : K) = 0 := by simpa using h'
      exact hp.ne_zero (by exact_mod_cast h'')
  have hI : Ideal.span {(p : 𝓞 K)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact hp0
  refine (Ideal.finite_factors hI).subset ?_
  intro w hw
  exact Ideal.dvd_span_singleton.mpr hw

theorem shift_sum_e_finset (p : ℕ) (hp : p.Prime) :
    ∑ w ∈ (shift_above_finite (K := K) p hp).toFinset, lw w * (vw w (p : K) : ℝ) = Real.log p := by
  rw [← (shift_sum_e (K := K) p hp).2]
  symm
  apply finsum_eq_sum_of_support_subset
  intro w hw
  simp only [Function.mem_support, ne_eq] at hw
  rw [Set.Finite.coe_toFinset, Set.mem_setOf_eq, shift_above_iff p hp]
  have h1 : (vw w (p : K) : ℝ) ≠ 0 := right_ne_zero_of_mul hw
  have h2 : vw w (p : K) ≠ 0 := by exact_mod_cast h1
  have h3 := shift_vw_nat_nonneg (K := K) p w
  omega

theorem shift_sum_above (p : ℕ) (hp : p.Prime) :
    ∑ᶠ (w : HeightOneSpectrum (𝓞 K)) (_ : Above p w), lw w =
      ∑ w ∈ (shift_above_finite (K := K) p hp).toFinset, lw w := by
  exact finsum_mem_eq_finite_toFinset_sum lw (shift_above_finite p hp)

theorem shift_sum_above_le (p : ℕ) (hp : p.Prime) :
    ∑ᶠ (w : HeightOneSpectrum (𝓞 K)) (_ : Above p w), lw w ≤ Real.log p := by
  rw [shift_sum_above (K := K) p hp, ← shift_sum_e_finset (K := K) p hp]
  apply Finset.sum_le_sum
  intro w hw
  rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, shift_above_iff p hp] at hw
  have h0 : (1 : ℤ) ≤ vw w (p : K) := by omega
  have h1 : (1 : ℝ) ≤ (vw w (p : K) : ℝ) := by exact_mod_cast h0
  have h2 := shift_lw_pos w
  nlinarith

end Prime

theorem lattice_weight_sum_prime : LwSumPrime := by
  intro K _ _ _ _ p hp
  have hsum := shift_sum_e (K := K) p hp
  have hlogp : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hex : ∃ w : HeightOneSpectrum (𝓞 K), Above p w := by
    by_contra hno
    push_neg at hno
    have h0 : ∀ w : HeightOneSpectrum (𝓞 K), lw w * (vw w (p : K) : ℝ) = 0 := by
      intro w
      have h1 : ¬ 0 < vw w (p : K) := fun h => hno w ((shift_above_iff p hp w).2 h)
      have h3 := shift_vw_nat_nonneg (K := K) p w
      have h2 : vw w (p : K) = 0 := by omega
      rw [h2]
      simp
    have h4 := hsum.2
    rw [finsum_congr h0, finsum_zero] at h4
    linarith
  refine ⟨shift_above_finite (K := K) p hp, hex, fun w => shift_above_iff p hp w,
    fun w => shift_lw_pos w, hsum.2, shift_sum_above_le (K := K) p hp, ?_⟩
  intro e he
  have he0 : (0 : ℝ) < e := by
    obtain ⟨w0, hw0⟩ := hex
    have h5 := (shift_above_iff p hp w0).1 hw0
    rw [he w0 hw0] at h5
    exact_mod_cast h5
  rw [eq_div_iff he0.ne', shift_sum_above (K := K) p hp, Finset.sum_mul,
    ← shift_sum_e_finset (K := K) p hp]
  apply Finset.sum_congr rfl
  intro w hw
  rw [Set.Finite.mem_toFinset] at hw
  rw [he w hw]

section Unit

variable {K : Type} [Field K] [NumberField K] [StarRing K] {d : ℕ}

theorem shift_vw_alg (w : HeightOneSpectrum (𝓞 K)) (x : 𝓞 K) :
    vw w (x : K) = FractionalIdeal.count K w
      (FractionalIdeal.spanSingleton (𝓞 K)⁰ (algebraMap (𝓞 K) K x)) := rfl

theorem shift_coe_ne_zero {x : 𝓞 K} (hx : x ≠ 0) : (x : K) ≠ 0 := by
  first
  | simpa using hx
  | exact_mod_cast hx

theorem shift_decomp (w : HeightOneSpectrum (𝓞 K)) :
    ∃ ϖ : 𝓞 K, ϖ ≠ 0 ∧ vw w (ϖ : K) = 1 ∧
      ∀ (n : ℕ) (x : 𝓞 K), x ≠ 0 → vw w (x : K) = n →
        ∃ t s : 𝓞 K, t ∉ w.asIdeal ∧ s ∉ w.asIdeal ∧ t * x = ϖ ^ n * s := by
  obtain ⟨ϖ, _, hϖ0, hcnt, t0, ht0, hdiv⟩ := idxChange_unif (K := K) w
  refine ⟨ϖ, hϖ0, hcnt, ?_⟩
  intro n
  induction n with
  | zero =>
    intro x hx hv
    refine ⟨1, x, ?_, ?_, by simp⟩
    · exact fun h => w.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h)
    · intro h
      have := idxChange_cnt_mem (K := K) w hx h
      rw [← shift_vw_alg, hv] at this
      simp at this
  | succ n ih =>
    intro x hx hv
    have hxw : x ∈ w.asIdeal := by
      by_contra h
      have := idxChange_cnt_unit (K := K) w h
      rw [← shift_vw_alg, hv] at this
      push_cast at this
      omega
    obtain ⟨u, hu⟩ := hdiv x hxw
    have ht00 : t0 ≠ 0 := fun h => ht0 (h ▸ w.asIdeal.zero_mem)
    have hu0 : u ≠ 0 := by
      intro h
      rw [h, mul_zero] at hu
      exact (mul_ne_zero ht00 hx) hu
    have hvu : vw w (u : K) = n := by
      have h1 : ((t0 : 𝓞 K) : K) * (x : K) = (ϖ : K) * (u : K) := by exact_mod_cast congrArg (fun z : 𝓞 K => (z : K)) hu
      have h2 := congrArg (vw w) h1
      rw [ValuationRepresentative.vw_mul w _ _ (shift_coe_ne_zero ht00) (shift_coe_ne_zero hx),
        ValuationRepresentative.vw_mul w _ _ (shift_coe_ne_zero hϖ0) (shift_coe_ne_zero hu0), hv] at h2
      have h3 : vw w (t0 : K) = 0 := idxChange_cnt_unit (K := K) w ht0
      have h4 : vw w (ϖ : K) = 1 := hcnt
      rw [h3, h4] at h2
      push_cast at h2
      omega
    obtain ⟨t, s, ht, hs, hts⟩ := ih u hu0 hvu
    refine ⟨t * t0, s, w.isPrime.mul_notMem ht ht0, hs, ?_⟩
    calc t * t0 * x = t * (t0 * x) := by ring
      _ = t * (ϖ * u) := by rw [hu]
      _ = ϖ * (t * u) := by ring
      _ = ϖ * (ϖ ^ n * s) := by rw [hts]
      _ = ϖ ^ (n + 1) * s := by ring

theorem shift_int_of_nonneg (w : HeightOneSpectrum (𝓞 K)) (b : K) (hb : b ≠ 0) (hv : 0 ≤ vw w b) :
    ∃ t y : 𝓞 K, t ∉ w.asIdeal ∧ (t : K) * b = (y : K) := by
  obtain ⟨ϖ, hϖ0, _, hdec⟩ := shift_decomp w
  obtain ⟨x, y, hy, hxy⟩ := IsFractionRing.div_surjective (A := 𝓞 K) b
  have hy0 : y ≠ 0 := nonZeroDivisors.ne_zero hy
  have hyK : (y : K) ≠ 0 := shift_coe_ne_zero hy0
  change (x : K) / (y : K) = b at hxy
  have hx0 : x ≠ 0 := by
    intro h
    rw [h] at hxy
    apply hb
    rw [← hxy]
    simp
  have hxK : (x : K) ≠ 0 := shift_coe_ne_zero hx0
  have hvx : vw w (x : K) = vw w b + vw w (y : K) := by
    rw [← ValuationRepresentative.vw_mul w _ _ hb hyK, ← hxy, div_mul_cancel₀ _ hyK]
  obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le (ValuationRepresentative.vw_int_nonneg w y)
  obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le hv
  have hvx' : vw w (x : K) = ((k + m : ℕ) : ℤ) := by
    rw [hvx, hm, hk]
    push_cast
    ring
  obtain ⟨t1, s1, ht1, hs1, h1⟩ := hdec (k + m) x hx0 hvx'
  obtain ⟨t2, s2, ht2, hs2, h2⟩ := hdec m y hy0 hm
  refine ⟨t1 * s2, ϖ ^ k * s1 * t2, w.isPrime.mul_notMem ht1 hs2, ?_⟩
  rw [← hxy, mul_div_assoc', div_eq_iff hyK]
  have : t1 * s2 * x = ϖ ^ k * s1 * t2 * y := by
    calc t1 * s2 * x = s2 * (t1 * x) := by ring
      _ = s2 * (ϖ ^ (k + m) * s1) := by rw [h1]
      _ = ϖ ^ k * s1 * (ϖ ^ m * s2) := by ring
      _ = ϖ ^ k * s1 * (t2 * y) := by rw [h2]
      _ = ϖ ^ k * s1 * t2 * y := by ring
  exact_mod_cast congrArg (fun z : 𝓞 K => (z : K)) this

theorem localizationAt_le_of_le_localizationAt (w : HeightOneSpectrum (𝓞 K)) {A B : Submodule (𝓞 K) (Fin d → K)}
    (h : A ≤ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal B) :
    Formalism.HermitianLatticesTheory.localization₂ w.asIdeal A ≤ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal B := by
  intro x hx
  rw [imageLcv_mem_locP] at hx
  obtain ⟨s, hs, hsx⟩ := hx
  obtain ⟨t, ht, htx⟩ := (imageLcv_mem_locP _ _ _).1 (h hsx)
  rw [imageLcv_mem_locP]
  exact ⟨t * s, w.asIdeal.primeCompl.mul_mem ht hs, by rw [mul_smul]; exact htx⟩

theorem shift_smul_mem_locP (w : HeightOneSpectrum (𝓞 K)) (N : Submodule (𝓞 K) (Fin d → K))
    {a b : K} (ha : a ≠ 0) (hab : b = 0 ∨ vw w a ≤ vw w b) {x : Fin d → K} (hx : x ∈ N) :
    b • x ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (smulLat a N) := by
  rcases hab with rfl | hab
  · rw [zero_smul]
    exact Submodule.zero_mem _
  · by_cases hb : b = 0
    · subst hb
      rw [zero_smul]
      exact Submodule.zero_mem _
    · have hv : 0 ≤ vw w (b / a) := by
        rw [div_eq_mul_inv, (valuation_basic_properties K w).1 b a⁻¹ hb (inv_ne_zero ha),
          (valuation_basic_properties K w).2.2.2.2.2.1]
        linarith
      obtain ⟨t, y, ht, hty⟩ := shift_int_of_nonneg w (b / a) (div_ne_zero hb ha) hv
      have key : a * (y : K) = (t : K) * b := by
        rw [← hty]
        field_simp
      rw [imageLcv_mem_locP]
      refine ⟨t, ht, ?_⟩
      rw [shift_mem_smulLat]
      refine ⟨y • x, N.smul_mem y hx, ?_⟩
      ext i
      simp only [Pi.smul_apply, smul_eq_mul]
      simp only [Algebra.smul_def]
      have hc : ∀ c : 𝓞 K, algebraMap (𝓞 K) K c = (c : K) := fun c => rfl
      rw [hc, hc]
      linear_combination (x i) * key

theorem shift_exists_val (w : HeightOneSpectrum (𝓞 K)) (s : ℤ) : ∃ a : K, a ≠ 0 ∧ vw w a = s := by
  obtain ⟨ϖ, hϖ0, hϖ1, -⟩ := shift_decomp w
  have hϖ : (ϖ : K) ≠ 0 := shift_coe_ne_zero hϖ0
  rcases Int.eq_nat_or_neg s with ⟨n, rfl | rfl⟩
  · refine ⟨(ϖ : K) ^ n, pow_ne_zero n hϖ, ?_⟩
    rw [shift_vw_pow w _ hϖ, hϖ1, mul_one]
  · refine ⟨((ϖ : K) ^ n)⁻¹, inv_ne_zero (pow_ne_zero n hϖ), ?_⟩
    rw [(valuation_basic_properties K w).2.2.2.2.2.1, shift_vw_pow w _ hϖ, hϖ1, mul_one]

end Unit

section Ideal

variable {K : Type} [Field K] [NumberField K] [StarRing K] {d : ℕ}

theorem shift_shiftIdeal_ne_zero (σ : HeightOneSpectrum (𝓞 K) → ℤ) : shiftIdeal σ ≠ 0 := by
  unfold shiftIdeal
  apply finprod_induction (fun I : FractionalIdeal (𝓞 K)⁰ K => I ≠ 0)
  · exact one_ne_zero
  · intro x y hx hy
    exact mul_ne_zero hx hy
  · intro v
    exact zpow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.mpr v.ne_bot)

theorem shift_count_shiftIdeal (σ : HeightOneSpectrum (𝓞 K) → ℤ) (hσ : (Function.support σ).Finite)
    (w : HeightOneSpectrum (𝓞 K)) : FractionalIdeal.count K w (shiftIdeal σ) = -σ w := by
  unfold shiftIdeal
  exact FractionalIdeal.count_finprod K w (fun w => -σ w)
    (Filter.eventually_cofinite.2 (hσ.subset (fun x hx => by simpa using hx)))

theorem shift_count_le_vw (I : FractionalIdeal (𝓞 K)⁰ K) (w : HeightOneSpectrum (𝓞 K)) {b : K}
    (hb0 : b ≠ 0) (hb : b ∈ I) : FractionalIdeal.count K w I ≤ vw w b := by
  have hI : I ≠ 0 := by
    intro h
    rw [h, FractionalIdeal.mem_zero_iff] at hb
    exact hb0 hb
  have hle : FractionalIdeal.spanSingleton (𝓞 K)⁰ b ≤ I :=
    (FractionalIdeal.spanSingleton_le_iff_mem).mpr hb
  have hJ : I⁻¹ * FractionalIdeal.spanSingleton (𝓞 K)⁰ b ≤ 1 := by
    calc I⁻¹ * FractionalIdeal.spanSingleton (𝓞 K)⁰ b ≤ I⁻¹ * I := by gcongr
      _ = 1 := inv_mul_cancel₀ hI
  obtain ⟨J, hJe⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.mp hJ
  have hsp0 : FractionalIdeal.spanSingleton (𝓞 K)⁰ b ≠ 0 := by
    rw [Ne, FractionalIdeal.spanSingleton_eq_zero_iff]; exact hb0
  have hJ0 : (J : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := by
    rw [hJe]; exact mul_ne_zero (inv_ne_zero hI) hsp0
  have e : FractionalIdeal.spanSingleton (𝓞 K)⁰ b = I * (J : FractionalIdeal (𝓞 K)⁰ K) := by
    rw [hJe, ← mul_assoc, mul_inv_cancel₀ hI, one_mul]
  have hv : vw w b = FractionalIdeal.count K w I + FractionalIdeal.count K w (J : FractionalIdeal (𝓞 K)⁰ K) := by
    show FractionalIdeal.count K w (FractionalIdeal.spanSingleton (𝓞 K)⁰ b) = _
    rw [e, FractionalIdeal.count_mul K w hI hJ0]
  have hnn := FractionalIdeal.count_coe_nonneg K w J
  omega

theorem shift_mem_ideal_loc (I : FractionalIdeal (𝓞 K)⁰ K) (hI : I ≠ 0) (w : HeightOneSpectrum (𝓞 K))
    {a : K} (ha : a ≠ 0) (hv : vw w a = FractionalIdeal.count K w I) :
    ∃ t : 𝓞 K, t ∉ w.asIdeal ∧ (t : K) * a ∈ I := by
  set J : FractionalIdeal (𝓞 K)⁰ K := FractionalIdeal.spanSingleton (𝓞 K)⁰ a * I⁻¹ with hJ
  have hsa : FractionalIdeal.spanSingleton (𝓞 K)⁰ a ≠ 0 :=
    FractionalIdeal.spanSingleton_ne_zero_iff.mpr ha
  have hJ0 : J ≠ 0 := mul_ne_zero hsa (inv_ne_zero hI)
  have hcJ : FractionalIdeal.count K w J = 0 := by
    rw [hJ, FractionalIdeal.count_mul K w hsa (inv_ne_zero hI), FractionalIdeal.count_inv]
    unfold vw at hv
    omega
  have hfg : (J : Submodule (𝓞 K) K).FG := by
    have : IsNoetherian (𝓞 K) (J : Submodule (𝓞 K) K) := FractionalIdeal.isNoetherian J
    exact (Submodule.fg_top _).mp (IsNoetherian.noetherian ⊤)
  have hle : (J : Submodule (𝓞 K) K) ≤
      Formalism.HermitianLatticesTheory.locS w.asIdeal.primeCompl (1 : Submodule (𝓞 K) K) := by
    intro b hb
    by_cases hb0 : b = 0
    · rw [hb0]; exact Submodule.zero_mem _
    have h1 := shift_count_le_vw J w hb0 hb
    rw [hcJ] at h1
    obtain ⟨t, y, ht, hty⟩ := shift_int_of_nonneg w b hb0 h1
    refine ⟨t, ht, ?_⟩
    rw [Submodule.mem_one]
    exact ⟨y, hty.symm⟩
  obtain ⟨t, ht, htJ⟩ := Formalism.HermitianLatticesTheory.indexBasic_denom w.asIdeal.primeCompl _ _ hfg hle
  refine ⟨t, ht, ?_⟩
  have h2 : FractionalIdeal.spanSingleton (𝓞 K)⁰ (t : K) * J ≤ 1 := by
    rw [FractionalIdeal.spanSingleton_mul_le_iff]
    intro z hz
    have h5 := htJ z hz
    rw [← FractionalIdeal.mem_coe, FractionalIdeal.coe_one]
    exact h5
  have h3 : FractionalIdeal.spanSingleton (𝓞 K)⁰ ((t : K) * a) ≤ I := by
    have h4 : FractionalIdeal.spanSingleton (𝓞 K)⁰ ((t : K) * a) =
        FractionalIdeal.spanSingleton (𝓞 K)⁰ (t : K) * J * I := by
      rw [hJ, ← FractionalIdeal.spanSingleton_mul_spanSingleton, mul_assoc, mul_assoc,
        inv_mul_cancel₀ hI, mul_one]
    rw [h4]
    calc FractionalIdeal.spanSingleton (𝓞 K)⁰ (t : K) * J * I ≤ 1 * I :=
          mul_le_mul_left h2 I
      _ = I := one_mul I
  exact (FractionalIdeal.spanSingleton_le_iff_mem).mp h3

theorem localizationAt_fractionalIdeal_smul_eq_smul (I : FractionalIdeal (𝓞 K)⁰ K) (hI : I ≠ 0)
    (w : HeightOneSpectrum (𝓞 K)) (N : Submodule (𝓞 K) (Fin d → K))
    {a : K} (ha : a ≠ 0) (hv : vw w a = FractionalIdeal.count K w I) :
    Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (Formalism.HermitianLatticesTheory.idealSmul (I : Submodule (𝓞 K) K) N) =
      Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (smulLat a N) := by
  apply le_antisymm
  · apply localizationAt_le_of_le_localizationAt
    unfold Formalism.HermitianLatticesTheory.idealSmul
    rw [Submodule.span_le]
    rintro z ⟨b, hb, x, hx, rfl⟩
    refine shift_smul_mem_locP w N ha ?_ hx
    by_cases hb0 : b = 0
    · exact Or.inl hb0
    · right
      rw [hv]
      exact shift_count_le_vw I w hb0 hb
  · apply localizationAt_le_of_le_localizationAt
    intro z hz
    obtain ⟨x, hx, rfl⟩ := (shift_mem_smulLat a N z).mp hz
    obtain ⟨t, ht, hta⟩ := shift_mem_ideal_loc I hI w ha hv
    refine ⟨t, ht, ?_⟩
    have e : t • (a • x) = ((t : K) * a) • x := by
      rw [mul_smul]
      rfl
    rw [e]
    exact Submodule.subset_span ⟨_, hta, x, hx, rfl⟩

theorem shift_smulLat_lattice (a : K) (ha : a ≠ 0) (N : Submodule (𝓞 K) (Fin d → K))
    (hN : Submodule.IsLattice K N) : Submodule.IsLattice K (smulLat a N) := by
  refine ⟨hN.fg.map _, ?_⟩
  have hset : ((smulLat a N : Submodule (𝓞 K) (Fin d → K)) : Set (Fin d → K)) =
      (LinearMap.lsmul K (Fin d → K) a) '' (N : Set (Fin d → K)) := by
    simp [smulLat]
  rw [hset, ← Submodule.map_span, hN.span_eq_top, Submodule.map_top, LinearMap.range_eq_top]
  intro v
  exact ⟨a⁻¹ • v, by simp [smul_smul, mul_inv_cancel₀ ha, inv_mul_cancel₀ ha]⟩

theorem shift_idealSmul_lattice (I : FractionalIdeal (𝓞 K)⁰ K) (hI : I ≠ 0)
    (N : Submodule (𝓞 K) (Fin d → K)) (hN : Submodule.IsLattice K N) :
    Submodule.IsLattice K (Formalism.HermitianLatticesTheory.idealSmul (I : Submodule (𝓞 K) K) N) := by
  have hNfg : N.FG := Submodule.IsLattice.fg (self := hN)
  obtain ⟨c, hc, hcI⟩ := I.isFractional
  have hc0 : c ≠ 0 := nonZeroDivisors.ne_zero hc
  have hcK : (c : K) ≠ 0 := shift_coe_ne_zero hc0
  constructor
  · have hle : smulLat (c : K) (Formalism.HermitianLatticesTheory.idealSmul (I : Submodule (𝓞 K) K) N) ≤ N := by
      unfold smulLat Formalism.HermitianLatticesTheory.idealSmul
      rw [Submodule.map_span, Submodule.span_le]
      rintro _ ⟨_, ⟨b, hb, x, hx, rfl⟩, rfl⟩
      obtain ⟨y, hy⟩ := hcI b hb
      show (c : K) • (b • x) ∈ N
      have e : (c : K) • (b • x) = y • x := by
        rw [smul_smul]
        have : (c : K) * b = (y : K) := by
          rw [show (y : K) = algebraMap (𝓞 K) K y from rfl, hy]
          rfl
        rw [this]
        rfl
      rw [e]
      exact N.smul_mem y hx
    have hnoe : IsNoetherian (𝓞 K) N := isNoetherian_of_fg_of_noetherian N hNfg
    have hfg : (smulLat (c : K) (Formalism.HermitianLatticesTheory.idealSmul (I : Submodule (𝓞 K) K) N)).FG :=
      isNoetherian_submodule.mp hnoe _ hle
    rw [shift_smulLat_eq_map _ hcK] at hfg
    exact Submodule.fg_of_fg_map_injective _ (shiftEquiv d (c : K) hcK).injective hfg
  · obtain ⟨b, hb, hb0⟩ := FractionalIdeal.exists_ne_zero_mem_isInteger hI
    have hbK : (b : K) ≠ 0 := shift_coe_ne_zero hb
    have hle : smulLat (b : K) N ≤ Formalism.HermitianLatticesTheory.idealSmul (I : Submodule (𝓞 K) K) N := by
      intro z hz
      obtain ⟨x, hx, rfl⟩ := (shift_mem_smulLat _ N z).mp hz
      exact Submodule.subset_span ⟨_, hb0, x, hx, rfl⟩
    have h1 := Submodule.IsLattice.span_eq_top (self := shift_smulLat_lattice (b : K) hbK N hN)
    rw [eq_top_iff, ← h1]
    exact Submodule.span_mono hle

theorem shift_eq_of_locP {A B : Submodule (𝓞 K) (Fin d → K)}
    (h : ∀ w : HeightOneSpectrum (𝓞 K), Formalism.HermitianLatticesTheory.localization₂ w.asIdeal A = Formalism.HermitianLatticesTheory.localization₂ w.asIdeal B) :
    A = B := by
  have key : ∀ {A B : Submodule (𝓞 K) (Fin d → K)},
      (∀ w : HeightOneSpectrum (𝓞 K), Formalism.HermitianLatticesTheory.localization₂ w.asIdeal A = Formalism.HermitianLatticesTheory.localization₂ w.asIdeal B) → A ≤ B := by
    intro A B h x hx
    by_contra hxB
    let I : Ideal (𝓞 K) := B.comap (LinearMap.toSpanSingleton (𝓞 K) (Fin d → K) x)
    have hmem : ∀ t, t ∈ I ↔ t • x ∈ B := fun t => by
      simp [I, Submodule.mem_comap, LinearMap.toSpanSingleton_apply]
    have hI : I ≠ ⊤ := by
      intro htop
      have h1 : (1 : 𝓞 K) ∈ I := htop ▸ Submodule.mem_top
      rw [hmem, one_smul] at h1
      exact hxB h1
    obtain ⟨M, hM, hIM⟩ := Ideal.exists_le_maximal I hI
    have hMne : M ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hM (NumberField.RingOfIntegers.not_isField K)
    let w : HeightOneSpectrum (𝓞 K) := ⟨M, hM.isPrime, hMne⟩
    have hxA : x ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal A :=
      (imageLcv_mem_locP _ _ _).2 ⟨1, w.asIdeal.primeCompl.one_mem, by rw [one_smul]; exact hx⟩
    rw [h w] at hxA
    obtain ⟨s, hs, hsx⟩ := (imageLcv_mem_locP _ _ _).1 hxA
    exact hs (hIM ((hmem s).mpr hsx))
  exact le_antisymm (key h) (key fun w => (h w).symm)

end Ideal

theorem shift_existence : ShiftEx := by
  intro K _ _ _ d N hN σ hσ
  have hI := shift_shiftIdeal_ne_zero σ
  have hsh : IsShift N (Formalism.HermitianLatticesTheory.idealSmul (shiftIdeal σ : Submodule (𝓞 K) K) N) σ := by
    intro w
    obtain ⟨a, ha, hv⟩ := shift_exists_val w (-σ w)
    exact ⟨a, ha, hv, localizationAt_fractionalIdeal_smul_eq_smul _ hI w N ha (by rw [hv, shift_count_shiftIdeal σ hσ])⟩
  refine ⟨hsh, shift_idealSmul_lattice _ hI N hN, ?_⟩
  intro N' hN'
  apply shift_eq_of_locP
  intro w
  obtain ⟨a, ha, hv, hl⟩ := hN' w
  rw [hl]
  exact (localizationAt_fractionalIdeal_smul_eq_smul _ hI w N ha (by rw [hv, shift_count_shiftIdeal σ hσ])).symm

private theorem vw_eq_zero_of_not_mem_asIdeal {K : Type} [Field K] [NumberField K] [StarRing K] (w : HeightOneSpectrum (𝓞 K))
    {t : 𝓞 K} (ht : t ∉ w.asIdeal) : vw w (t : K) = 0 := by
  have ht0 : t ≠ 0 := by
    rintro rfl
    exact ht w.asIdeal.zero_mem
  have hI : Ideal.span {t} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact ht0
  have hv : vw w (t : K) =
      ((Associates.mk w.asIdeal).count (Associates.mk (Ideal.span {t})).factors : ℤ) := by
    rw [← FractionalIdeal.count_coe K w hI, FractionalIdeal.coeIdeal_span_singleton]
    simp [vw]
  have hnd : ¬ (w.asIdeal ∣ Ideal.span {t}) := by
    rw [Ideal.dvd_span_singleton]
    exact ht
  rw [← Associates.count_ne_zero_iff_dvd hI w.irreducible] at hnd
  push_neg at hnd
  rw [hv, hnd]
  rfl

theorem shift_pairing_formula : ShiftPairing := by
  intro K _ _ _ d w N N' s hsh f hf φ hφ
  obtain ⟨a, ha, hva, hloc⟩ := hsh
  have hVB := valuation_basic_properties K w
  have hφl : φ ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal N' :=
    (imageLcv_mem_locP _ _ _).2 ⟨1, w.asIdeal.primeCompl.one_mem, by rw [one_smul]; exact hφ⟩
  rw [hloc, imageLcv_mem_locP] at hφl
  obtain ⟨t, ht, htφ⟩ := hφl
  rw [shift_mem_smulLat] at htφ
  obtain ⟨ψ, hψ, hψe⟩ := htφ
  have ht' : t ∉ w.asIdeal := ht
  have ht0 : t ≠ 0 := by
    rintro rfl
    exact ht' w.asIdeal.zero_mem
  have htK : (t : K) ≠ 0 := shift_coe_ne_zero ht0
  have hft : a * f ψ = (t : K) * f φ := by
    have h1 := congrArg f hψe
    rw [map_smul, smul_eq_mul, LinearMap.map_smul_of_tower, Algebra.smul_def] at h1
    exact h1
  have hvt : vw w (t : K) = 0 := vw_eq_zero_of_not_mem_asIdeal w ht'
  rcases hf ψ hψ with h0 | hle
  · left
    rw [h0, mul_zero] at hft
    exact (mul_eq_zero.mp hft.symm).resolve_left htK
  · by_cases hfφ : f φ = 0
    · exact Or.inl hfφ
    · right
      have hfψ : f ψ ≠ 0 := by
        intro h
        rw [h, mul_zero] at hft
        exact hfφ ((mul_eq_zero.mp hft.symm).resolve_left htK)
      have e1 := hVB.1 a (f ψ) ha hfψ
      have e2 := hVB.1 (t : K) (f φ) htK hfφ
      rw [hft, e2, hvt] at e1
      omega

theorem divisor_into_dual_shift : DivIntoDualShift := by
  intro K _ _ _ d D R B n M π ι P ζ hζ0 hζ hP N N' σ τ hσ hτ hsh hR φ hφ
  refine divisor_into_dual_lattice K D R (B φ) n M π ι (fun w => P w φ) ζ hζ0 hζ (fun w F => hP w φ F)
    ?_ hR
  intro w F hF
  refine shift_pairing_formula K d w N N' (τ w) (hsh w) ((P w).flip F) ?_ φ hφ
  intro φ0 hφ0
  rcases hσ w φ0 hφ0 F hF with h | h
  · exact Or.inl h
  · right
    exact le_trans (hτ w) (Int.ceil_le.mpr h)

end Formalism.DivisionValues
