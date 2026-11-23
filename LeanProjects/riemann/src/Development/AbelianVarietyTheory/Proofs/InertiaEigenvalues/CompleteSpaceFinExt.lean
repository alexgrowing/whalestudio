import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ConvZero

noncomputable section

namespace GlobalTheory.HWL.Disc

open PowerSeries Filter Finset
open scoped PowerSeries.WithPiTopology

variable {K : Type} [NormedField K]

def SC (a : K⟦X⟧) : Prop := ∀ r : ℝ, 0 < r → r < 1 → Summable fun k : ℕ => ‖coeff k a‖ * r ^ k

def Ev (y a e : K⟦X⟧) : Prop := ∀ k : ℕ, HasSum (fun m : ℕ => coeff m a * coeff k (y ^ m)) (coeff k e)

theorem sc_of_tendsto {a : K⟦X⟧}
    (h : ∀ r : ℝ, 0 < r → r < 1 → Tendsto (fun k : ℕ => ‖coeff k a‖ * r ^ k) atTop (nhds 0)) : SC a := by
  intro r hr0 hr1
  obtain ⟨s, hrs, hs1⟩ := exists_between hr1
  have hs0 : 0 < s := hr0.trans hrs
  obtain ⟨C, hC⟩ := (h s hs0 hs1).bddAbove_range
  have hq : r / s < 1 := (div_lt_one hs0).2 hrs
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
    ((summable_geometric_of_lt_one (by positivity) hq).mul_left C)
  have h1 : ‖coeff k a‖ * s ^ k ≤ C := hC ⟨k, rfl⟩
  have h2 : ‖coeff k a‖ * r ^ k = ‖coeff k a‖ * s ^ k * (r / s) ^ k := by
    rw [div_pow]; field_simp
  rw [h2]
  exact mul_le_mul_of_nonneg_right h1 (by positivity)

theorem sc_of_le {a : K⟦X⟧} (n : ℕ) (h : ∀ k, ‖coeff k a‖ ≤ ((k : ℝ) + 1) ^ n) : SC a := by
  intro r hr0 hr1
  have h1 := summable_pow_mul_geometric_of_norm_lt_one n (r := r) (by rwa [Real.norm_of_nonneg hr0.le])
  have h2 := ((summable_nat_add_iff 1).2 h1).mul_right r⁻¹
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_) h2
  have : ((k + 1 : ℕ) : ℝ) ^ n * r ^ (k + 1) * r⁻¹ = ((k : ℝ) + 1) ^ n * r ^ k := by
    push_cast; rw [pow_succ]; field_simp
  rw [this]
  exact mul_le_mul_of_nonneg_right (h k) (by positivity)

theorem SC.add {a b : K⟦X⟧} (ha : SC a) (hb : SC b) : SC (a + b) := by
  intro r hr0 hr1
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_) ((ha r hr0 hr1).add (hb r hr0 hr1))
  rw [← add_mul, map_add]
  exact mul_le_mul_of_nonneg_right (norm_add_le _ _) (by positivity)

theorem SC.mul {a b : K⟦X⟧} (ha : SC a) (hb : SC b) : SC (a * b) := by
  intro r hr0 hr1
  have h := (summable_norm_sum_mul_antidiagonal_of_summable_norm (ha r hr0 hr1).norm (hb r hr0 hr1).norm).of_norm
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_) h
  rw [coeff_mul]
  refine (mul_le_mul_of_nonneg_right (norm_sum_le _ _) (by positivity)).trans ?_
  rw [sum_mul]
  refine sum_le_sum fun p hp => le_of_eq ?_
  rw [← mem_antidiagonal.1 hp, norm_mul, pow_add]; ring

theorem sc_coe (p : Polynomial K) : SC (p : K⟦X⟧) := by
  intro r _ _
  refine summable_of_ne_finset_zero (s := p.support) fun k hk => ?_
  simp [Polynomial.notMem_support_iff.1 hk]

theorem Ev.unique {y a e f : K⟦X⟧} (he : Ev y a e) (hf : Ev y a f) : e = f :=
  PowerSeries.ext fun k => (he k).unique (hf k)

theorem Ev.add {y a b e f : K⟦X⟧} (he : Ev y a e) (hf : Ev y b f) : Ev y (a + b) (e + f) := fun k => by
  simpa only [map_add, add_mul] using (he k).add (hf k)

theorem Ev.smul {y a e : K⟦X⟧} (c : K) (he : Ev y a e) : Ev y (c • a) (c • e) := fun k => by
  simpa only [map_smul, smul_eq_mul, mul_assoc] using (he k).mul_left c

theorem coeff_aeval_trunc (y a : K⟦X⟧) (k m : ℕ) :
    coeff k (Polynomial.aeval y (trunc m a)) = ∑ i ∈ range m, coeff i a * coeff k (y ^ i) := by
  rw [Polynomial.aeval_def, eval₂_trunc_eq_sum_range, map_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [← Algebra.smul_def, map_smul, smul_eq_mul]

theorem ev_coe (y : K⟦X⟧) (p : Polynomial K) : Ev y (p : K⟦X⟧) (Polynomial.aeval y p) := fun k => by
  have h : coeff k (Polynomial.aeval y p) = ∑ m ∈ p.support, coeff m (p : K⟦X⟧) * coeff k (y ^ m) := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_sum, Polynomial.sum, map_sum]
    refine sum_congr rfl fun i _ => ?_
    rw [← Algebra.smul_def, map_smul, smul_eq_mul, Polynomial.coeff_coe]
  rw [h]
  refine hasSum_sum_of_ne_finset_zero fun m hm => ?_
  simp [Polynomial.notMem_support_iff.1 hm]

variable [IsUltrametricDist K]

theorem norm_coeff_pow_le (y : K⟦X⟧) (k : ℕ) {r R : ℝ} (hr : 0 ≤ r) (hR : 0 ≤ R)
    (h : ∀ i ≤ k, ‖coeff i y‖ ≤ r * R ^ i) (m : ℕ) : ∀ i ≤ k, ‖coeff i (y ^ m)‖ ≤ r ^ m * R ^ i := by
  induction m with
  | zero =>
    intro i _
    rw [pow_zero, coeff_one]
    split_ifs with hi
    · simp [hi]
    · rw [norm_zero]; positivity
  | succ m ih =>
    intro i hi
    rw [pow_succ, coeff_mul]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun p hp => ?_
    have hp' := mem_antidiagonal.1 hp
    rw [norm_mul]
    refine (mul_le_mul (ih _ (by omega)) (h _ (by omega)) (norm_nonneg _) (by positivity)).trans (le_of_eq ?_)
    rw [← hp', pow_add, pow_succ]; ring

theorem exists_bound {y : K⟦X⟧} (hy : ‖constantCoeff y‖ < 1) (k : ℕ) :
    ∃ r C : ℝ, 0 < r ∧ r < 1 ∧ ∀ m, ‖coeff k (y ^ m)‖ ≤ r ^ m * C := by
  obtain ⟨r, hr1, hr2⟩ := exists_between hy
  have hr0 : 0 < r := (norm_nonneg _).trans_lt hr1
  set S : ℝ := ∑ i ∈ range (k + 1), ‖coeff i y‖ with hS
  have hS0 : 0 ≤ S := sum_nonneg fun _ _ => norm_nonneg _
  have hR1 : 1 ≤ 1 + S / r := le_add_of_nonneg_right (by positivity)
  refine ⟨r, (1 + S / r) ^ k, hr0, hr2, fun m => norm_coeff_pow_le y k hr0.le (by positivity) ?_ m k le_rfl⟩
  intro i hi
  rcases Nat.eq_zero_or_pos i with rfl | hi0
  · simpa using hr1.le
  · have h1 : ‖coeff i y‖ ≤ S :=
      single_le_sum (f := fun i => ‖coeff i y‖) (fun _ _ => norm_nonneg _) (mem_range.2 (by omega))
    have h2 : 1 + S / r ≤ (1 + S / r) ^ i := le_self_pow₀ hR1 hi0.ne'
    have h3 : r * (1 + S / r) = r + S := by field_simp
    nlinarith

theorem summable_norm {y a : K⟦X⟧} (hy : ‖constantCoeff y‖ < 1) (ha : SC a) (k : ℕ) :
    Summable fun m : ℕ => ‖coeff m a * coeff k (y ^ m)‖ := by
  obtain ⟨r, C, h0, h1, h⟩ := exists_bound hy k
  refine Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun m => ?_) ((ha r h0 h1).mul_right C)
  rw [norm_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (h m) (norm_nonneg _)

variable [CompleteSpace K]

theorem exists_ev {y a : K⟦X⟧} (hy : ‖constantCoeff y‖ < 1) (ha : SC a) : ∃ e, Ev y a e :=
  ⟨PowerSeries.mk fun k => ∑' m : ℕ, coeff m a * coeff k (y ^ m), fun k => by
    rw [coeff_mk]; exact (summable_norm hy ha k).of_norm.hasSum⟩

theorem Ev.mul {y a b e f : K⟦X⟧} (hy : ‖constantCoeff y‖ < 1) (ha : SC a) (hb : SC b)
    (he : Ev y a e) (hf : Ev y b f) : Ev y (a * b) (e * f) := fun k => by
  have h : ∀ p ∈ antidiagonal k, HasSum (fun N : ℕ => ∑ q ∈ antidiagonal N,
      (coeff q.1 a * coeff p.1 (y ^ q.1)) * (coeff q.2 b * coeff p.2 (y ^ q.2))) (coeff p.1 e * coeff p.2 f) := by
    intro p _
    rw [← (he p.1).tsum_eq, ← (hf p.2).tsum_eq,
      tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm (summable_norm hy ha _) (summable_norm hy hb _)]
    exact (summable_norm_sum_mul_antidiagonal_of_summable_norm (summable_norm hy ha _)
      (summable_norm hy hb _)).of_norm.hasSum
  have h2 := hasSum_sum h
  rw [← coeff_mul] at h2
  convert h2 using 2 with N
  rw [sum_comm, coeff_mul, sum_mul]
  refine sum_congr rfl fun q hq => ?_
  rw [← mem_antidiagonal.1 hq, pow_add, coeff_mul, mul_sum]
  exact sum_congr rfl fun p _ => by ring

theorem ev_X (y : K⟦X⟧) : Ev y X y := by simpa using ev_coe y Polynomial.X

def lg (K : Type) [NormedField K] : K⟦X⟧ := PowerSeries.mk fun k => (-1 : K) ^ (k + 1) / (k : K)

def geo (K : Type) [NormedField K] : K⟦X⟧ := PowerSeries.mk fun k => (-1 : K) ^ k

omit [IsUltrametricDist K] [CompleteSpace K] in
theorem geo_mul : geo K * (1 + X) = 1 := by
  ext n
  cases n with
  | zero => simp [geo, mul_add]
  | succ n => simp [geo, mul_add, coeff_succ_mul_X, pow_succ, coeff_one]

omit [IsUltrametricDist K] [CompleteSpace K] in
theorem sc_geo : SC (geo K) := sc_of_le 0 fun k => by simp [geo]

omit [IsUltrametricDist K] [CompleteSpace K] in
theorem sc_lg (hn : ∀ m : ℕ, ‖(m : K)⁻¹‖ ≤ m) : SC (lg K) := sc_of_le 1 fun k => by
  have := hn k
  simp only [lg, coeff_mk, div_eq_mul_inv, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, pow_one]
  linarith

variable [CharZero K]

omit [IsUltrametricDist K] [CompleteSpace K] in
theorem derivative_lg : derivative K (lg K) = geo K := by
  ext n
  have : ((n : K) + 1) ≠ 0 := by exact_mod_cast n.succ_ne_zero
  simp only [coeff_derivative, lg, geo, coeff_mk]
  push_cast
  field_simp
  ring

theorem Ev.derivative_log {y e : K⟦X⟧} (hy : ‖constantCoeff y‖ < 1) (he : Ev y (lg K) e) :
    derivative K e * (1 + y) = derivative K y := by
  obtain ⟨g, hg⟩ := exists_ev hy (sc_geo (K := K))
  have h1 : g * (1 + y) = 1 := by
    have h := Ev.mul hy sc_geo (sc_coe (1 + Polynomial.X)) hg (ev_coe y (1 + Polynomial.X))
    have h' := ev_coe y 1
    simp only [Polynomial.coe_add, Polynomial.coe_one, Polynomial.coe_X, geo_mul, map_add, map_one,
      Polynomial.aeval_X] at h h'
    exact h.unique h'
  have h2 : derivative K e = g * derivative K y := by
    ext k
    have h3 := (hasSum_nat_add_iff' 1).2 ((he (k + 1)).mul_right ((k : K) + 1))
    have h4 := hasSum_sum fun p (_ : p ∈ antidiagonal k) => (hg p.1).mul_right (coeff p.2 (derivative K y))
    rw [← coeff_mul] at h4
    rw [← coeff_derivative] at h3
    simp only [range_one, sum_singleton, lg, coeff_mk, Nat.cast_zero, div_zero, zero_mul, sub_zero] at h3
    refine h3.unique ((congrArg (HasSum · _) (funext fun m => ?_)).mpr h4)
    have : ((m : K) + 1) ≠ 0 := by exact_mod_cast m.succ_ne_zero
    rw [mul_assoc, ← coeff_derivative, Derivation.leibniz_pow, Nat.add_sub_cancel, map_nsmul, smul_eq_mul,
      coeff_mul, nsmul_eq_mul, ← mul_assoc, mul_sum]
    refine sum_congr rfl fun p _ => ?_
    simp only [geo, coeff_mk]
    push_cast
    field_simp
    ring
  rw [h2, mul_right_comm, h1, one_mul]

theorem exists_log_factor (hn : ∀ m : ℕ, ‖(m : K)⁻¹‖ ≤ m) (n : ℕ) :
    ∃ g : K⟦X⟧, SC g ∧ ((n + 1 : ℕ) : K) • lg K = ((1 + X) ^ (n + 1) - 1) * g := by
  set y : K⟦X⟧ := (1 + X) ^ (n + 1) - 1 with hy
  have hy0 : constantCoeff y = 0 := by simp [hy]
  have hy1 : ‖constantCoeff y‖ < 1 := by simp [hy0]
  set h : K⟦X⟧ := PowerSeries.mk fun m => (-1 : K) ^ m / ((m + 1 : ℕ) : K) with hh
  have hhn : ∀ m, ‖coeff m h‖ ≤ (m : ℝ) + 1 := fun m => by
    have := hn (m + 1)
    simp only [hh, coeff_mk, div_eq_mul_inv, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    exact_mod_cast this
  have hsc : SC h := sc_of_le 1 fun m => by simpa using hhn m
  have hlg : lg K = X * h := by
    ext m
    cases m with
    | zero => simp [lg]
    | succ m => simp [lg, hh, coeff_succ_X_mul, pow_succ]
  obtain ⟨g, hg⟩ := exists_ev hy1 hsc
  have hX : SC (X : K⟦X⟧) := by simpa using sc_coe (Polynomial.X : Polynomial K)
  have hev : Ev y (lg K) (y * g) := hlg ▸ Ev.mul hy1 hX hsc (ev_X y) hg
  refine ⟨g, sc_of_le 1 fun k => ?_, ?_⟩
  · have hone : ∀ i ≤ k, ‖coeff i (1 : K⟦X⟧)‖ ≤ 1 := fun i _ => by
      rw [coeff_one]; split_ifs <;> simp
    have hb : ∀ i ≤ k, ‖coeff i (1 + X : K⟦X⟧)‖ ≤ 1 * 1 ^ i := fun i hi => by
      rw [map_add, one_pow, one_mul]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hone i hi) ?_)
      rw [coeff_X]; split_ifs <;> simp
    have hb2 : ∀ i ≤ k, ‖coeff i y‖ ≤ 1 * 1 ^ i := fun i hi => by
      rw [hy, map_sub, one_pow, one_mul, sub_eq_add_neg]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ (by rw [norm_neg]; exact hone i hi))
      simpa using norm_coeff_pow_le _ k zero_le_one zero_le_one hb (n + 1) i hi
    have hs : coeff k g = ∑ m ∈ range (k + 1), coeff m h * coeff k (y ^ m) := by
      refine (hg k).unique (hasSum_sum_of_ne_finset_zero fun m hm => ?_)
      have hd : X ^ m ∣ y ^ m := pow_dvd_pow_of_dvd (X_dvd_iff.2 hy0) m
      rw [X_pow_dvd_iff.1 hd k (by simpa using hm), mul_zero]
    rw [hs, pow_one]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun m hm => ?_
    have h1 : ‖coeff k (y ^ m)‖ ≤ 1 := by
      simpa using norm_coeff_pow_le _ k zero_le_one zero_le_one hb2 m k le_rfl
    have h2 : (m : ℝ) ≤ k := by exact_mod_cast Nat.lt_succ_iff.1 (mem_range.1 hm)
    rw [norm_mul]
    exact (mul_le_of_le_one_right (norm_nonneg _) h1).trans ((hhn m).trans (by linarith))
  · have hd := hev.derivative_log hy1
    have hne : 1 + y ≠ 0 := fun h0 => by simpa [hy0] using congrArg constantCoeff h0
    refine derivative.ext (mul_right_cancel₀ hne ?_) ?_
    · rw [hd, Derivation.map_smul, derivative_lg, hy, add_sub_cancel, map_sub, Derivation.map_one_eq_zero,
        Derivation.leibniz_pow, smul_mul_assoc, pow_succ', ← mul_assoc, geo_mul, Nat.cast_smul_eq_nsmul]
      simp
    · simp [hy0, lg]

theorem ev_log (hn : ∀ m : ℕ, ‖(m : K)⁻¹‖ ≤ m) {ζ : K} (hζ : ‖ζ - 1‖ < 1) {n : ℕ} (hn0 : n ≠ 0) (h1 : ζ ^ n = 1) :
    Ev (C ζ * exp K - 1) (lg K) X := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
  set y : K⟦X⟧ := C ζ * exp K - 1 with hy
  have hy0 : constantCoeff y = ζ - 1 := by simp [hy]
  have hy1 : ‖constantCoeff y‖ < 1 := by rwa [hy0]
  obtain ⟨e, he⟩ := exists_ev hy1 (sc_lg hn)
  obtain ⟨g, hg, hfac⟩ := exists_log_factor hn n
  obtain ⟨G, hG⟩ := exists_ev hy1 hg
  have h2 := Ev.mul hy1 (sc_coe ((1 + Polynomial.X) ^ (n + 1) - 1)) hg (ev_coe y _) hG
  simp only [Polynomial.coe_sub, Polynomial.coe_pow, Polynomial.coe_add, Polynomial.coe_one, Polynomial.coe_X,
    map_sub, map_pow, map_add, map_one, Polynomial.aeval_X] at h2
  rw [← hfac] at h2
  have h3 := congrArg constantCoeff ((he.smul _).unique h2)
  have hc : constantCoeff e = 0 := by
    have h1' : ζ ^ (n + 1) = 1 := h1
    have hne : ((n : K) + 1) ≠ 0 := by exact_mod_cast n.succ_ne_zero
    simpa [hy0, h1', hne] using h3
  have hd := he.derivative_log hy1
  have hne : 1 + y ≠ 0 := fun h0 => by
    have h4 : ζ = 0 := by simpa [hy0] using congrArg constantCoeff h0
    simp [h4] at h1
  have : e = X := by
    refine derivative.ext (mul_right_cancel₀ hne ?_) (by simp [hc])
    rw [hd, hy]
    simp [Derivation.leibniz, derivative_exp]
  exact this ▸ he

end GlobalTheory.HWL.Disc

namespace GlobalTheory.HWL

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries Filter Disc

variable {l : ℕ} [Fact l.Prime] {LL : FinExt l}

theorem completeSpace_finExt (LL : FinExt l) : CompleteSpace ↥LL.1 :=
  haveI := LL.2
  FiniteDimensional.complete ℚ_[l] ↥LL.1

theorem conv_iff_sc (a : PowerSeries ↥LL.1) : Conv a ↔ SC a :=
  ⟨fun h => sc_of_tendsto h, fun h r h0 h1 => (h r h0 h1).tendsto_atTop_zero⟩

theorem isExp_iff_ev {ζ : ↥LL.1} (hζ : ‖(ζ : Om l) - 1‖ < 1) {a : PowerSeries ↥LL.1} (ha : Conv a)
    (e : PowerSeries ↥LL.1) : IsExp ζ a e ↔ Ev (C ζ * exp ↥LL.1 - 1) a e := by
  haveI := completeSpace_finExt LL
  have hy : ‖constantCoeff (C ζ * exp ↥LL.1 - 1)‖ < 1 := by
    have : constantCoeff (C ζ * exp ↥LL.1 - 1) = ζ - 1 := by simp
    rw [this]; exact hζ
  refine forall_congr' fun k => ?_
  rw [(summable_norm hy ((conv_iff_sc a).1 ha) k).of_norm.hasSum_iff_tendsto_nat]
  simp only [coeff_aeval_trunc]
  exact tendsto_subtype_rng.symm

theorem norm_natCast_inv_le (LL : FinExt l) (m : ℕ) : ‖(m : ↥LL.1)⁻¹‖ ≤ m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  have h1 : ‖(m : ↥LL.1)‖ = ‖(m : ℚ_[l])‖ := by
    rw [← norm_algebraMap' ↥LL.1 (m : ℚ_[l]), map_natCast]
  rw [norm_inv, h1, Padic.norm_eq_zpow_neg_valuation (by exact_mod_cast hm.ne'), Padic.valuation_natCast,
    zpow_neg, inv_inv, zpow_natCast]
  exact_mod_cast Nat.le_of_dvd hm pow_padicValNat_dvd

theorem norm_integer_le_one (x : ↥(OL LL)) : ‖algebraMap ↥(OL LL) ↥LL.1 x‖ ≤ 1 := by
  have h : IsIntegral ℤ_[l] ((x : ↥LL.1) : Om l) :=
    IsIntegral.map (LL.1.val.restrictScalars ℤ_[l]) (show IsIntegral ℤ_[l] (x : ↥LL.1) from x.2)
  have hx : IsIntegral ℚ_[l] ((x : ↥LL.1) : Om l) := Algebra.IsIntegral.isIntegral _
  change ‖((x : ↥LL.1) : Om l)‖ ≤ 1
  rw [← PadicAlgCl.spectralNorm_eq, spectralNorm, spectralValue_le_one_iff (minpoly.monic hx)]
  intro n
  rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] h, Polynomial.coeff_map]
  exact ((minpoly ℤ_[l] _).coeff n).2

theorem conv_expansion (l : ℕ) [Fact l.Prime] (LL : FinExt l) (ζ : ↥LL.1) (hζ : ‖((ζ : Om l)) - 1‖ < 1) :
    (∀ a : PowerSeries ↥LL.1, Conv a → ∃! e, IsExp ζ a e) ∧
    (∀ a b e f : PowerSeries ↥LL.1, Conv a → Conv b → IsExp ζ a e → IsExp ζ b f →
      Conv (a + b) ∧ Conv (a * b) ∧ IsExp ζ (a + b) (e + f) ∧ IsExp ζ (a * b) (e * f)) ∧
    (∀ a : PowerSeries ↥(OL LL), Conv (PowerSeries.map (algebraMap ↥(OL LL) ↥LL.1) a)) ∧
    Conv (logS LL) ∧ ((∃ j : ℕ, ζ ^ l ^ j = 1) → IsExp ζ (logS LL) PowerSeries.X) := by
  haveI := completeSpace_finExt LL
  have hy : ‖constantCoeff (C ζ * exp ↥LL.1 - 1)‖ < 1 := by
    have : constantCoeff (C ζ * exp ↥LL.1 - 1) = ζ - 1 := by simp
    rw [this]; exact hζ
  have hlog : Conv (logS LL) := (conv_iff_sc _).2 (sc_lg (norm_natCast_inv_le LL))
  refine ⟨fun a ha => ?_, fun a b e f ha hb he hf => ?_, fun a => ?_, hlog, fun ⟨j, hj⟩ => ?_⟩
  · obtain ⟨e, he⟩ := exists_ev hy ((conv_iff_sc a).1 ha)
    exact ⟨e, (isExp_iff_ev hζ ha e).2 he, fun f hf => ((isExp_iff_ev hζ ha f).1 hf).unique he⟩
  · have ha' := (conv_iff_sc a).1 ha
    have hb' := (conv_iff_sc b).1 hb
    have h1 := (conv_iff_sc _).2 (ha'.add hb')
    have h2 := (conv_iff_sc _).2 (ha'.mul hb')
    rw [isExp_iff_ev hζ ha] at he
    rw [isExp_iff_ev hζ hb] at hf
    exact ⟨h1, h2, (isExp_iff_ev hζ h1 _).2 (he.add hf), (isExp_iff_ev hζ h2 _).2 (Ev.mul hy ha' hb' he hf)⟩
  · refine (conv_iff_sc _).2 (sc_of_le 0 fun k => ?_)
    rw [coeff_map, pow_zero]
    exact norm_integer_le_one _
  · exact (isExp_iff_ev hζ hlog _).2
      (ev_log (norm_natCast_inv_le LL) hζ (pow_ne_zero j (Fact.out : l.Prime).ne_zero) hj)

end GlobalTheory.HWL
