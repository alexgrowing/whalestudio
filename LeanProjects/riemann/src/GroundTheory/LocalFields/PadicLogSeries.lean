import Mathlib
import GroundTheory.LocalFields.ExistsUnitFiltrationUnitsLeAndRangePowLe
import GroundTheory.LocalFields.ExamplesCharZero

namespace GroundTheory.LocalField

open ValuativeRel IsLocalRing Topology Filter
open scoped WithZero

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

section Summation

variable (K) in

theorem exists_normalizedValuation_eq (n : ℤ) :
    ∃ y : K, normalizedValuation K y = WithZero.exp n := by
  obtain ⟨y, hy⟩ := ValuativeRel.valuation_surjective
    ((IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K).symm (WithZero.exp n))
  exact ⟨y, by rw [normalizedValuation_apply, hy]; simp⟩

variable (K) in

def valBall (n : ℤ) : AddSubgroup K where
  carrier := {x | normalizedValuation K x ≤ WithZero.exp (-n)}
  zero_mem' := by simp
  add_mem' hx hy := (normalizedValuation K).map_add_le hx hy
  neg_mem' hx := by simpa using hx

theorem mem_valBall {n : ℤ} {x : K} :
    x ∈ valBall K n ↔ normalizedValuation K x ≤ WithZero.exp (-n) := Iff.rfl

theorem valBall_antitone {m n : ℤ} (h : m ≤ n) : valBall K n ≤ valBall K m := fun x hx ↦
  hx.trans (WithZero.exp_le_exp.mpr (by omega))

theorem mul_mem_valBall {m n : ℤ} {x y : K} (hx : x ∈ valBall K m) (hy : y ∈ valBall K n) :
    x * y ∈ valBall K (m + n) := by
  rw [mem_valBall, map_mul, neg_add, WithZero.exp_add]
  exact mul_le_mul' hx hy

theorem pow_mem_valBall {n : ℤ} {x : K} (hx : x ∈ valBall K n) (k : ℕ) :
    x ^ k ∈ valBall K (k * n) := by
  induction k with
  | zero => simp [mem_valBall]
  | succ k ih =>
    rw [pow_succ]
    convert mul_mem_valBall ih hx using 2
    push_cast; ring

theorem isOpen_valBall (n : ℤ) : IsOpen (valBall K n : Set K) := by
  obtain ⟨y, hy⟩ := exists_normalizedValuation_eq K (-n)
  have hy0 : valuation K y ≠ 0 := by
    intro h
    rw [normalizedValuation_apply, h, map_zero] at hy
    exact WithZero.exp_ne_zero hy.symm
  have : (valBall K n : Set K) = {z : K | valuation K (z - 0) ≤ valuation K y} := by
    ext z
    simp only [sub_zero, SetLike.mem_coe, mem_valBall, ← hy, normalizedValuation_le_iff]
    rfl
  rw [this]
  exact isOpen_setOf_valuation_sub_le hy0

theorem isClosed_valBall (n : ℤ) : IsClosed (valBall K n : Set K) :=
  AddSubgroup.isClosed_of_isOpen _ (isOpen_valBall n)

theorem valBall_mem_nhds (n : ℤ) : (valBall K n : Set K) ∈ 𝓝 (0 : K) :=
  (isOpen_valBall n).mem_nhds (zero_mem _)

private instance t2Space_local_field_instance : T2Space K := by
  let := IsTopologicalAddGroup.rightUniformSpace K
  have := isUniformAddGroup_of_addCommGroup (G := K)
  infer_instance

instance nonarchimedeanRing : NonarchimedeanRing K where
  is_nonarchimedean U hU := by
    obtain ⟨γ, -, hγ⟩ := (IsValuativeTopology.hasBasis_nhds_zero K).mem_iff.mp hU
    exact ⟨⟨(valuation K).ltAddSubgroup γ, isOpen_setOf_valuation_lt⟩, hγ⟩

theorem tendsto_zero_iff_valBall {ι : Type*} {l : Filter ι} {f : ι → K} :
    Tendsto f l (𝓝 0) ↔ ∀ N : ℤ, ∀ᶠ i in l, f i ∈ valBall K N := by
  constructor
  · intro hf N
    exact hf (valBall_mem_nhds N)
  · intro hf
    rw [(IsValuativeTopology.hasBasis_nhds_zero K).tendsto_right_iff]
    intro γ _
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
    obtain ⟨n, -, hn⟩ := exists_pow_lt hϖ γ.ne_zero
    filter_upwards [hf n] with i hi
    refine lt_of_le_of_lt ?_ hn
    rw [← map_pow, ← normalizedValuation_le_iff, map_pow, normalizedValuation_uniformizer hϖ,
      ← WithZero.exp_nsmul]
    simpa [mem_valBall] using hi

theorem summable_of_tendsto_zero {f : ℕ → K} (hf : Tendsto f atTop (𝓝 0)) : Summable f := by
  let := IsTopologicalAddGroup.rightUniformSpace K
  have := isUniformAddGroup_of_addCommGroup (G := K)
  exact NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero (by rwa [Nat.cofinite_eq_atTop])

theorem tsum_mem_valBall {f : ℕ → K} {N : ℤ} (h : ∀ k, f k ∈ valBall K N) :
    ∑' k, f k ∈ valBall K N := by
  by_cases hs : Summable f
  · exact (isClosed_valBall N).mem_of_tendsto hs.hasSum.tendsto_sum_nat
      (Eventually.of_forall fun s ↦ AddSubgroup.sum_mem _ fun k _ ↦ h k)
  · rw [tsum_eq_zero_of_not_summable hs]
    exact zero_mem _

end Summation

section Arithmetic

theorem mul_self_le_two_pow_succ (v : ℕ) : v * v ≤ 2 ^ (v + 1) := by
  induction v with
  | zero => norm_num
  | succ v ih =>
    rcases Nat.lt_or_ge v 3 with h | h
    · interval_cases v <;> norm_num
    · rw [pow_succ]; nlinarith

theorem four_mul_padicValNat_le (p : ℕ) [hp : Fact p.Prime] (c : ℕ) {n : ℕ} (hn : n ≠ 0) :
    4 * c * padicValNat p n ≤ n + 32 * c ^ 2 := by
  set v := padicValNat p n
  have h1 : 2 ^ v ≤ p ^ v := Nat.pow_le_pow_left hp.out.two_le v
  have h2 : p ^ v ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) pow_padicValNat_dvd
  have h3 := mul_self_le_two_pow_succ v
  rw [pow_succ] at h3
  rcases Nat.lt_or_ge v (8 * c) with h | h
  · nlinarith
  · nlinarith

theorem sub_one_mul_padicValNat_lt (p : ℕ) [hp : Fact p.Prime] {n : ℕ} (hn : n ≠ 0) :
    (p - 1) * padicValNat p n < n := by
  have h : padicValNat p n ≤ padicValNat p n.factorial := by
    rw [← padicValNat_dvd_iff_le (Nat.factorial_ne_zero n)]
    exact pow_padicValNat_dvd.trans (Nat.dvd_factorial (Nat.pos_of_ne_zero hn) le_rfl)
  exact lt_of_le_of_lt (Nat.mul_le_mul_left _ h)
    (sub_one_mul_padicValNat_factorial_lt_of_ne_zero p hn)

end Arithmetic

section CharZero

variable (K) in

noncomputable def absRamificationIndex : ℕ := (ord ((ringChar 𝓀[K] : ℕ) : K)).toNat

variable (p : ℕ) [hp : Fact p.Prime] [CharP 𝓀[K] p] [CharZero K]

theorem normalizedValuation_natCast_prime :
    normalizedValuation K (p : K) = WithZero.exp (-(absRamificationIndex K : ℤ)) := by
  have hp0 : (p : K) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
  have hr : ringChar 𝓀[K] = p := ringChar.eq 𝓀[K] p
  have hlt : normalizedValuation K (p : K) < 1 := by
    rw [← map_one (normalizedValuation K), normalizedValuation_lt_iff, map_one]
    exact CharZero.valuation_p_lt_one K p
  rw [normalizedValuation_eq_exp_ord hp0] at hlt ⊢
  rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at hlt
  rw [absRamificationIndex, hr, Int.toNat_of_nonneg (by omega)]

include p in
theorem one_le_absRamificationIndex : 1 ≤ absRamificationIndex K := by
  have h := normalizedValuation_natCast_prime (K := K) p
  have hlt : normalizedValuation K (p : K) < 1 := by
    rw [← map_one (normalizedValuation K), normalizedValuation_lt_iff, map_one]
    exact CharZero.valuation_p_lt_one K p
  rw [h, ← WithZero.exp_zero, WithZero.exp_lt_exp] at hlt
  omega

omit hp [CharZero K] in
theorem normalizedValuation_natCast_of_not_dvd {m : ℕ} (hm : ¬ p ∣ m) :
    normalizedValuation K (m : K) = 1 := by
  rw [← map_one (normalizedValuation K), normalizedValuation_eq_iff, map_one]
  have := (CharZero.valuation_intCast_eq_one_iff K p (m : ℤ)).mpr (by exact_mod_cast hm)
  exact_mod_cast this

theorem normalizedValuation_natCast {n : ℕ} (hn : n ≠ 0) :
    normalizedValuation K (n : K) =
      WithZero.exp (-(absRamificationIndex K * padicValNat p n : ℤ)) := by
  obtain ⟨k, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn p hp.out.ne_one
  have hm0 : m ≠ 0 := by rintro rfl; exact hm (dvd_zero p)
  rw [padicValNat.mul (pow_ne_zero _ hp.out.ne_zero) hm0, padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd hm]
  push_cast
  rw [map_mul, map_pow, normalizedValuation_natCast_prime p,
    normalizedValuation_natCast_of_not_dvd p hm, mul_one, ← WithZero.exp_nsmul]
  congr 1
  simp; ring

theorem div_natCast_mem_valBall {a : ℤ} {x : K} (hx : x ∈ valBall K a) {n : ℕ} (hn : n ≠ 0) :
    x / n ∈ valBall K (a - absRamificationIndex K * padicValNat p n) := by
  rw [mem_valBall, map_div₀, normalizedValuation_natCast p hn, div_eq_mul_inv,
    ← WithZero.exp_neg, neg_neg, neg_sub, sub_eq_add_neg, WithZero.exp_add, mul_comm]
  exact mul_le_mul_right hx _

end CharZero

section Series

noncomputable def logSeries (x : K) : K := ∑' k : ℕ, (-1) ^ k * x ^ (k + 1) / ((k + 1 : ℕ) : K)

noncomputable def expSeries (x : K) : K := ∑' k : ℕ, x ^ k / (k.factorial : K)

variable (p : ℕ) [hp : Fact p.Prime] [CharP 𝓀[K] p] [CharZero K]

theorem logTerm_mem {a : ℤ} {x : K} (hx : x ∈ valBall K a) (k : ℕ) :
    (-1) ^ k * x ^ (k + 1) / ((k + 1 : ℕ) : K) ∈
      valBall K ((k + 1) * a - absRamificationIndex K * padicValNat p (k + 1)) := by
  have h1 : (-1 : K) ^ k * x ^ (k + 1) ∈ valBall K ((k + 1 : ℕ) * a) := by
    rw [mem_valBall, map_mul, map_pow, Valuation.map_neg, map_one, one_pow, one_mul]
    exact pow_mem_valBall hx (k + 1)
  have := div_natCast_mem_valBall p h1 (by omega : k + 1 ≠ 0)
  simpa only [Nat.cast_add, Nat.cast_one] using this

theorem expTerm_mem {a : ℤ} {x : K} (hx : x ∈ valBall K a) (k : ℕ) :
    x ^ k / (k.factorial : K) ∈
      valBall K (k * a - absRamificationIndex K * padicValNat p k.factorial) :=
  div_natCast_mem_valBall p (pow_mem_valBall hx k) (Nat.factorial_ne_zero k)

omit [CharP 𝓀[K] p] [CharZero K] in
theorem sub_one_mul_padicValNat_factorial_le (k : ℕ) :
    (p - 1) * padicValNat p k.factorial ≤ k :=
  (sub_one_mul_padicValNat_factorial k).le.trans (Nat.sub_le _ _)

include p in

theorem summable_logSeries {x : K} (hx : x ∈ valBall K 1) :
    Summable fun k : ℕ ↦ (-1) ^ k * x ^ (k + 1) / ((k + 1 : ℕ) : K) := by
  refine summable_of_tendsto_zero (tendsto_zero_iff_valBall.mpr fun N ↦ ?_)
  rw [eventually_atTop]
  set e := absRamificationIndex K
  refine ⟨4 * N.toNat + 32 * e ^ 2, fun k hk ↦ valBall_antitone ?_ (logTerm_mem p hx k)⟩
  have h1 := four_mul_padicValNat_le p e (Nat.succ_ne_zero k)
  have h2 : N ≤ (N.toNat : ℤ) := Int.self_le_toNat N
  have h3 : ((4 * N.toNat + 32 * e ^ 2 : ℕ) : ℤ) ≤ k := by exact_mod_cast hk
  have h4 : ((4 * e * padicValNat p (k + 1) : ℕ) : ℤ) ≤ ((k + 1 + 32 * e ^ 2 : ℕ) : ℤ) := by
    exact_mod_cast h1
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one,
    ] at h3 h4
  nlinarith

theorem one_le_of_lt_sub_one_mul {a : ℤ} (ha : (absRamificationIndex K : ℤ) < (p - 1 : ℤ) * a) :
    1 ≤ a := by
  have he := one_le_absRamificationIndex (K := K) p
  have hp2 : (2 : ℤ) ≤ p := by exact_mod_cast hp.out.two_le
  by_contra h
  push Not at h
  nlinarith

theorem logSeries_sub_self_mem {a : ℤ} {x : K} (hx : x ∈ valBall K a)
    (ha : (absRamificationIndex K : ℤ) < (p - 1 : ℤ) * a) :
    logSeries x - x ∈ valBall K (a + 1) := by
  have ha1 := one_le_of_lt_sub_one_mul p ha
  have hs := summable_logSeries p (valBall_antitone ha1 hx)
  rw [logSeries, hs.tsum_eq_zero_add]
  simp only [pow_zero, zero_add, pow_one, one_mul, Nat.cast_one, div_one, add_sub_cancel_left]
  refine tsum_mem_valBall fun k ↦ valBall_antitone ?_ (logTerm_mem p hx (k + 1))
  have h1 := sub_one_mul_padicValNat_lt p (Nat.succ_ne_zero (k + 1))
  set v := padicValNat p (k + 1 + 1)
  set e := absRamificationIndex K
  have hp2 : (2 : ℤ) ≤ p := by exact_mod_cast hp.out.two_le
  have h1' : ((p : ℤ) - 1) * v ≤ k + 1 := by
    have : ((p - 1) * v : ℕ) < k + 1 + 1 := h1
    have hp1 : ((p - 1 : ℕ) : ℤ) = (p : ℤ) - 1 := by
      rw [Nat.cast_sub hp.out.one_le]; simp
    have : (((p - 1) * v : ℕ) : ℤ) < k + 1 + 1 := by exact_mod_cast this
    push_cast [hp1] at this
    linarith
  have hv : (0 : ℤ) ≤ v := by positivity
  have he : (0 : ℤ) ≤ e := by positivity
  push_cast
  nlinarith [mul_le_mul_of_nonneg_left h1' he]

end Series

section Exp

variable (p : ℕ) [hp : Fact p.Prime] [CharP 𝓀[K] p] [CharZero K]

omit [CharP 𝓀[K] p] [CharZero K] in

theorem expTerm_order_bound {a : ℤ} (ha : (absRamificationIndex K : ℤ) < (p - 1 : ℤ) * a)
    (k : ℕ) : (k : ℤ) ≤ (p - 1 : ℤ) * (k * a - absRamificationIndex K * padicValNat p k.factorial)
    := by
  have h1 := sub_one_mul_padicValNat_factorial_le p k
  set v := padicValNat p k.factorial
  set e := absRamificationIndex K
  have hp2 : (2 : ℤ) ≤ p := by exact_mod_cast hp.out.two_le
  have h1' : ((p : ℤ) - 1) * v ≤ k := by
    have hp1 : ((p - 1 : ℕ) : ℤ) = (p : ℤ) - 1 := by
      rw [Nat.cast_sub hp.out.one_le]; simp
    have : (((p - 1) * v : ℕ) : ℤ) ≤ k := by exact_mod_cast h1
    push_cast [hp1] at this
    linarith
  have he : (0 : ℤ) ≤ e := by positivity
  have hk : (0 : ℤ) ≤ k := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h1' he, mul_le_mul_of_nonneg_left ha.le hk]

theorem summable_expSeries {a : ℤ} {x : K} (hx : x ∈ valBall K a)
    (ha : (absRamificationIndex K : ℤ) < (p - 1 : ℤ) * a) :
    Summable fun k : ℕ ↦ x ^ k / (k.factorial : K) := by
  refine summable_of_tendsto_zero (tendsto_zero_iff_valBall.mpr fun N ↦ ?_)
  rw [eventually_atTop]
  refine ⟨(p - 1) * N.toNat, fun k hk ↦ valBall_antitone ?_ (expTerm_mem p hx k)⟩
  have h1 := expTerm_order_bound p ha k
  have h2 : N ≤ (N.toNat : ℤ) := Int.self_le_toNat N
  have hp2 : (2 : ℤ) ≤ p := by exact_mod_cast hp.out.two_le
  have hp1 : ((p - 1 : ℕ) : ℤ) = (p : ℤ) - 1 := by
    rw [Nat.cast_sub hp.out.one_le]; simp
  have h3 : (((p - 1) * N.toNat : ℕ) : ℤ) ≤ k := by exact_mod_cast hk
  push_cast [hp1] at h3
  nlinarith

theorem expSeries_sub_one_sub_self_mem {a : ℤ} {x : K} (hx : x ∈ valBall K a)
    (ha : (absRamificationIndex K : ℤ) < (p - 1 : ℤ) * a) :
    expSeries x - 1 - x ∈ valBall K (a + 1) := by
  have hs := summable_expSeries p hx ha
  rw [expSeries, hs.tsum_eq_zero_add, ((summable_nat_add_iff 1).mpr hs).tsum_eq_zero_add]
  simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, zero_add, pow_one,
    Nat.factorial_one]
  have : ∀ t : K, 1 + (x + t) - 1 - x = t := fun t ↦ by ring
  rw [this]
  refine tsum_mem_valBall fun k ↦ valBall_antitone ?_ (expTerm_mem p hx (k + 1 + 1))
  have h1 := expTerm_order_bound p ha (k + 1 + 1)
  have h0 := sub_one_mul_padicValNat_factorial_lt_of_ne_zero p (by omega : k + 1 + 1 ≠ 0)
  set v := padicValNat p (k + 1 + 1).factorial
  set e := absRamificationIndex K
  have hp2 : (2 : ℤ) ≤ p := by exact_mod_cast hp.out.two_le
  have hp1 : ((p - 1 : ℕ) : ℤ) = (p : ℤ) - 1 := by
    rw [Nat.cast_sub hp.out.one_le]; simp
  have h0' : (((p - 1) * v : ℕ) : ℤ) < k + 1 + 1 := by exact_mod_cast h0
  push_cast [hp1] at h0' h1
  have he : (0 : ℤ) ≤ e := by positivity
  have h0'' : ((p : ℤ) - 1) * v ≤ k + 1 := by linarith
  have ha' : (e : ℤ) + 1 ≤ ((p : ℤ) - 1) * a := by linarith
  have hk : (0 : ℤ) ≤ k + 1 := by positivity
  push_cast
  nlinarith [mul_le_mul_of_nonneg_left h0'' he, mul_le_mul_of_nonneg_left ha' hk]

theorem expSeries_add {a : ℤ} {x y : K} (hx : x ∈ valBall K a) (hy : y ∈ valBall K a)
    (ha : (absRamificationIndex K : ℤ) < (p - 1 : ℤ) * a) :
    expSeries (x + y) = expSeries x * expSeries y := by
  let := IsTopologicalAddGroup.rightUniformSpace K
  have := isUniformAddGroup_of_addCommGroup (G := K)
  have hsx := summable_expSeries p hx ha
  have hsy := summable_expSeries p hy ha
  have hxy := hsx.mul_of_nonarchimedean hsy
  unfold expSeries
  rw [hsx.tsum_mul_tsum_eq_tsum_sum_antidiagonal hsy hxy]
  refine tsum_congr fun n ↦ ?_
  rw [(Commute.all x y).add_pow', Finset.sum_div]
  refine Finset.sum_congr rfl fun ij hij ↦ ?_
  obtain ⟨i, j⟩ := ij
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hij
  subst hij
  have key : ((i + j).choose i : K) * (i.factorial : K) * (j.factorial : K) =
      ((i + j).factorial : K) := by
    have h := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right i j)
    rw [Nat.add_sub_cancel_left] at h
    exact_mod_cast h
  have hi : (i.factorial : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero i)
  have hj : (j.factorial : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero j)
  have hc : ((i + j).choose i : K) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.choose_pos (Nat.le_add_right i j)).ne'
  simp only [nsmul_eq_mul]
  rw [← key]
  field_simp

theorem expSeries_sub_one_mem {a : ℤ} {x : K} (hx : x ∈ valBall K a)
    (ha : (absRamificationIndex K : ℤ) < (p - 1 : ℤ) * a) :
    expSeries x - 1 ∈ valBall K a := by
  have h := add_mem (valBall_antitone (by omega : a ≤ a + 1)
    (expSeries_sub_one_sub_self_mem p hx ha)) hx
  simpa using h

theorem logSeries_mem_valBall {a : ℤ} {x : K} (hx : x ∈ valBall K a)
    (ha : (absRamificationIndex K : ℤ) < (p - 1 : ℤ) * a) :
    logSeries x ∈ valBall K a := by
  have h := add_mem (valBall_antitone (by omega : a ≤ a + 1) (logSeries_sub_self_mem p hx ha)) hx
  simpa using h

end Exp

end GroundTheory.LocalField
