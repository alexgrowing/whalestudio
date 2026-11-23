import Mathlib
import GroundTheory.LocalFields.PadicLogSeries
import GroundTheory.LocalFields.Uniqueness
import GroundTheory.LocalFields.SeparableClosureValuation

noncomputable section

namespace GroundTheory.LocalField

open ValuativeRel MeasureTheory Measure Topology Filter TopologicalSpace
open scoped WithZero NNReal ENNReal Pointwise

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

section Topology

instance t2Space_nonarchimedeanLocalField : T2Space K := by
  let := IsTopologicalAddGroup.rightUniformSpace K
  have := isUniformAddGroup_of_addCommGroup (G := K)
  infer_instance

theorem mem_valBall_iff_le_ord {n : ℤ} {x : K} (hx : x ≠ 0) : x ∈ valBall K n ↔ n ≤ ord x := by
  rw [mem_valBall, normalizedValuation_eq_exp_ord hx, WithZero.exp_le_exp]
  omega

theorem mem_valBall_ord {x : K} : x ∈ valBall K (ord x) := by
  by_cases hx : x = 0
  · rw [hx]; exact zero_mem _
  · exact (mem_valBall_iff_le_ord hx).mpr le_rfl

theorem ord_inv {x : K} (hx : x ≠ 0) : ord x⁻¹ = -ord x := by
  have h := ord_mul hx (inv_ne_zero hx)
  rw [mul_inv_cancel₀ hx, ord_one] at h
  omega

theorem mem_valBall_zero_iff {x : K} : x ∈ valBall K 0 ↔ x ∈ 𝒪[K] := by
  rw [mem_valBall, neg_zero, WithZero.exp_zero, normalizedValuation_le_one_iff]

theorem coe_valBall_zero : (valBall K 0 : Set K) = 𝒪[K] := by
  ext x
  exact mem_valBall_zero_iff

theorem mem_valBall_one_iff {x : K} : x ∈ valBall K 1 ↔ valuation K x < 1 := by
  by_cases hx : x = 0
  · simp [hx]
  rw [mem_valBall_iff_le_ord hx, ← map_one (valuation K), ← normalizedValuation_lt_iff,
    normalizedValuation_eq_exp_ord hx, map_one, ← WithZero.exp_zero, WithZero.exp_lt_exp]
  omega

theorem mem_maximalIdeal_iff_mem_valBall_one {z : 𝒪[K]} : z ∈ 𝓂[K] ↔ (z : K) ∈ valBall K 1 := by
  rw [mem_valBall_one_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    Valuation.Integer.not_isUnit_iff_valuation_lt_one]

theorem residue_eq_residue_iff {a b : 𝒪[K]} :
    IsLocalRing.residue 𝒪[K] a = IsLocalRing.residue 𝒪[K] b ↔ (a : K) - b ∈ valBall K 1 := by
  rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff,
    mem_maximalIdeal_iff_mem_valBall_one]
  rfl

theorem smul_valBall {c : K} (hc : c ≠ 0) (n : ℤ) :
    c • (valBall K n : Set K) = valBall K (n + ord c) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    have := mul_mem_valBall (mem_valBall_ord (x := c)) hy
    rw [add_comm]
    exact this
  · intro hx
    refine ⟨c⁻¹ * x, ?_, by simp [smul_eq_mul, hc]⟩
    have h1 : c⁻¹ ∈ valBall K (-ord c) := by
      rw [← ord_inv hc]; exact mem_valBall_ord
    have := mul_mem_valBall h1 hx
    simpa using this

theorem isCompact_valBall (n : ℤ) : IsCompact (valBall K n : Set K) := by
  obtain ⟨c, hc, hcn⟩ := exists_ord_eq K n
  have h0 : IsCompact (valBall K 0 : Set K) := by
    have : (valBall K 0 : Set K) = {x : K | valuation K x ≤ 1} := by
      ext x
      exact mem_valBall_zero_iff
    rw [this]
    exact IsNonarchimedeanLocalField.isCompact_closedBall K 1
  have := h0.smul c
  rwa [smul_valBall hc, zero_add, hcn] at this

theorem exists_mem_valBall_neg_nat (x : K) : ∃ m : ℕ, x ∈ valBall K (-(m : ℤ)) := by
  refine ⟨(-ord x).toNat, valBall_antitone ?_ mem_valBall_ord⟩
  omega

instance sigmaCompactSpace_localField : SigmaCompactSpace K :=
  ⟨⟨fun m : ℕ => (valBall K (-(m : ℤ)) : Set K), fun _ => isCompact_valBall _, by
    ext x
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true, SetLike.mem_coe]
    exact exists_mem_valBall_neg_nat x⟩⟩

instance secondCountableTopology_localField : SecondCountableTopology K := by
  let := nontriviallyNormedField K
  exact EMetric.secondCountable_of_sigmaCompact K

end Topology

section Residue

variable (K) in

def residueCard : ℕ := Nat.card 𝓀[K]

theorem one_lt_residueCard : 1 < residueCard K := Finite.one_lt_card

theorem residueCard_ne_zero : residueCard K ≠ 0 := by
  have := one_lt_residueCard (K := K)
  omega

theorem one_lt_residueCard_nnreal : 1 < (residueCard K : ℝ≥0) := by
  exact_mod_cast one_lt_residueCard

theorem residueCard_nnreal_ne_zero : (residueCard K : ℝ≥0) ≠ 0 := by
  exact_mod_cast residueCard_ne_zero

end Residue

section Modulus

def modulus (x : K) : ℝ≥0 := by
  classical exact if x = 0 then 0 else (residueCard K : ℝ≥0) ^ (-ord x)

theorem modulus_of_ne_zero {x : K} (hx : x ≠ 0) :
    modulus x = (residueCard K : ℝ≥0) ^ (-ord x) := by
  simp [modulus, hx]

@[simp]
theorem modulus_zero : modulus (0 : K) = 0 := by
  simp [modulus]

theorem modulus_pos {x : K} (hx : x ≠ 0) : 0 < modulus x := by
  rw [modulus_of_ne_zero hx]
  exact zpow_pos (zero_lt_one.trans one_lt_residueCard_nnreal) _

theorem modulus_ne_zero {x : K} (hx : x ≠ 0) : modulus x ≠ 0 := (modulus_pos hx).ne'

@[simp]
theorem modulus_eq_zero {x : K} : modulus x = 0 ↔ x = 0 :=
  ⟨fun h => by_contra fun hx => modulus_ne_zero hx h, fun h => h ▸ modulus_zero⟩

theorem modulus_mul (x y : K) : modulus (x * y) = modulus x * modulus y := by
  by_cases hx : x = 0
  · simp [hx]
  by_cases hy : y = 0
  · simp [hy]
  rw [modulus_of_ne_zero hx, modulus_of_ne_zero hy, modulus_of_ne_zero (mul_ne_zero hx hy),
    ord_mul hx hy, neg_add, zpow_add₀ residueCard_nnreal_ne_zero]

@[simp]
theorem modulus_one : modulus (1 : K) = 1 := by
  rw [modulus_of_ne_zero one_ne_zero, ord_one, neg_zero, zpow_zero]

theorem modulus_inv (x : K) : modulus x⁻¹ = (modulus x)⁻¹ := by
  by_cases hx : x = 0
  · simp [hx]
  rw [modulus_of_ne_zero hx, modulus_of_ne_zero (inv_ne_zero hx), ord_inv hx, zpow_neg]

theorem modulus_le_one_iff {x : K} : modulus x ≤ 1 ↔ x ∈ 𝒪[K] := by
  by_cases hx : x = 0
  · simp only [hx, modulus_zero, zero_le, true_iff]
    exact zero_mem _
  rw [modulus_of_ne_zero hx, ← mem_valBall_zero_iff, mem_valBall_iff_le_ord hx,
    zpow_le_one_iff_right₀ one_lt_residueCard_nnreal]
  omega

theorem modulus_eq_one_iff {x : K} : modulus x = 1 ↔ x ≠ 0 ∧ ord x = 0 := by
  by_cases hx : x = 0
  · simp [hx]
  rw [modulus_of_ne_zero hx, ← zpow_zero (residueCard K : ℝ≥0),
    (zpow_right_strictMono₀ one_lt_residueCard_nnreal).injective.eq_iff]
  simp [hx]

theorem ord_add_eq {x d : K} (hx : x ≠ 0) (hd : d ∈ valBall K (ord x + 1)) :
    x + d ≠ 0 ∧ ord (x + d) = ord x := by
  have hlt : normalizedValuation K d < normalizedValuation K x := by
    rw [normalizedValuation_eq_exp_ord hx]
    exact lt_of_le_of_lt (mem_valBall.mp hd) (WithZero.exp_lt_exp.mpr (by omega))
  have heq : normalizedValuation K (x + d) = normalizedValuation K x :=
    Valuation.map_add_eq_of_lt_left _ hlt
  have hne : x + d ≠ 0 := by
    intro h
    rw [h, map_zero, normalizedValuation_eq_exp_ord hx] at heq
    exact WithZero.exp_ne_zero heq.symm
  exact ⟨hne, by simp only [ord, heq]⟩

theorem modulus_add_eq {x d : K} (hx : x ≠ 0) (hd : d ∈ valBall K (ord x + 1)) :
    modulus (x + d) = modulus x := by
  obtain ⟨h1, h2⟩ := ord_add_eq hx hd
  rw [modulus_of_ne_zero h1, modulus_of_ne_zero hx, h2]

theorem modulus_le_of_mem_valBall {n : ℤ} {x : K} (hx : x ∈ valBall K n) :
    modulus x ≤ (residueCard K : ℝ≥0) ^ (-n) := by
  by_cases h0 : x = 0
  · simp [h0]
  rw [modulus_of_ne_zero h0]
  have := (mem_valBall_iff_le_ord h0).mp hx
  exact zpow_le_zpow_right₀ one_lt_residueCard_nnreal.le (by omega)

theorem continuous_modulus : Continuous (modulus : K → ℝ≥0) := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x = 0
  · subst hx
    rw [ContinuousAt, modulus_zero, tendsto_order]
    refine ⟨fun a ha => (not_lt_zero ha).elim, fun ε hε => ?_⟩
    obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hε
      (inv_lt_one_of_one_lt₀ (one_lt_residueCard_nnreal (K := K)))
    filter_upwards [valBall_mem_nhds (K := K) k] with y hy
    calc modulus y ≤ (residueCard K : ℝ≥0) ^ (-(k : ℤ)) := modulus_le_of_mem_valBall hy
      _ = ((residueCard K : ℝ≥0))⁻¹ ^ k := by rw [zpow_neg, zpow_natCast, inv_pow]
      _ < ε := hk
  · have hmem : {y : K | y - x ∈ valBall K (ord x + 1)} ∈ 𝓝 x :=
      ((isOpen_valBall _).preimage (continuous_id.sub continuous_const)).mem_nhds (by simp)
    have hev : ∀ᶠ y in 𝓝 x, modulus x = modulus y := by
      filter_upwards [hmem] with y hy
      have := modulus_add_eq hx hy
      rw [add_sub_cancel] at this
      exact this.symm
    exact tendsto_const_nhds.congr' hev

end Modulus

section Haar

variable [MeasurableSpace K] [BorelSpace K]

theorem measurableSet_valBall (n : ℤ) : MeasurableSet (valBall K n : Set K) :=
  (isOpen_valBall n).measurableSet

theorem measurable_modulus : Measurable (modulus : K → ℝ≥0) :=
  continuous_modulus.measurable

theorem measure_valBall_zero_eq_mul (μ : Measure K) [μ.IsAddLeftInvariant] :
    μ (valBall K 0) = residueCard K * μ (valBall K 1) := by
  classical
  have : Fintype 𝓀[K] := Fintype.ofFinite _
  choose s hs using
    (IsLocalRing.residue_surjective : Function.Surjective (IsLocalRing.residue 𝒪[K]))
  let T : 𝓀[K] → Set K := fun r => (fun x => -((s r : 𝒪[K]) : K) + x) ⁻¹' (valBall K 1 : Set K)
  have hmem : ∀ r x, x ∈ T r ↔ ∃ h : x ∈ 𝒪[K], IsLocalRing.residue 𝒪[K] ⟨x, h⟩ = r := by
    intro r x
    constructor
    · intro hx
      have hx' : x - (s r : K) ∈ valBall K 1 := by
        have : -((s r : 𝒪[K]) : K) + x ∈ valBall K 1 := hx
        rwa [neg_add_eq_sub] at this
      have h1 := add_mem (valBall_antitone (show (0 : ℤ) ≤ 1 by norm_num) hx')
        (mem_valBall_zero_iff.mpr (s r).2)
      rw [sub_add_cancel] at h1
      refine ⟨mem_valBall_zero_iff.mp h1, ?_⟩
      rw [← hs r, residue_eq_residue_iff]
      exact hx'
    · rintro ⟨h, hr⟩
      rw [← hs r, residue_eq_residue_iff] at hr
      show -((s r : 𝒪[K]) : K) + x ∈ valBall K 1
      rw [neg_add_eq_sub]
      exact hr
  have hunion : (valBall K 0 : Set K) = ⋃ r, T r := by
    ext x
    simp only [Set.mem_iUnion, hmem, SetLike.mem_coe, mem_valBall_zero_iff]
    constructor
    · intro hx
      exact ⟨_, hx, rfl⟩
    · rintro ⟨r, h, -⟩
      exact h
  have hdisj : Pairwise (Function.onFun Disjoint T) := by
    intro r r' hne
    refine Set.disjoint_left.mpr fun x hx hx' => hne ?_
    obtain ⟨h, rfl⟩ := (hmem r x).mp hx
    obtain ⟨h', rfl⟩ := (hmem r' x).mp hx'
    rfl
  have hmeas : ∀ r, MeasurableSet (T r) := fun r =>
    (measurableSet_valBall 1).preimage (measurable_const_add _)
  have hμ : ∀ r, μ (T r) = μ (valBall K 1) := fun r => measure_preimage_add μ _ _
  rw [hunion, measure_iUnion hdisj hmeas, tsum_fintype]
  simp only [hμ, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, residueCard,
    Nat.card_eq_fintype_card]

variable (μ : Measure K) [μ.IsAddHaarMeasure]

theorem measure_smul_eq_distribHaarChar {c : K} (hc : c ≠ 0) (s : Set K) :
    μ (c • s) = distribHaarChar K (Units.mk0 c hc) * μ s :=
  (distribHaarChar_mul μ (Units.mk0 c hc) s).symm

theorem measure_valBall_eq_mul_succ (n : ℤ) :
    μ (valBall K n) = residueCard K * μ (valBall K (n + 1)) := by
  obtain ⟨c, hc, hcn⟩ := exists_ord_eq K n
  have h0 := measure_smul_eq_distribHaarChar μ hc (valBall K 0)
  have h1 := measure_smul_eq_distribHaarChar μ hc (valBall K 1)
  rw [smul_valBall hc, zero_add, hcn] at h0
  rw [smul_valBall hc, hcn, add_comm] at h1
  rw [h0, h1, measure_valBall_zero_eq_mul μ]
  ring

theorem measure_valBall (n : ℤ) :
    μ (valBall K n) = ((residueCard K : ℝ≥0) ^ (-n) : ℝ≥0) * μ (valBall K 0) := by
  have hq0 := residueCard_nnreal_ne_zero (K := K)
  have hq : ((residueCard K : ℝ≥0) : ℝ≥0∞) ≠ 0 := by exact_mod_cast hq0
  have hqt : ((residueCard K : ℝ≥0) : ℝ≥0∞) ≠ ∞ := ENNReal.coe_ne_top
  have hcast : ((residueCard K : ℕ) : ℝ≥0∞) = ((residueCard K : ℝ≥0) : ℝ≥0∞) := rfl
  induction n using Int.induction_on with
  | zero => simp
  | succ k ih =>
    have h := measure_valBall_eq_mul_succ μ (k : ℤ)
    rw [ih, hcast] at h
    have : μ (valBall K (k + 1)) = ((residueCard K : ℝ≥0) : ℝ≥0∞)⁻¹ *
        (((residueCard K : ℝ≥0) ^ (-(k : ℤ)) : ℝ≥0) * μ (valBall K 0)) := by
      rw [h, ← mul_assoc, ENNReal.inv_mul_cancel hq hqt, one_mul]
    have e : ((residueCard K : ℝ≥0))⁻¹ * (residueCard K : ℝ≥0) ^ (-(k : ℤ)) =
        (residueCard K : ℝ≥0) ^ (-((k : ℤ) + 1)) := by
      rw [show -((k : ℤ) + 1) = -1 + -(k : ℤ) by ring, zpow_add₀ hq0, zpow_neg_one]
    rw [this, ← mul_assoc, ← ENNReal.coe_inv hq0, ← ENNReal.coe_mul, e]
  | pred k ih =>
    have h := measure_valBall_eq_mul_succ μ (-(k : ℤ) - 1)
    rw [sub_add_cancel, ih, hcast] at h
    have e : (residueCard K : ℝ≥0) * (residueCard K : ℝ≥0) ^ (-(-(k : ℤ))) =
        (residueCard K : ℝ≥0) ^ (-(-(k : ℤ) - 1)) := by
      rw [show -(-(k : ℤ) - 1) = 1 + -(-(k : ℤ)) by ring, zpow_add₀ hq0, zpow_one]
    rw [h, ← mul_assoc, ← ENNReal.coe_mul, e]

variable (K) in

def integersPositiveCompacts : PositiveCompacts K where
  carrier := valBall K 0
  isCompact' := isCompact_valBall 0
  interior_nonempty' := by
    rw [(isOpen_valBall 0).interior_eq]
    exact ⟨0, zero_mem _⟩

variable (K) in

def haarIntegers : Measure K := addHaarMeasure (integersPositiveCompacts K)

instance : (haarIntegers K).IsAddHaarMeasure := by
  unfold haarIntegers
  infer_instance

theorem measureReal_valBall (n : ℤ) :
    μ.real (valBall K n) = (residueCard K : ℝ) ^ (-n) * μ.real (valBall K 0) := by
  rw [measureReal_def, measureReal_def, measure_valBall μ n, ENNReal.toReal_mul,
    ENNReal.coe_toReal, NNReal.coe_zpow, NNReal.coe_natCast]

theorem distribHaarChar_eq_modulus (u : Kˣ) : distribHaarChar K u = modulus (u : K) := by
  have h0 : haarIntegers K (valBall K 0) ≠ 0 :=
    ((isOpen_valBall 0).measure_pos (haarIntegers K) ⟨0, zero_mem _⟩).ne'
  have ht : haarIntegers K (valBall K 0) ≠ ∞ := (isCompact_valBall 0).measure_lt_top.ne
  refine distribHaarChar_eq_of_measure_smul_eq_mul (μ := haarIntegers K) h0 ht ?_
  have hu : ((u : K)) ≠ 0 := u.ne_zero
  have : u • (valBall K 0 : Set K) = (u : K) • (valBall K 0 : Set K) := rfl
  rw [this, smul_valBall hu, zero_add, measure_valBall (haarIntegers K), modulus_of_ne_zero hu]

theorem addHaar_smul {a : K} (ha : a ≠ 0) (s : Set K) : μ (a • s) = modulus a * μ s := by
  rw [measure_smul_eq_distribHaarChar μ ha, distribHaarChar_eq_modulus, Units.val_mk0]

theorem map_mul_left_eq_smul {a : K} (ha : a ≠ 0) :
    Measure.map (fun x => a * x) μ = (modulus a)⁻¹ • μ := by
  ext s hs
  rw [Measure.map_apply (measurable_const_mul a) hs]
  have : (fun x => a * x) ⁻¹' s = a⁻¹ • s := by
    ext x
    simp [Set.mem_smul_set_iff_inv_smul_mem₀ (inv_ne_zero ha), smul_eq_mul]
  rw [this, addHaar_smul μ (inv_ne_zero ha), modulus_inv, Measure.smul_apply, ENNReal.smul_def,
    smul_eq_mul]

theorem integral_comp_mul_left {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a : K} (ha : a ≠ 0) (f : K → E) :
    ∫ x, f (a * x) ∂μ = ((modulus a : ℝ))⁻¹ • ∫ x, f x ∂μ := by
  have he : MeasurableEmbedding (fun x : K => a * x) :=
    (Homeomorph.mulLeft₀ a ha).measurableEmbedding
  rw [← he.integral_map, map_mul_left_eq_smul μ ha, integral_smul_nnreal_measure]
  simp [NNReal.smul_def]

theorem lintegral_comp_mul_left {a : K} (ha : a ≠ 0) (f : K → ℝ≥0∞) :
    ∫⁻ x, f (a * x) ∂μ = ((modulus a : ℝ≥0∞))⁻¹ * ∫⁻ x, f x ∂μ := by
  have he : MeasurableEmbedding (fun x : K => a * x) :=
    (Homeomorph.mulLeft₀ a ha).measurableEmbedding
  rw [← he.lintegral_map, map_mul_left_eq_smul μ ha, lintegral_smul_measure,
    ENNReal.smul_def, smul_eq_mul, ENNReal.coe_inv (modulus_ne_zero ha)]

theorem haarIntegers_integers : haarIntegers K (𝒪[K] : Set K) = 1 := by
  rw [← coe_valBall_zero]
  exact addHaarMeasure_self

theorem haarIntegers_valBall (n : ℤ) :
    haarIntegers K (valBall K n) = ((residueCard K : ℝ≥0) ^ (-n) : ℝ≥0) := by
  rw [measure_valBall (haarIntegers K), coe_valBall_zero, haarIntegers_integers, mul_one]

theorem eq_smul_haarIntegers (ν : Measure K) [ν.IsAddHaarMeasure] :
    ν = ν (𝒪[K] : Set K) • haarIntegers K := by
  have := addHaarMeasure_unique ν (integersPositiveCompacts K)
  rw [← coe_valBall_zero]
  exact this

end Haar

end GroundTheory.LocalField
