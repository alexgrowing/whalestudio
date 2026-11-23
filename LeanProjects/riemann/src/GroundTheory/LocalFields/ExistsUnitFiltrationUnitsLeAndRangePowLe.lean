import Mathlib
import GroundTheory.LocalFields.UnitsBasic
import GroundTheory.LocalFields.UnitsPowers

namespace GroundTheory.LocalField

open ValuativeRel IsLocalRing Topology Filter
open scoped WithZero

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

noncomputable def unitFiltrationUnits (n : ℕ) : Subgroup Kˣ :=
  (unitFiltration K n).map (unitsIncl K)

variable {K}

theorem unitFiltrationUnits_antitone : Antitone (unitFiltrationUnits K) :=
  fun _ _ hmn ↦ Subgroup.map_mono (unitFiltration_antitone K hmn)

theorem mem_unitFiltrationUnits_zero_iff {x : Kˣ} :
    x ∈ unitFiltrationUnits K 0 ↔ valuation K (x : K) = 1 := by
  rw [unitFiltrationUnits, unitFiltration_zero, ← MonoidHom.range_eq_map, mem_range_unitsIncl_iff,
    ← map_one (normalizedValuation K), normalizedValuation_eq_iff, map_one]

theorem mem_unitFiltrationUnits_iff {n : ℕ} (hn : 1 ≤ n) {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ)
    {x : Kˣ} :
    x ∈ unitFiltrationUnits K n ↔ valuation K ((x : K) - 1) ≤ valuation K (ϖ : K) ^ n := by
  have hset := hϖ.maximalIdeal_pow_eq_setOfPred_le_v_coe_pow (v := valuation K) n
  constructor
  · rintro ⟨u, hu, rfl⟩
    have : ((u : 𝒪[K]) - 1 : 𝒪[K]) ∈ ((𝓂[K] ^ n : Ideal 𝒪[K]) : Set 𝒪[K]) := hu
    rw [hset] at this
    simpa using this
  · intro h
    have hϖ1 : valuation K (ϖ : K) < 1 :=
      valuation_lt_one_of_mem_maximalIdeal (uniformizer_mem_maximalIdeal hϖ)
    have hlt : valuation K ((x : K) - 1) < 1 :=
      h.trans_lt (pow_lt_one₀ zero_le hϖ1 (by omega))
    have hx1 : valuation K (x : K) = 1 := by
      have := (valuation K).map_one_add_of_lt hlt
      simpa using this
    obtain ⟨u, rfl⟩ := mem_range_unitsIncl_iff.mpr (by
      rw [← map_one (normalizedValuation K), normalizedValuation_eq_iff, map_one]; exact hx1)
    refine ⟨u, ?_, rfl⟩
    show ((u : 𝒪[K]) - 1 : 𝒪[K]) ∈ ((𝓂[K] ^ n : Ideal 𝒪[K]) : Set 𝒪[K])
    rw [hset]
    simpa using h

theorem isOpen_setOf_valuation_sub_le {a : K} {γ : ValueGroupWithZero K} (hγ : γ ≠ 0) :
    IsOpen {y : K | valuation K (y - a) ≤ γ} := by
  rw [isOpen_iff_mem_nhds]
  intro y hy
  rw [IsValuativeTopology.mem_nhds_iff']
  refine ⟨Units.mk0 γ hγ, fun z hz ↦ ?_⟩
  have : z - a = (z - y) + (y - a) := by ring
  simp only [Set.mem_ofPred_eq, Units.val_mk0] at hz hy ⊢
  rw [this]
  exact (valuation K).map_add_le hz.le hy

theorem isOpen_setOf_valuation_lt {γ : ValueGroupWithZero K} :
    IsOpen {y : K | valuation K y < γ} := by
  rw [isOpen_iff_mem_nhds]
  intro y hy
  rw [IsValuativeTopology.mem_nhds_iff']
  have hγ : γ ≠ 0 := ne_bot_of_gt hy
  refine ⟨Units.mk0 γ hγ, fun z hz ↦ ?_⟩
  have : z = (z - y) + y := by ring
  simp only [Set.mem_ofPred_eq, Units.val_mk0] at hz hy ⊢
  rw [this]
  exact (valuation K).map_add_lt hz hy

theorem isOpen_setOf_valuation_eq_one : IsOpen {y : K | valuation K y = 1} := by
  rw [isOpen_iff_mem_nhds]
  intro y hy
  rw [IsValuativeTopology.mem_nhds_iff']
  refine ⟨1, fun z hz ↦ ?_⟩
  simp only [Set.mem_ofPred_eq, Units.val_one] at hz hy ⊢
  have : z = y + (z - y) := by ring
  rw [this, (valuation K).map_add_eq_of_lt_left (by rw [hy]; exact hz), hy]

theorem val_image_unitFiltrationUnits_zero :
    ((↑) : Kˣ → K) '' (unitFiltrationUnits K 0 : Set Kˣ) = {y : K | valuation K y = 1} := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact mem_unitFiltrationUnits_zero_iff.mp hx
  · intro hy
    have hy0 : y ≠ 0 := by rintro rfl; simp at hy
    exact ⟨Units.mk0 y hy0, mem_unitFiltrationUnits_zero_iff.mpr hy, rfl⟩

theorem val_image_unitFiltrationUnits {n : ℕ} (hn : 1 ≤ n) {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ) :
    ((↑) : Kˣ → K) '' (unitFiltrationUnits K n : Set Kˣ) =
      {y : K | valuation K (y - 1) ≤ valuation K (ϖ : K) ^ n} := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (mem_unitFiltrationUnits_iff hn hϖ).mp hx
  · intro hy
    have hϖ1 : valuation K (ϖ : K) < 1 :=
      valuation_lt_one_of_mem_maximalIdeal (uniformizer_mem_maximalIdeal hϖ)
    have hy0 : y ≠ 0 := by
      rintro rfl
      have : valuation K ((0 : K) - 1) ≤ valuation K (ϖ : K) ^ n := hy
      simp only [zero_sub, Valuation.map_neg, map_one] at this
      exact (pow_lt_one₀ zero_le hϖ1 (by omega)).not_ge this
    exact ⟨Units.mk0 y hy0, (mem_unitFiltrationUnits_iff hn hϖ).mpr hy, rfl⟩

theorem valuation_uniformizer_ne_zero {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ) :
    valuation K (ϖ : K) ≠ 0 := by
  rw [Ne, Valuation.zero_iff]
  exact_mod_cast hϖ.ne_zero

theorem isOpen_unitFiltrationUnits (n : ℕ) : IsOpen (unitFiltrationUnits K n : Set Kˣ) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have : (unitFiltrationUnits K 0 : Set Kˣ) = (↑) ⁻¹' {y : K | valuation K y = 1} := by
      ext x; exact mem_unitFiltrationUnits_zero_iff
    rw [this]
    exact isOpen_setOf_valuation_eq_one.preimage Units.continuous_val
  · have : (unitFiltrationUnits K n : Set Kˣ) =
        (↑) ⁻¹' {y : K | valuation K (y - 1) ≤ valuation K (ϖ : K) ^ n} := by
      ext x; exact mem_unitFiltrationUnits_iff hn hϖ
    rw [this]
    exact (isOpen_setOf_valuation_sub_le
      (pow_ne_zero _ (valuation_uniformizer_ne_zero hϖ))).preimage Units.continuous_val

theorem isCompact_unitFiltrationUnits (n : ℕ) : IsCompact (unitFiltrationUnits K n : Set Kˣ) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  rw [Units.isEmbedding_val₀.isCompact_iff]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [val_image_unitFiltrationUnits_zero]
    have : {y : K | valuation K y = 1} =
        {y : K | valuation K y ≤ 1} \ {y : K | valuation K y < 1} := by
      ext y
      simp only [Set.mem_ofPred_eq, Set.mem_sdiff, not_lt]
      constructor
      · intro h; exact ⟨h.le, h.ge⟩
      · intro h; exact le_antisymm h.1 h.2
    rw [this]
    exact (IsNonarchimedeanLocalField.isCompact_closedBall K 1).diff isOpen_setOf_valuation_lt
  · rw [val_image_unitFiltrationUnits hn hϖ]
    have : {y : K | valuation K (y - 1) ≤ valuation K (ϖ : K) ^ n} =
        (Homeomorph.subRight (1 : K)) ⁻¹' {y : K | valuation K y ≤ valuation K (ϖ : K) ^ n} := by
      ext y; rfl
    rw [this, Homeomorph.isCompact_preimage]
    exact IsNonarchimedeanLocalField.isCompact_closedBall K _

theorem exists_pow_lt {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ) {γ : ValueGroupWithZero K} (hγ : γ ≠ 0) :
    ∃ n, 1 ≤ n ∧ valuation K (ϖ : K) ^ n < γ := by
  obtain ⟨z, rfl⟩ := ValuativeRel.valuation_surjective γ
  have hz : z ≠ 0 := by rintro rfl; simp at hγ
  refine ⟨max 1 (ord z + 1).toNat, le_max_left _ _, ?_⟩
  rw [← map_pow, ← normalizedValuation_lt_iff, map_pow, normalizedValuation_uniformizer hϖ,
    normalizedValuation_eq_exp_ord hz, ← WithZero.exp_nsmul, WithZero.exp_lt_exp]
  simp only [nsmul_eq_mul, mul_neg, mul_one, neg_lt_neg_iff]
  have := le_max_right 1 (ord z + 1).toNat
  omega

theorem hasBasis_nhds_one_unitFiltrationUnits :
    (𝓝 (1 : Kˣ)).HasBasis (fun _ ↦ True) (fun n ↦ (unitFiltrationUnits K n : Set Kˣ)) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  rw [Filter.hasBasis_iff]
  intro t
  constructor
  · intro ht
    rw [Units.isEmbedding_val₀.isInducing.nhds_eq_comap, Filter.mem_comap] at ht
    obtain ⟨t', ht', hsub⟩ := ht
    rw [Units.val_one, IsValuativeTopology.mem_nhds_iff'] at ht'
    obtain ⟨γ, hγ⟩ := ht'
    obtain ⟨n, hn, hlt⟩ := exists_pow_lt hϖ γ.ne_zero
    refine ⟨n, trivial, fun x hx ↦ hsub (hγ ?_)⟩
    exact ((mem_unitFiltrationUnits_iff hn hϖ).mp hx).trans_lt hlt
  · rintro ⟨n, -, hn⟩
    exact Filter.mem_of_superset
      ((isOpen_unitFiltrationUnits n).mem_nhds (Subgroup.one_mem _)) hn

theorem exists_unitFiltrationUnits_le {H : Subgroup Kˣ} (hH : IsOpen (H : Set Kˣ)) :
    ∃ n, unitFiltrationUnits K n ≤ H := by
  obtain ⟨n, -, hn⟩ :=
    hasBasis_nhds_one_unitFiltrationUnits.mem_iff.mp (hH.mem_nhds (Subgroup.one_mem H))
  exact ⟨n, hn⟩

theorem exists_range_pow_le {H : Subgroup Kˣ} [H.FiniteIndex] :
    ∃ m, m ≠ 0 ∧ (powMonoidHom m : Kˣ →* Kˣ).range ≤ H := by
  refine ⟨H.index, Subgroup.FiniteIndex.index_ne_zero, ?_⟩
  rintro _ ⟨x, rfl⟩
  exact H.pow_index_mem x

theorem exists_unitFiltrationUnits_le_and_range_pow_le {H : Subgroup Kˣ} [H.FiniteIndex]
    (hH : IsOpen (H : Set Kˣ)) :
    (∃ n, unitFiltrationUnits K n ≤ H) ∧ ∃ m, m ≠ 0 ∧ (powMonoidHom m : Kˣ →* Kˣ).range ≤ H :=
  ⟨exists_unitFiltrationUnits_le hH, exists_range_pow_le⟩

theorem isOpen_range_pow {m : ℕ} (hm : (m : K) ≠ 0) :
    IsOpen ((powMonoidHom m : Kˣ →* Kˣ).range : Set Kˣ) := by
  obtain ⟨N, hN⟩ := exists_unitFiltration_le_range_pow hm
  refine Subgroup.isOpen_mono ?_ (isOpen_unitFiltrationUnits N)
  rintro _ ⟨u, hu, rfl⟩
  obtain ⟨x, rfl⟩ := hN hu
  exact ⟨unitsIncl K x, by simp⟩

end GroundTheory.LocalField
