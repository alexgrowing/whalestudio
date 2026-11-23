import Mathlib
import GroundTheory.PAdicHodge.ExtRobbaUnion
set_option maxSynthPendingDepth 1

noncomputable section

set_option linter.unusedSectionVars false

namespace GroundTheory.PAdicHodge

namespace TeichLift

open Laurent Filter Topology UniformSpace

variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]
  [CharP L p] [PerfectRing L p] {Γ : Type*} [CommRing Γ] (T : TeichLift p L Γ)

theorem prefixLe_π_pow_mul {D : Γ} {n : ℕ} {b : ℝ} (hD : T.PrefixLe D n b) (i : ℕ) :
    T.PrefixLe (T.π ^ i * D) n b := by
  intro m hm
  rcases lt_or_ge m i with h | h
  · rw [T.coeff_π_pow_mul_of_lt _ h, norm_zero]; exact hD.nonneg
  · obtain ⟨m', rfl⟩ := Nat.exists_eq_add_of_le' h
    rw [coeff_π_pow_mul_add]
    exact hD m' (by omega)

theorem prefixLe_teich_sub {a c : L} {B η : ℝ} (ha : ‖a‖ ≤ B) (hc : ‖c‖ ≤ B) (hac : ‖a - c‖ ≤ η)
    (hη : 0 ≤ η) (hηB : η ≤ B) (k : ℕ) :
    T.PrefixLe (T.teich a - T.teich c) k
      (B ^ (1 - ((p ^ k : ℕ) : ℝ)⁻¹) * η ^ ((p ^ k : ℕ) : ℝ)⁻¹) := by
  obtain ⟨ht0, ht1⟩ := inv_pow_pos_le_one (p := p) k
  have hD := T.prefixLe_teich_add_sub_of_le (a := c) (e := a - c) hc hac hη hηB k
  rw [add_sub_cancel] at hD
  have hE : T.PrefixLe (T.teich (a - c)) k
      (B ^ (1 - ((p ^ k : ℕ) : ℝ)⁻¹) * η ^ ((p ^ k : ℕ) : ℝ)⁻¹) := by
    intro m hm
    rw [coeff_teich]
    split_ifs
    · exact hac.trans (le_rpow_mix hη hηB ht1)
    · rw [norm_zero]
      exact mul_nonneg (Real.rpow_nonneg (hη.trans hηB) _) (Real.rpow_nonneg hη _)
  have := T.prefixLe_add hD hE
  rwa [show T.teich a - T.teich c - T.teich (a - c) + T.teich (a - c) = T.teich a - T.teich c by
    ring] at this

theorem prefixLe_sub_of_coeff_close {u v : Γ} {n : ℕ} {B η : ℝ} (hη : 0 ≤ η) (hηB : η ≤ B)
    (hu : ∀ i ≤ n, ‖T.coeff u i‖ ≤ B) (hv : ∀ i ≤ n, ‖T.coeff v i‖ ≤ B)
    (huv : ∀ i ≤ n, ‖T.coeff u i - T.coeff v i‖ ≤ η) :
    T.PrefixLe (u - v) n (B ^ (1 - ((p ^ n : ℕ) : ℝ)⁻¹) * η ^ ((p ^ n : ℕ) : ℝ)⁻¹) := by
  have hb0 : 0 ≤ B ^ (1 - ((p ^ n : ℕ) : ℝ)⁻¹) * η ^ ((p ^ n : ℕ) : ℝ)⁻¹ :=
    mul_nonneg (Real.rpow_nonneg (hη.trans hηB) _) (Real.rpow_nonneg hη _)
  have hS : T.PrefixLe (∑ i ∈ Finset.range (n + 1), T.π ^ i * (T.teich (T.coeff u i) -
      T.teich (T.coeff v i))) n (B ^ (1 - ((p ^ n : ℕ) : ℝ)⁻¹) * η ^ ((p ^ n : ℕ) : ℝ)⁻¹) := by
    refine T.prefixLe_sum _ _ hb0 fun i hi => ?_
    have hi' : i ≤ n := by simpa [Nat.lt_succ_iff] using hi
    exact T.prefixLe_π_pow_mul (T.prefixLe_teich_sub (hu i hi') (hv i hi') (huv i hi') hη hηB n) i
  have hR : u - v - ∑ i ∈ Finset.range (n + 1), T.π ^ i * (T.teich (T.coeff u i) -
      T.teich (T.coeff v i)) ∈ Ideal.span {T.π ^ (n + 1)} := by
    have e : ∑ i ∈ Finset.range (n + 1), T.π ^ i * (T.teich (T.coeff u i) - T.teich (T.coeff v i)) =
        T.partialSum u (n + 1) - T.partialSum v (n + 1) := by
      simp only [partialSum, finSum, ← Finset.sum_sub_distrib, mul_sub]
    rw [e, show u - v - (T.partialSum u (n + 1) - T.partialSum v (n + 1)) =
      (u - T.partialSum u (n + 1)) - (v - T.partialSum v (n + 1)) by ring]
    exact sub_mem (T.sub_partialSum_mem u _) (T.sub_partialSum_mem v _)
  have := T.prefixLe_add hS (T.prefixLe_of_mem_span hR hb0)
  rwa [add_sub_cancel] at this

variable {ρ1 : Set.Ioo (0 : ℝ) 1}

theorem exists_approx (z : T.RobbaExt ρ1) (σ : Set.Ioc (0 : ℝ) ρ1) {ε : ℝ} (hε : 0 < ε) :
    ∃ b : T.Econ ρ1, ∀ ρ : Set.Ioc (0 : ℝ) ρ1, (σ : ℝ) ≤ ρ →
      T.extNorm ρ1 ρ (z - b) < ε := by
  have hU : {y : T.RobbaExt ρ1 | T.extNorm ρ1 σ (z - y) < ε ∧
      T.extNorm ρ1 (topRad ρ1) (z - y) < ε} ∈ 𝓝 z := by
    refine IsOpen.mem_nhds ?_ ?_
    · exact (isOpen_lt ((T.continuous_extNorm σ).comp (continuous_const.sub continuous_id))
        continuous_const).inter (isOpen_lt ((T.continuous_extNorm _).comp
          (continuous_const.sub continuous_id)) continuous_const)
    · simp only [Set.mem_setOf_eq, sub_self, extNorm_zero]; exact ⟨hε, hε⟩
  obtain ⟨b, hb1, hb2⟩ := Completion.denseRange_coe.mem_nhds hU
  exact ⟨b, fun ρ hρ => (T.extNorm_le_max σ (topRad ρ1) ρ hρ ρ.2.2 _).trans_lt (max_lt hb1 hb2)⟩

theorem exists_nonneg_part (b : T.B) : ∃ X : Γ,
    (∀ k : ℤ, 0 ≤ k → T.zcoeff X k = T.coeffB b k) ∧
    (∀ k : ℤ, k < 0 → T.coeffB (b - algebraMap Γ T.B X) k = T.coeffB b k) ∧
    (∀ k : ℤ, 0 ≤ k → T.coeffB (b - algebraMap Γ T.B X) k = 0) := by
  obtain ⟨N, x, hx⟩ := IsLocalization.Away.surj T.π b
  have hsub : (b - algebraMap Γ T.B (T.tail^[N] x)) * algebraMap Γ T.B T.π ^ N =
      algebraMap Γ T.B (T.partialSum x N) := by
    have h2 := T.sub_partialSum x N
    rw [sub_mul, hx, ← map_pow, ← map_mul, ← map_sub, mul_comm (T.tail^[N] x), ← h2,
      sub_sub_cancel]
  refine ⟨T.tail^[N] x, ?_, ?_, ?_⟩
  · intro k hk
    lift k to ℕ using hk
    rw [T.coeffB_eq hx, zcoeff_natCast]
    show T.coeff (T.tail^[N] x) k = T.zcoeff x ((k : ℤ) + N)
    rw [show ((k : ℤ) + N) = ((k + N : ℕ) : ℤ) by push_cast; ring, zcoeff_natCast, coeff_tail_iterate]
  · intro k hk
    rw [T.coeffB_eq hsub, T.coeffB_eq hx]
    rcases lt_or_ge (k + N) 0 with h | h
    · simp only
      rw [T.zcoeff_of_neg _ h, T.zcoeff_of_neg _ h]
    · obtain ⟨m, hm⟩ : ∃ m : ℕ, k + N = m := ⟨_, (Int.toNat_of_nonneg h).symm⟩
      simp only [hm, zcoeff_natCast, partialSum, coeff_finSum]
      rw [if_pos (by omega)]
  · intro k hk
    rw [T.coeffB_eq hsub]
    obtain ⟨m, hm⟩ : ∃ m : ℕ, k + N = m := ⟨_, (Int.toNat_of_nonneg (by omega)).symm⟩
    simp only [hm, zcoeff_natCast, partialSum, coeff_finSum]
    rw [if_neg (by omega)]

theorem gaussNorm_neg_part_le {c : T.B} {σ ρ C' : ℝ} (hσ : 0 < σ) (hσρ : σ ≤ ρ) (hC : 0 ≤ C')
    (hc0 : ∀ k : ℤ, 0 ≤ k → T.coeffB c k = 0) (hcw : ∀ k : ℤ, ‖T.coeffB c k‖ * σ ^ k ≤ C') :
    gaussNorm (T.coeffB c) ρ ≤ C' * (σ / ρ) := by
  have hρ : 0 < ρ := hσ.trans_le hσρ
  refine gaussNorm_le fun k => ?_
  rcases le_or_gt 0 k with hk | hk
  · rw [hc0 k hk, norm_zero, zero_mul]; positivity
  · have hq : 1 ≤ ρ / σ := by rw [le_div_iff₀ hσ, one_mul]; exact hσρ
    calc ‖T.coeffB c k‖ * ρ ^ k = (‖T.coeffB c k‖ * σ ^ k) * (ρ / σ) ^ k := by
          rw [div_zpow, mul_assoc, mul_div_assoc', mul_div_cancel_left₀ _ (zpow_pos hσ k).ne']
      _ ≤ C' * (ρ / σ) ^ (-1 : ℤ) :=
          mul_le_mul (hcw k) (zpow_le_zpow_right₀ hq (by omega)) (zpow_pos (by positivity) k).le hC
      _ = C' * (σ / ρ) := by rw [zpow_neg_one, inv_div]

theorem exists_gamma_approx {z : T.RobbaExt ρ1} {C : ℝ} (hC : 0 ≤ C)
    (hz : ∀ ρ, T.extNorm ρ1 ρ z ≤ C) (σ : Set.Ioc (0 : ℝ) ρ1) {ε : ℝ} (hε : 0 < ε)
    (hε1 : ε ≤ 1) :
    ∃ (X : Γ) (hX : algebraMap Γ T.B X ∈ T.Econ ρ1),
      (∀ m : ℕ, ‖T.coeff X m‖ * (ρ1 : ℝ) ^ (m : ℤ) ≤ C + 1) ∧
      ∀ ρ : Set.Ioc (0 : ℝ) ρ1, (σ : ℝ) ≤ ρ →
        T.extNorm ρ1 ρ (z - ((⟨_, hX⟩ : T.Econ ρ1) : T.RobbaExt ρ1)) ≤
          max ε ((C + 1) * (σ / ρ)) := by
  obtain ⟨b, hb⟩ := T.exists_approx z σ hε
  have hbn : ∀ ρ : Set.Ioc (0 : ℝ) ρ1, (σ : ℝ) ≤ ρ → gaussNorm (T.coeffB b) ρ ≤ C + 1 := by
    intro ρ hρ
    rw [← extNorm_coe]
    have := T.extNorm_add_le ρ z ((b : T.RobbaExt ρ1) - z)
    rw [add_sub_cancel, T.extNorm_sub_comm] at this
    exact this.trans (max_le ((hz ρ).trans (by linarith)) ((hb ρ hρ).le.trans (by linarith)))
  obtain ⟨X, hX1, hX2, hX3⟩ := T.exists_nonneg_part (b : T.B)
  have hwX : ∀ k : ℤ, ‖T.zcoeff X k‖ * (ρ1 : ℝ) ^ k ≤ ‖T.coeffB b k‖ * (ρ1 : ℝ) ^ k := by
    intro k
    rcases le_or_gt 0 k with hk | hk
    · rw [hX1 k hk]
    · rw [T.zcoeff_of_neg _ hk, norm_zero, zero_mul]
      exact mul_nonneg (norm_nonneg _) (zpow_pos ρ1.2.1 k).le
  have hXc : ConvergesAt (T.zcoeff X) ρ1 := by
    have hb1 : ConvergesAt (T.coeffB b) ρ1 := b.2
    refine squeeze_zero (fun k => mul_nonneg (norm_nonneg _) (zpow_pos ρ1.2.1 k).le) hwX hb1
  have hX : algebraMap Γ T.B X ∈ T.Econ ρ1 := by
    rw [mem_Econ, coeffB_algebraMap]; exact hXc
  refine ⟨X, hX, fun m => ?_, fun ρ hρ => ?_⟩
  · have h1 := hwX m
    rw [zcoeff_natCast] at h1
    exact h1.trans (((T.convergesAt_rad ρ1 b (topRad ρ1)).le_gaussNorm _).trans
      (hbn (topRad ρ1) σ.2.2))
  · have hc : (b : T.B) - algebraMap Γ T.B X ∈ T.Econ ρ1 := (T.Econ ρ1).sub_mem b.2 hX
    have hσ : 0 < (σ : ℝ) := σ.2.1
    have hw : ∀ k : ℤ, ‖T.coeffB ((b : T.B) - algebraMap Γ T.B X) k‖ * (σ : ℝ) ^ k ≤ C + 1 := by
      intro k
      rcases le_or_gt 0 k with hk | hk
      · rw [hX3 k hk, norm_zero, zero_mul]; linarith
      · rw [hX2 k hk]
        exact ((T.convergesAt_rad ρ1 b σ).le_gaussNorm k).trans (hbn σ le_rfl)
    have hneg := T.gaussNorm_neg_part_le hσ hρ (by linarith) hX3 hw
    have e : z - ((⟨_, hX⟩ : T.Econ ρ1) : T.RobbaExt ρ1) =
        (z - (b : T.RobbaExt ρ1)) + ((⟨_, hc⟩ : T.Econ ρ1) : T.RobbaExt ρ1) := by
      rw [show ((⟨_, hc⟩ : T.Econ ρ1)) = b - ⟨_, hX⟩ from Subtype.ext rfl, Completion.coe_sub]
      ring
    rw [e]
    refine (T.extNorm_add_le ρ _ _).trans (max_le_max (hb ρ hρ).le ?_)
    rw [extNorm_coe]
    exact hneg

def halfRad (ρ1 : Set.Ioo (0 : ℝ) 1) : Set.Ioo (0 : ℝ) 1 :=
  ⟨(ρ1 : ℝ) / 2, by have := ρ1.2.1; positivity, by linarith [ρ1.2.1, ρ1.2.2]⟩

theorem halfRad_le (ρ1 : Set.Ioo (0 : ℝ) 1) : ((halfRad ρ1 : Set.Ioo (0 : ℝ) 1) : ℝ) ≤ ρ1 := by
  show (ρ1 : ℝ) / 2 ≤ ρ1; linarith [ρ1.2.1]

theorem gaussNorm_zcoeff_le_of_weight {X : Γ} {ρ C' : ℝ} (hρ : 0 < ρ) (hC : 0 ≤ C')
    (h : ∀ m : ℕ, ‖T.coeff X m‖ * ρ ^ (m : ℤ) ≤ C') : gaussNorm (T.zcoeff X) ρ ≤ C' := by
  refine gaussNorm_le fun k => ?_
  rcases lt_or_ge k 0 with hk | hk
  · rw [T.zcoeff_of_neg _ hk, norm_zero, zero_mul]; exact hC
  · lift k to ℕ using hk
    rw [zcoeff_natCast]; exact h k

theorem convergesAt_of_weight_le {X : Γ} {ρ ρ' C' : ℝ} (hρ : 0 < ρ) (hρρ' : ρ < ρ')
    (h : ∀ m : ℕ, ‖T.coeff X m‖ * ρ' ^ (m : ℤ) ≤ C') : ConvergesAt (T.zcoeff X) ρ := by
  have hρ' : 0 < ρ' := hρ.trans hρρ'
  have hq : ρ / ρ' < 1 := (div_lt_one hρ').2 hρρ'
  have hq0 : 0 ≤ ρ / ρ' := by positivity
  refine convergesAt_of_eventually hρ (T.zcoeff_neg_exists X) fun ε hε => ?_
  obtain ⟨K, hK⟩ := exists_pow_lt_of_lt_one (show 0 < ε / (|C'| + 1) by positivity) hq
  refine ⟨K, fun n hn => ?_⟩
  lift n to ℕ using (by omega)
  have hKn : K ≤ n := by exact_mod_cast hn
  rw [zcoeff_natCast]
  calc ‖T.coeff X n‖ * ρ ^ (n : ℤ) = (‖T.coeff X n‖ * ρ' ^ (n : ℤ)) * (ρ / ρ') ^ n := by
        rw [zpow_natCast, zpow_natCast, div_pow, mul_assoc, mul_div_assoc',
          mul_div_cancel_left₀ _ (pow_pos hρ' n).ne']
    _ ≤ (|C'| + 1) * (ε / (|C'| + 1)) := by
        refine mul_le_mul ((h n).trans ((le_abs_self _).trans (by linarith)))
          ((pow_le_pow_of_le_one hq0 hq.le hKn).trans hK.le) (by positivity) (by positivity)
    _ = ε := by field_simp

variable [CompleteSpace L]

theorem tendsto_approx_bound (C' : ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    Tendsto (fun j : ℕ => max (1 / ((j : ℝ) + 2)) (C' * (((ρ1 : ℝ) / ((j : ℝ) + 2)) / ρ)))
      atTop (𝓝 0) := by
  have h1 : Tendsto (fun j : ℕ => 1 / ((j : ℝ) + 2)) atTop (𝓝 0) := by
    have := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    refine squeeze_zero (fun j => by positivity) (fun j => ?_) this
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  have h2 : Tendsto (fun j : ℕ => C' * (((ρ1 : ℝ) / ((j : ℝ) + 2)) / ρ)) atTop (𝓝 0) := by
    have : (fun j : ℕ => C' * (((ρ1 : ℝ) / ((j : ℝ) + 2)) / ρ)) =
        fun j : ℕ => (C' * (ρ1 : ℝ) / ρ) * (1 / ((j : ℝ) + 2)) := by
      funext j; field_simp
    rw [this]
    simpa using h1.const_mul (C' * (ρ1 : ℝ) / ρ)
  simpa using h1.max h2

theorem exists_gamma_of_bounded {z : T.RobbaExt ρ1} {C : ℝ} (hC : 0 ≤ C)
    (hz : ∀ ρ, T.extNorm ρ1 ρ z ≤ C) :
    ∃ (X : Γ) (hX : algebraMap Γ T.B X ∈ T.Econ (halfRad ρ1)),
      T.res (halfRad_le ρ1) z = ((⟨_, hX⟩ : T.Econ (halfRad ρ1)) : T.RobbaExt _) := by
  have hC' : 0 < C + 1 := by linarith
  have hρ1 : 0 < (ρ1 : ℝ) := ρ1.2.1
  let σ : ℕ → Set.Ioc (0 : ℝ) ρ1 := fun j => ⟨(ρ1 : ℝ) / ((j : ℝ) + 2), by positivity,
    div_le_self hρ1.le (by linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)])⟩
  have hε : ∀ j : ℕ, (0 : ℝ) < 1 / ((j : ℝ) + 2) := fun j => by positivity
  have hε1 : ∀ j : ℕ, 1 / ((j : ℝ) + 2) ≤ 1 := fun j => by
    rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
  have happ := fun j => T.exists_gamma_approx hC hz (σ j) (hε j) (hε1 j)
  choose X hX hXw hXa using happ
  set e : ℕ → ℝ → ℝ := fun j ρ =>
    max (1 / ((j : ℝ) + 2)) ((C + 1) * (((ρ1 : ℝ) / ((j : ℝ) + 2)) / ρ)) with hedef
  have he_tend : ∀ {ρ : ℝ}, 0 < ρ → Tendsto (fun j => e j ρ) atTop (𝓝 0) :=
    fun hρ => tendsto_approx_bound (ρ1 := ρ1) (C + 1) hρ
  have he_anti : ∀ {ρ : ℝ}, 0 < ρ → ∀ {j k : ℕ}, j ≤ k → e k ρ ≤ e j ρ := by
    intro ρ hρ j k hjk
    have hjk' : (j : ℝ) + 2 ≤ (k : ℝ) + 2 := by exact_mod_cast Nat.add_le_add_right hjk 2
    refine max_le_max (one_div_le_one_div_of_le (by positivity) hjk') ?_
    refine mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right ?_ hρ.le) hC'.le
    exact div_le_div_of_nonneg_left hρ1.le (by positivity) hjk'
  have hXconv : ∀ j, ConvergesAt (T.zcoeff (X j)) ρ1 := fun j => by
    have := hX j; rwa [mem_Econ, coeffB_algebraMap] at this
  have hXc : ∀ j (m : ℕ), ‖T.coeff (X j) m‖ ≤ (C + 1) / (ρ1 : ℝ) ^ (m : ℤ) := fun j m => by
    rw [le_div_iff₀ (zpow_pos hρ1 _)]; exact hXw j m
  have hXg : ∀ j, gaussNorm (T.zcoeff (X j)) ρ1 ≤ C + 1 :=
    fun j => T.gaussNorm_zcoeff_le_of_weight hρ1 hC'.le (hXw j)

  have hdconv : ∀ j k, ConvergesAt (T.zcoeff (X k - X j)) ρ1 := fun j k => by
    rw [sub_eq_add_neg]
    exact T.convergesAt_zcoeff_add hρ1 ρ1.2.2 (hXconv k) (T.convergesAt_zcoeff_neg hρ1 ρ1.2.2 (hXconv j))
  have hdC : ∀ j k, gaussNorm (T.zcoeff (X k - X j)) ρ1 ≤ C + 1 := fun j k => by
    rw [sub_eq_add_neg]
    refine (T.gaussNorm_zcoeff_add_le hρ1 ρ1.2.2.le (hXconv k)
      (T.convergesAt_zcoeff_neg hρ1 ρ1.2.2 (hXconv j))).trans (max_le (hXg k) ?_)
    rw [T.gaussNorm_zcoeff_neg hρ1 ρ1.2.2 (hXconv j)]; exact hXg j
  have hdist : ∀ j k, gaussNorm (T.zcoeff (X k - X j)) ρ1 ≤ max (e j ρ1) (e k ρ1) := by
    intro j k
    have h1 := hXa j (topRad ρ1) (σ j).2.2
    have h2 := hXa k (topRad ρ1) (σ k).2.2
    have h3 := T.extNorm_add_le (topRad ρ1)
      (z - ((⟨_, hX j⟩ : T.Econ ρ1) : T.RobbaExt ρ1))
      (-(z - ((⟨_, hX k⟩ : T.Econ ρ1) : T.RobbaExt ρ1)))
    rw [T.extNorm_neg,
      show z - ((⟨_, hX j⟩ : T.Econ ρ1) : T.RobbaExt ρ1) + -(z - ((⟨_, hX k⟩ : T.Econ ρ1) :
        T.RobbaExt ρ1)) = (((⟨_, hX k⟩ : T.Econ ρ1) - ⟨_, hX j⟩ : T.Econ ρ1) : T.RobbaExt ρ1) by
        rw [Completion.coe_sub]; ring, extNorm_coe] at h3
    have e1 : T.coeffB (((⟨_, hX k⟩ : T.Econ ρ1) - ⟨_, hX j⟩ : T.Econ ρ1) : T.B) =
        T.zcoeff (X k - X j) := by
      rw [show (((⟨_, hX k⟩ : T.Econ ρ1) - ⟨_, hX j⟩ : T.Econ ρ1) : T.B) =
        algebraMap Γ T.B (X k - X j) by simp [map_sub], coeffB_algebraMap]
    rw [e1] at h3
    exact h3.trans (max_le_max h1 h2)

  have hcauchy : ∀ m : ℕ, CauchySeq (fun j => T.coeff (X j) m) := by
    intro m
    obtain ⟨ht0, ht1⟩ := coeffHolderExp_pos_le_one (p := p) m
    set t := coeffHolderExp p m
    set B := (C + 1) / (ρ1 : ℝ) ^ (m : ℤ) with hBdef
    have hB : 0 < B := by positivity
    refine cauchySeq_of_le_tendsto_0
      (fun N => B ^ (1 - t) * (min (e N ρ1) (C + 1) / (ρ1 : ℝ) ^ (m : ℤ)) ^ t)
      (fun n k N hn hk => ?_) ?_
    · have hdnk : gaussNorm (T.zcoeff (X k - X n)) ρ1 ≤ min (e N ρ1) (C + 1) :=
        le_min ((hdist n k).trans (max_le (he_anti hρ1 hn) (he_anti hρ1 hk))) (hdC n k)
      have hδ0 : 0 ≤ min (e N ρ1) (C + 1) / (ρ1 : ℝ) ^ (m : ℤ) :=
        div_nonneg ((gaussNorm_nonneg hρ1).trans hdnk) (zpow_pos hρ1 _).le
      have hδB : min (e N ρ1) (C + 1) / (ρ1 : ℝ) ^ (m : ℤ) ≤ B :=
        div_le_div_of_nonneg_right (min_le_right _ _) (zpow_pos hρ1 _).le
      have hx : T.PrefixLe (X n) m B := fun i hi =>
        norm_le_div_of_weight hρ1 ρ1.2.2.le (by exact_mod_cast hi) (hXw n i)
      have hy : T.PrefixLe (X k - X n) m (min (e N ρ1) (C + 1) / (ρ1 : ℝ) ^ (m : ℤ)) :=
        fun i hi => norm_le_div_of_weight hρ1 ρ1.2.2.le (by exact_mod_cast hi)
          ((T.weight_natCast_le (hdconv n k) i).trans hdnk)
      have := T.norm_coeff_add_sub_le m hδ0 hδB hx hy m le_rfl
      rw [add_sub_cancel] at this
      rw [dist_comm, dist_eq_norm]
      exact this
    · have h1 : Tendsto (fun N => min (e N ρ1) (C + 1) / (ρ1 : ℝ) ^ (m : ℤ)) atTop (𝓝 0) := by
        have := ((he_tend hρ1).min (tendsto_const_nhds (x := C + 1))).div_const ((ρ1 : ℝ) ^ (m : ℤ))
        rwa [min_eq_left hC'.le, zero_div] at this
      have h2 := ((Real.continuousAt_rpow_const 0 t (Or.inr ht0.le)).tendsto.comp h1).const_mul
        (B ^ (1 - t))
      rwa [Real.zero_rpow ht0.ne', mul_zero] at h2
  set a : ℕ → L := fun m => limUnder atTop (fun j => T.coeff (X j) m) with hadef
  have hlim : ∀ m, Tendsto (fun j => T.coeff (X j) m) atTop (𝓝 (a m)) :=
    fun m => (hcauchy m).tendsto_limUnder
  have ha : ∀ m : ℕ, ‖a m‖ ≤ (C + 1) / (ρ1 : ℝ) ^ (m : ℤ) := fun m =>
    le_of_tendsto ((continuous_norm.tendsto _).comp (hlim m)) (Eventually.of_forall fun j => hXc j m)
  set Xl := T.ofCoeff a with hXldef
  have hXlc : ∀ m, T.coeff Xl m = a m := fun m => by rw [hXldef, coeff_ofCoeff]
  have hXlw : ∀ m : ℕ, ‖T.coeff Xl m‖ * (ρ1 : ℝ) ^ (m : ℤ) ≤ C + 1 := fun m => by
    rw [hXlc, ← le_div_iff₀ (zpow_pos hρ1 _)]; exact ha m
  have hXlh : algebraMap Γ T.B Xl ∈ T.Econ (halfRad ρ1) := by
    rw [mem_Econ, coeffB_algebraMap]
    exact T.convergesAt_of_weight_le (halfRad ρ1).2.1
      (show (ρ1 : ℝ) / 2 < ρ1 by linarith) hXlw
  refine ⟨Xl, hXlh, ?_⟩
  rw [← sub_eq_zero]
  refine T.eq_zero_of_forall_extNorm_eq_zero fun ρ => le_antisymm ?_ (T.extNorm_nonneg _ _)
  have hρ0 : 0 < (ρ : ℝ) := ρ.2.1
  have hρle : (ρ : ℝ) ≤ ρ1 := ρ.2.2.trans (halfRad_le ρ1)
  have hρhalf : (ρ : ℝ) / ρ1 ≤ 1 / 2 := by
    rw [div_le_iff₀ hρ1]; have := ρ.2.2; change (ρ : ℝ) ≤ (ρ1 : ℝ) / 2 at this; linarith
  refine le_of_forall_pos_le_add fun ε hε => ?_
  rw [zero_add]

  obtain ⟨N0, hN0⟩ := exists_pow_lt_of_lt_one (show 0 < ε / (C + 1) by positivity)
    (show (1 / 2 : ℝ) < 1 by norm_num)

  obtain ⟨ht0, ht1⟩ := inv_pow_pos_le_one (p := p) N0
  set t := ((p ^ N0 : ℕ) : ℝ)⁻¹
  set B := (C + 1) / (ρ1 : ℝ) ^ (N0 : ℤ) with hBdef
  have hB : 0 < B := by positivity
  set η : ℕ → ℝ := fun j => ∑ i ∈ Finset.range (N0 + 1), ‖T.coeff (X j) i - a i‖ with hηdef
  have hη : Tendsto η atTop (𝓝 0) := by
    have := tendsto_finset_sum (Finset.range (N0 + 1)) fun i _ =>
      ((continuous_norm.tendsto _).comp ((hlim i).sub_const (a i)))
    simpa [hηdef] using this
  have hlow : Tendsto (fun j => B ^ (1 - t) * (min (η j) B) ^ t) atTop (𝓝 0) := by
    have h1 : Tendsto (fun j => min (η j) B) atTop (𝓝 0) := by
      have := hη.min (tendsto_const_nhds (x := B)); rwa [min_eq_left hB.le] at this
    have h2 := ((Real.continuousAt_rpow_const 0 t (Or.inr ht0.le)).tendsto.comp h1).const_mul
      (B ^ (1 - t))
    rwa [Real.zero_rpow ht0.ne', mul_zero] at h2
  have hev : ∀ᶠ j in atTop, e j ρ ≤ ε ∧ (σ j : ℝ) ≤ ρ ∧ B ^ (1 - t) * (min (η j) B) ^ t ≤ ε := by
    refine ((he_tend hρ0).eventually (ge_mem_nhds hε)).and
      (Eventually.and ?_ (hlow.eventually (ge_mem_nhds hε)))
    obtain ⟨J, hJ⟩ := exists_nat_gt ((ρ1 : ℝ) / ρ)
    refine eventually_atTop.2 ⟨J, fun j hj => ?_⟩
    show (ρ1 : ℝ) / ((j : ℝ) + 2) ≤ ρ
    rw [div_le_iff₀ (by positivity)]
    have hjJ : (J : ℝ) ≤ j := by exact_mod_cast hj
    rw [div_lt_iff₀ hρ0] at hJ
    nlinarith
  obtain ⟨j, hje, hjσ, hjlow⟩ := hev.exists
  set ρ' : Set.Ioc (0 : ℝ) ρ1 := ⟨ρ, hρ0, hρle⟩

  have hA : T.extNorm (halfRad ρ1) ρ (T.res (halfRad_le ρ1) z -
      T.res (halfRad_le ρ1) ((⟨_, hX j⟩ : T.Econ ρ1) : T.RobbaExt ρ1)) ≤ ε := by
    rw [← map_sub, T.extNorm_res]
    exact (hXa j ρ' hjσ).trans hje

  have hBd : T.extNorm (halfRad ρ1) ρ (T.res (halfRad_le ρ1) ((⟨_, hX j⟩ : T.Econ ρ1) :
      T.RobbaExt ρ1) - ((⟨_, hXlh⟩ : T.Econ (halfRad ρ1)) : T.RobbaExt _)) ≤ ε := by
    rw [res_coe, ← Completion.coe_sub, extNorm_coe]
    have e1 : ((T.incl (halfRad_le ρ1) ⟨_, hX j⟩ - ⟨_, hXlh⟩ : T.Econ (halfRad ρ1)) : T.B) =
        algebraMap Γ T.B (X j - Xl) := by
      change ((T.incl (halfRad_le ρ1) ⟨_, hX j⟩ : T.Econ (halfRad ρ1)) : T.B) - algebraMap Γ T.B Xl = _
      rw [coe_incl, map_sub]
    rw [e1, coeffB_algebraMap]
    refine gaussNorm_le fun n => ?_
    rcases lt_or_ge n 0 with hn | hn
    · rw [T.zcoeff_of_neg _ hn, norm_zero, zero_mul]; exact hε.le
    lift n to ℕ using hn
    rw [zcoeff_natCast]
    rcases le_or_gt N0 n with hn0 | hn0
    ·
      have hp1 : T.PrefixLe (X j) n ((C + 1) / (ρ1 : ℝ) ^ (n : ℤ)) := fun i hi =>
        norm_le_div_of_weight hρ1 ρ1.2.2.le (by exact_mod_cast hi) (hXw j i)
      have hp2 : T.PrefixLe Xl n ((C + 1) / (ρ1 : ℝ) ^ (n : ℤ)) := fun i hi =>
        norm_le_div_of_weight hρ1 ρ1.2.2.le (by exact_mod_cast hi) (hXlw i)
      have h3 := T.prefixLe_sub hp1 hp2 n le_rfl
      calc ‖T.coeff (X j - Xl) n‖ * (ρ : ℝ) ^ (n : ℤ)
          ≤ (C + 1) / (ρ1 : ℝ) ^ (n : ℤ) * (ρ : ℝ) ^ (n : ℤ) :=
            mul_le_mul_of_nonneg_right h3 (zpow_pos hρ0 _).le
        _ = (C + 1) * ((ρ : ℝ) / ρ1) ^ n := by
            rw [zpow_natCast, zpow_natCast, div_pow]; ring
        _ ≤ (C + 1) * (1 / 2) ^ N0 := by
            refine mul_le_mul_of_nonneg_left ?_ hC'.le
            exact (pow_le_pow_left₀ (by positivity) hρhalf n).trans
              (pow_le_pow_of_le_one (by norm_num) (by norm_num) hn0)
        _ ≤ (C + 1) * (ε / (C + 1)) := mul_le_mul_of_nonneg_left hN0.le hC'.le
        _ = ε := by field_simp
    ·
      have hηB : min (η j) B ≤ B := min_le_right _ _
      have hη0 : 0 ≤ min (η j) B := le_min (Finset.sum_nonneg fun _ _ => norm_nonneg _) hB.le
      have hu : ∀ i ≤ N0, ‖T.coeff (X j) i‖ ≤ B := fun i hi =>
        norm_le_div_of_weight hρ1 ρ1.2.2.le (by exact_mod_cast hi) (hXw j i)
      have hv : ∀ i ≤ N0, ‖T.coeff Xl i‖ ≤ B := fun i hi =>
        norm_le_div_of_weight hρ1 ρ1.2.2.le (by exact_mod_cast hi) (hXlw i)
      have huv : ∀ i ≤ N0, ‖T.coeff (X j) i - T.coeff Xl i‖ ≤ min (η j) B := by
        intro i hi
        refine le_min ?_ ?_
        · rw [hXlc]
          exact Finset.single_le_sum (f := fun i => ‖T.coeff (X j) i - a i‖)
            (fun _ _ => norm_nonneg _) (Finset.mem_range.2 (by omega))
        · calc ‖T.coeff (X j) i - T.coeff Xl i‖ = ‖T.coeff (X j) i + -T.coeff Xl i‖ := by
                rw [sub_eq_add_neg]
            _ ≤ max ‖T.coeff (X j) i‖ ‖-T.coeff Xl i‖ := IsUltrametricDist.norm_add_le_max _ _
            _ ≤ B := by rw [norm_neg]; exact max_le (hu i hi) (hv i hi)
      have h3 := T.prefixLe_sub_of_coeff_close hη0 hηB hu hv huv n hn0.le
      calc ‖T.coeff (X j - Xl) n‖ * (ρ : ℝ) ^ (n : ℤ)
          ≤ B ^ (1 - ((p ^ N0 : ℕ) : ℝ)⁻¹) * (min (η j) B) ^ ((p ^ N0 : ℕ) : ℝ)⁻¹ * 1 := by
            refine mul_le_mul h3 ?_ (zpow_pos hρ0 _).le
              (mul_nonneg (Real.rpow_nonneg hB.le _) (Real.rpow_nonneg hη0 _))
            rw [zpow_natCast]
            exact pow_le_one₀ hρ0.le (hρle.trans ρ1.2.2.le)
        _ ≤ ε := by rw [mul_one]; exact hjlow
  have hsum := T.extNorm_add_le ρ (T.res (halfRad_le ρ1) z -
    T.res (halfRad_le ρ1) ((⟨_, hX j⟩ : T.Econ ρ1) : T.RobbaExt ρ1))
    (T.res (halfRad_le ρ1) ((⟨_, hX j⟩ : T.Econ ρ1) : T.RobbaExt ρ1) -
      ((⟨_, hXlh⟩ : T.Econ (halfRad ρ1)) : T.RobbaExt _))
  rw [sub_add_sub_cancel] at hsum
  exact hsum.trans (max_le hA hBd)

def πExt (ρ1 : Set.Ioo (0 : ℝ) 1) : T.RobbaExt ρ1 :=
  ((⟨algebraMap Γ T.B T.π, T.algebraMap_π_mem_Econ ρ1⟩ : T.Econ ρ1) : T.RobbaExt ρ1)

def πInvExt (ρ1 : Set.Ioo (0 : ℝ) 1) : T.RobbaExt ρ1 :=
  ((⟨IsLocalization.Away.invSelf T.π, T.invSelf_mem_Econ ρ1⟩ : T.Econ ρ1) : T.RobbaExt ρ1)

theorem πExt_mul_πInvExt (ρ1 : Set.Ioo (0 : ℝ) 1) : T.πExt ρ1 * T.πInvExt ρ1 = 1 := by
  rw [πExt, πInvExt, ← Completion.coe_mul, ← Completion.coe_one]
  congr 1
  exact Subtype.ext (IsLocalization.Away.mul_invSelf T.π)

theorem extNorm_πExt (ρ : Set.Ioc (0 : ℝ) ρ1) : T.extNorm ρ1 ρ (T.πExt ρ1) = ρ := by
  rw [πExt, extNorm_coe]
  show gaussNorm (T.coeffB (algebraMap Γ T.B T.π)) ρ = ρ
  rw [coeffB_algebraMap, ← pow_one T.π, zcoeff_π_pow, gaussNorm_pi_single _ _ (rad_pos ρ1 ρ)]
  simp

theorem extNorm_πInvExt (ρ : Set.Ioc (0 : ℝ) ρ1) :
    T.extNorm ρ1 ρ (T.πInvExt ρ1) = (ρ : ℝ)⁻¹ := by
  rw [πInvExt, extNorm_coe]
  show gaussNorm (T.coeffB (IsLocalization.Away.invSelf T.π)) ρ = (ρ : ℝ)⁻¹
  rw [coeffB_invSelf, gaussNorm_pi_single _ _ (rad_pos ρ1 ρ)]
  simp

theorem extNorm_pow (ρ : Set.Ioc (0 : ℝ) ρ1) (x : T.RobbaExt ρ1) (n : ℕ) :
    T.extNorm ρ1 ρ (x ^ n) = T.extNorm ρ1 ρ x ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, extNorm_one]
  | succ n ih => rw [pow_succ, extNorm_mul, ih, pow_succ]

theorem ofRad_πInvExt (ρ1 : Set.Ioo (0 : ℝ) 1) :
    T.ofRad ρ1 (T.πInvExt ρ1) =
      T.edagToTilde ⟨_, T.Econ_le_Edag ρ1 (T.invSelf_mem_Econ ρ1)⟩ :=
  (T.edagToTilde_apply (T.invSelf_mem_Econ ρ1)).symm

theorem mem_range_of_isUnit {x : T.RobbaTilde} (hx : IsUnit x) : x ∈ T.edagToTilde.range := by
  obtain ⟨y, hxy⟩ := hx.exists_right_inv
  obtain ⟨ρ1, x', y', rfl, rfl⟩ := T.exists_ofRad₂ x y
  have h1 : x' * y' = 1 := T.ofRad_injective ρ1 (by rw [map_mul, hxy, map_one])
  have hN : ∀ ρ, T.extNorm ρ1 ρ x' * T.extNorm ρ1 ρ y' = 1 := fun ρ => by
    rw [← extNorm_mul, h1, extNorm_one]
  have hypos : ∀ ρ, 0 < T.extNorm ρ1 ρ y' := fun ρ => by
    rcases (T.extNorm_nonneg ρ y').lt_or_eq with h | h
    · exact h
    · have := hN ρ; rw [← h, mul_zero] at this; exact absurd this zero_ne_one
  have hρ1 : 0 < (ρ1 : ℝ) := ρ1.2.1
  set ρ2 : Set.Ioc (0 : ℝ) ρ1 := ⟨(ρ1 : ℝ) / 2, by positivity, by linarith⟩ with hρ2def
  obtain ⟨M, hM⟩ := pow_unbounded_of_one_lt
    (T.extNorm ρ1 (topRad ρ1) y' / T.extNorm ρ1 ρ2 y') (show (1 : ℝ) < 2 by norm_num)
  rw [div_lt_iff₀ (hypos ρ2)] at hM
  set w := y' * T.πInvExt ρ1 ^ M with hwdef
  set z := x' * T.πExt ρ1 ^ M with hzdef
  have hzw : z * w = 1 := by
    rw [hzdef, hwdef, show x' * T.πExt ρ1 ^ M * (y' * T.πInvExt ρ1 ^ M) =
      (x' * y') * (T.πExt ρ1 * T.πInvExt ρ1) ^ M by ring, h1, T.πExt_mul_πInvExt, one_pow, one_mul]
  have hNw : ∀ ρ : Set.Ioc (0 : ℝ) ρ1, T.extNorm ρ1 ρ w = T.extNorm ρ1 ρ y' * ((ρ : ℝ)⁻¹) ^ M :=
    fun ρ => by rw [hwdef, extNorm_mul, extNorm_pow, extNorm_πInvExt]
  have hNzw : ∀ ρ, T.extNorm ρ1 ρ z * T.extNorm ρ1 ρ w = 1 := fun ρ => by
    rw [← extNorm_mul, hzw, extNorm_one]
  have hwpos : ∀ ρ, 0 < T.extNorm ρ1 ρ w := fun ρ => by
    rw [hNw]; exact mul_pos (hypos ρ) (pow_pos (inv_pos.2 (rad_pos ρ1 ρ)) M)
  have hw12 : T.extNorm ρ1 (topRad ρ1) w ≤ T.extNorm ρ1 ρ2 w := by
    rw [hNw, hNw]
    have e : ((ρ2 : ℝ))⁻¹ ^ M = 2 ^ M * ((topRad ρ1 : Set.Ioc (0 : ℝ) ρ1) : ℝ)⁻¹ ^ M := by
      show ((ρ1 : ℝ) / 2)⁻¹ ^ M = 2 ^ M * ((ρ1 : ℝ))⁻¹ ^ M
      rw [inv_div, div_eq_mul_inv, mul_pow]
    rw [e, ← mul_assoc]
    refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg (inv_nonneg.2 hρ1.le) M)
    rw [mul_comm]; exact hM.le
  have hρ2lt : (ρ2 : ℝ) < ρ1 := by show (ρ1 : ℝ) / 2 < ρ1; linarith
  have hwlow : ∀ ρ : Set.Ioc (0 : ℝ) ρ1, (ρ : ℝ) ≤ ρ2 →
      T.extNorm ρ1 ρ2 w ≤ T.extNorm ρ1 ρ w := by
    intro ρ hρ
    rcases hρ.lt_or_eq with hlt | heq
    · obtain ⟨t, ht0, ht1, hρt⟩ := exists_interp_exponent (a := (ρ : ℝ)) (r := ρ2) (b := ρ1)
        (rad_pos ρ1 ρ) hlt hρ2lt
      have hI := T.extNorm_interp_le ρ (topRad ρ1) ρ2 ht0.le ht1.le hρt w
      have hp := hwpos ρ2
      have h2 : T.extNorm ρ1 ρ2 w ^ (1 - t) * T.extNorm ρ1 ρ2 w ^ t ≤
          T.extNorm ρ1 ρ w ^ (1 - t) * T.extNorm ρ1 ρ2 w ^ t := by
        calc T.extNorm ρ1 ρ2 w ^ (1 - t) * T.extNorm ρ1 ρ2 w ^ t = T.extNorm ρ1 ρ2 w := by
              rw [← Real.rpow_add hp, sub_add_cancel, Real.rpow_one]
          _ ≤ T.extNorm ρ1 ρ w ^ (1 - t) * T.extNorm ρ1 (topRad ρ1) w ^ t := hI
          _ ≤ T.extNorm ρ1 ρ w ^ (1 - t) * T.extNorm ρ1 ρ2 w ^ t :=
              mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (T.extNorm_nonneg _ _) hw12 ht0.le)
                (Real.rpow_nonneg (T.extNorm_nonneg _ _) _)
      have h3 := le_of_mul_le_mul_right h2 (Real.rpow_pos_of_pos hp t)
      exact (Real.rpow_le_rpow_iff hp.le (T.extNorm_nonneg _ _) (by linarith)).1 h3
    · rw [show ρ = ρ2 from Subtype.ext heq]
  set z2 := T.res (halfRad_le ρ1) z with hz2def
  have hz2 : ∀ ρ : Set.Ioc (0 : ℝ) (halfRad ρ1),
      T.extNorm (halfRad ρ1) ρ z2 ≤ (T.extNorm ρ1 ρ2 w)⁻¹ := by
    intro ρ
    rw [hz2def, T.extNorm_res]
    have hz' : T.extNorm ρ1 ⟨ρ, ρ.2.1, ρ.2.2.trans (halfRad_le ρ1)⟩ z =
        (T.extNorm ρ1 ⟨ρ, ρ.2.1, ρ.2.2.trans (halfRad_le ρ1)⟩ w)⁻¹ :=
      eq_inv_of_mul_eq_one_left (hNzw _)
    rw [hz']
    exact inv_anti₀ (hwpos ρ2) (hwlow _ ρ.2.2)
  obtain ⟨X, hX, hres⟩ := T.exists_gamma_of_bounded (inv_nonneg.2 (hwpos ρ2).le) hz2
  have hx' : x' = z * T.πInvExt ρ1 ^ M := by
    rw [hzdef, mul_assoc, ← mul_pow, T.πExt_mul_πInvExt, one_pow, mul_one]
  refine ⟨⟨algebraMap Γ T.B X, T.Econ_le_Edag _ hX⟩ *
    ⟨_, T.Econ_le_Edag ρ1 (T.invSelf_mem_Econ ρ1)⟩ ^ M, ?_⟩
  rw [map_mul, map_pow, ← T.ofRad_πInvExt, T.edagToTilde_apply hX, hx', map_mul, map_pow]
  congr 1
  show T.ofRad (halfRad (halfRad ρ1)) (((⟨algebraMap Γ T.B X, hX⟩ : T.Econ (halfRad (halfRad ρ1)))) :
    T.RobbaExt (halfRad (halfRad ρ1))) = T.ofRad ρ1 z
  rw [← hres, T.ofRad_res, hz2def, T.ofRad_res]

theorem isUnit_iff (x : T.RobbaTilde) : IsUnit x ↔ x ≠ 0 ∧ x ∈ T.edagToTilde.range := by
  constructor
  · intro hx
    exact ⟨hx.ne_zero, T.mem_range_of_isUnit hx⟩
  · rintro ⟨hx0, b, rfl⟩
    have hb : b ≠ 0 := fun h => hx0 (by rw [h, map_zero])
    obtain ⟨c, hc⟩ := T.isField_Edag.mul_inv_cancel hb
    exact IsUnit.of_mul_eq_one (T.edagToTilde c) (by rw [← map_mul, hc, map_one])

end TeichLift

end GroundTheory.PAdicHodge
